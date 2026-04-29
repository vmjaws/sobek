package sobek

// vm_dbg.go — Debug execution loop and helpers.
// This file contains the vm.debug() method which is the main debugger-aware
// execution loop. It is separated from vm.go to minimize diffs against upstream
// sobek, making rebases trivial.
//
// vm.go only needs:
//   - The `debugger *Debugger` and `debugMode bool` fields on the `vm` struct
//   - The dispatch in runTryInner(): `if vm.debugMode { vm.debug() } else { vm.run() }`
//   - Minor safety checks (nil prg, stash bounds) guarded by `vm.debugMode`

import (
	"fmt"
	"os"
	"strings"
	"sync/atomic"
)

// Debug logging control via environment variables (same as debugger.go)
var vmDebugEnabled = os.Getenv("SOBEK_DEBUG_VM") == "1" || os.Getenv("SOBEK_DEBUG_ALL") == "1"


func (vm *vm) debug() {
	// Log every debug() entry when step flags are active — unconditionally
	if vm.debugger != nil && debugVM && (vm.debugger.next || vm.debugger.stepIn) {
		funcName := ""
		if vm.prg != nil {
			funcName = string(vm.prg.funcName)
		}
		srcName := ""
		if vm.prg != nil && vm.prg.src != nil {
			srcName = vm.prg.src.Name()
		}
		if debugVM {
			fmt.Printf("[VM-DEBUG-ENTRY] debug() entered: func=%q, file=%s, PC=%d, next=%v, stepIn=%v, suppress=%v, depth=%d\n",
			funcName, srcName, vm.pc, vm.debugger.next, vm.debugger.stepIn, vm.debugger.suppressDebugger, vm.debugger.callStackDepth())
		}
	}
	if vm.profTracker != nil && !vm.runWithProfiler() {
		return
	}

	// ARROW-DEBUG: Log when debug() starts with step flags active at function entry (PC=0)
	// This helps trace arrow function callbacks entering the debug loop
	if vm.debugger != nil && vm.pc == 0 && debugVM && (vm.debugger.next || vm.debugger.stepIn) {
		srcName := ""
		if vm.prg != nil && vm.prg.src != nil {
			srcName = vm.prg.src.Name()
		}
		funcName := ""
		if vm.prg != nil {
			funcName = string(vm.prg.funcName)
		}
		if debugVM {
			fmt.Printf("[ARROW-DEBUG] debug() entered at PC=0: func=%q, file=%s, stepIn=%v, next=%v, depth=%d, lastBP={file=%s, line=%d, pc=%d, depth=%d}, suppressDebugger=%v\n",
			funcName, srcName, vm.debugger.stepIn, vm.debugger.next, len(vm.callStack),
			vm.debugger.lastBreakpoint.filename, vm.debugger.lastBreakpoint.line, vm.debugger.lastBreakpoint.pc, vm.debugger.lastBreakpoint.stackDepth,
			vm.debugger.suppressDebugger)
		}
	}

	count := 0
	interrupted := false
	// lastExecPC tracks the PC of the most recently executed instruction.
	// Unlike lastBreakpoint.pc (which is the PC where we last PAUSED), this
	// reflects the actual previous instruction — needed to detect forward jumps
	// from conditional/try-exit instructions that skip over catch blocks.
	lastExecPC := -1
	for {
		if count == 0 {
			if atomic.LoadInt32(&globalProfiler.enabled) == 1 && !vm.runWithProfiler() {
				return
			}
			count = 100
		} else {
			count--
		}
		if interrupted = atomic.LoadUint32(&vm.interrupted) != 0; interrupted {
			break
		}

		if vm.debugger != nil {
			// CRITICAL: When suppressDebugger is set, skip ALL debugger processing.
			// This is set by gherkin.Run() during orchestration and cleared only by
			// gherkin's runPickleStep when executing step functions.
			// Init, setup, teardown, and handleSummary never set suppressDebugger,
			// so breakpoints work normally in those phases.
			if vm.debugger.suppressDebugger {
				goto executeInstruction
			}


			// CHANGED: Allow breakpoints during init phase for user scripts
			// Only skip breakpoints during init if the current file is NOT a user file
			// User files are those with breakpoints set on them
			skipBreakpoints := false

			// PERF: refresh the filename cache once per instruction (O(1) when prg unchanged).
			// All code below uses cachedFilename / cachedNormFile instead of
			// calling Filename() + strings.HasPrefix/TrimPrefix repeatedly.
			vm.debugger.refreshFilenameCache()

			// CRITICAL: First check if init was already completed for ANY user file
			// This check happens REGARDLESS of whether initPhase is set
			// It prevents re-hitting init breakpoints on subsequent VUs (VU 0 for teardown/handleSummary)
			//
			// HOWEVER: Do NOT skip breakpoints when:
			// 1. The debugger is in stepIn mode (explicitly enabled for lifecycle functions)
			// 2. The initPhase flag is false (we're past init and in a lifecycle function)
			//
			// The key insight is that init breakpoints should only be skipped during MODULE-LEVEL
			// code execution (during VU instantiation). Once we're inside a lifecycle function
			// (setup/default/teardown), breakpoints should work normally even if they happen
			// to be on the same line number as something that was executed during init.
			if vm.prg != nil && vm.prg.src != nil {
				// Use cached normalized filename (refreshed above)
				normalizedFilename := vm.debugger.cachedNormFile

				// PERF: Use the debugger's local monotonic initComplete flag
				// instead of calling GetGlobalInitTracker().HasAnyInitCompleted()
				// on every instruction (which acquires an RLock).
				// initComplete is already maintained by breakpoint() in debugger.go.
				if !vm.debugger.initComplete {
					vm.debugger.initComplete = GetGlobalInitTracker().HasAnyInitCompleted()
				}
				anyInitCompleted := vm.debugger.initComplete

				if anyInitCompleted {
					// Apply init-BP dedup: skip breakpoints that already fired during init.
					// NOTE: The inLifecycleBody guard (callStackDepth >= 1) was removed because
					// module-level init code runs inside a Go callback wrapper (bundle.go call(nil))
					// that pushes a call frame. The dedup uses composite {file, line} keys from the
					// source map, so breakpoints in different files at the same line are NOT suppressed.
					{
						currentLine := vm.debugger.Line()

						// Use the consolidated ensureInitBPSnapshot / wasHitDuringInit methods
						// instead of inline snapshot logic (was duplicated between vm.go and debugger.go).
						vm.debugger.ensureInitBPSnapshot()

						// FIX: Use source-mapped filename for init-BP dedup, not the bundle filename.
						// In bundled TypeScript, normalizedFilename is the bundle file (e.g., LoadTests.ts).
						// Multiple original files (CcsApi.ts, Stores.ts) share that name, so using it
						// causes cross-file line-number collisions: a breakpoint at line 15 in CcsApi.ts
						// hit during init would suppress a breakpoint at line 15 in Stores.ts.
						// The source-mapped filename (cachedSrcMapFile) is the ORIGINAL file, making
						// the dedup key unique per original source file.
						initCheckFile := normalizedFilename
						if vm.debugger.cachedSrcMapFile != "" {
							initCheckFile = vm.debugger.cachedSrcMapFile
						}
						wasHitDuringInit := vm.debugger.wasHitDuringInit(initCheckFile, currentLine)

						if wasHitDuringInit {
							skipBreakpoints = true
							if vmDebugEnabled || vm.debugger.enableDebugLogging {
								fmt.Printf("[VM-INIT-CHECK] Skipping init breakpoint at line %d for '%s' (srcMap='%s', snapshotDone=%v, snapshotSize=%d)\n",
									currentLine, normalizedFilename, initCheckFile, vm.debugger.initBPSnapshotDone, len(vm.debugger.initBPSnapshot))
							}
						}
					}
				}
			}

			// Now handle the init phase logic for the FIRST VU
			if !skipBreakpoints && vm.debugger.initPhase && vm.prg != nil && vm.prg.src != nil {
				currentFilename := vm.debugger.cachedFilename
				normalizedFilename := vm.debugger.cachedNormFile

				// PERF: Use Count() + HasBreakpoint() instead of GetAllBreakpoints() which
				// allocates a new map on every call. We only need to know if the file has
				// ANY breakpoint, not which specific lines — so checking HasBreakpoint at
				// the current line (already computed) is sufficient combined with the
				// hasLocalBPs/hasGlobalBPs fast-path flags.
				gbr := GetGlobalBreakpoints()
				hasAnyGlobalBP := gbr.Count() > 0
				var hasGlobalBP bool
				if hasAnyGlobalBP {
					// Check if the global registry has any breakpoint for this file.
					// We only need a file-level check, not line-level, but HasBreakpoint
					// is still cheaper than GetAllBreakpoints. Use line 0 sentinel? No —
					// just check if any breakpoint exists for either filename variant.
					// PERF: fileHasBreakpoint does a single RLock + map lookup.
					hasGlobalBP = gbr.FileHasBreakpoints(normalizedFilename) || gbr.FileHasBreakpoints(currentFilename)
				}
				vm.debugger.breakpointMutex.RLock()
				_, hasLocalBP := vm.debugger.breakpoints[currentFilename]
				_, hasNormalizedLocalBP := vm.debugger.breakpoints[normalizedFilename]
				vm.debugger.breakpointMutex.RUnlock()

				// If this is a user file, capture the init filename for later
				// This ensures MarkInitCompleted works even if SetInitPhase(true) was called
				// before the program was loaded
				isUserFile := hasGlobalBP || hasLocalBP || hasNormalizedLocalBP

				// FIX: Also consider it a user file if ANY global breakpoints exist.
				// In bundled TypeScript (esbuild), all code is in a single vm.prg
				// with src.Name() pointing to the main bundle file. Breakpoints set
				// on imported files (e.g., CcsApi.ts) won't match the bundle filename,
				// but breakpoint() correctly checks source-mapped line numbers.
				// Without this, skipBreakpoints=true prevents breakpoint() from ever
				// being called, and breakpoints in imported files never fire.
				if !isUserFile && hasAnyGlobalBP {
					isUserFile = true
				}

				if isUserFile && vm.debugger.initFilename == "" {
					vm.debugger.initFilename = normalizedFilename
				}

				// Skip breakpoints during init ONLY for non-user files (internal k6 modules)
				skipBreakpoints = !isUserFile
			}

			// CRITICAL FIX: Do NOT clear step operations when skipping init breakpoints
			// The skipBreakpoints flag is used to skip RE-HITTING breakpoints that were hit during init
			// But if the user explicitly requested step-over or step-in, we should honor that request
			// Only clear step flags when skipping breakpoints in NON-USER files (internal k6 code)
			// NOT when skipping init breakpoints in user files
			//
			// The old logic was:
			// if skipBreakpoints && (vm.debugger.next || vm.debugger.stepIn) {
			//     vm.debugger.next = false
			//     vm.debugger.stepIn = false
			//     vm.debugger.steppingFilename = ""
			// }
			//
			// This is WRONG because it clears step flags even when stepping through user code
			// after an init breakpoint. The step flags should only be cleared when entering
			// non-user code (which is handled below in the fileChanged check)

			// Add nil check for vm.prg before accessing debugger methods
			// CRITICAL FIX: We need to process step-over/step-in even when skipBreakpoints is true
			// The skipBreakpoints flag should only skip BREAKPOINT activation, not stepping
			if vm.prg != nil && vm.prg.src != nil {
				// CRITICAL: Inherit global step state if this VM doesn't have local step state
				// This allows step-over/step-in to work across VM transitions (e.g., init -> setup)
				//
				// FIX #5: Allow inheritance when the coordinator has explicit step state
				// regardless of init completion. Previously, the !anyInitCompleted guard
				// blocked VU1 from inheriting step state set during VU0's setup pause.
				// The init-skip logic below (justInheritedStepState) handles not stopping
				// at module-level init code.
			justInheritedStepState := false
			if !vm.debugger.next && !vm.debugger.stepIn && !vm.debugger.suppressStepInheritance {
				// FIX #1: Use the already-cached initComplete flag (updated ~20 lines above)
				// instead of calling HasAnyInitCompleted() again which acquires a redundant RLock.
				anyInitCompleted := vm.debugger.initComplete

				// PERF: Atomic fast-path — skip the RLock-protected GetGlobalStepState /
				// GetVUStepState entirely when no step state exists anywhere. This is the
				// common case (99.9% of instructions between breakpoints) and eliminates
				// 2 RLock acquisitions per instruction.
				hasGlobalStep := false
				var globalNext, globalStepIn bool
				var globalSteppingFile string
				var globalTargetDepth int
				isMultiVU := false

				if GetGlobalCoordinator().HasAnyStepStateFast() {
					// Step state exists somewhere — take the RLock to read it.
					isMultiVU = GetGlobalCoordinator().IsMultiVUDebug()

					if isMultiVU {
						globalNext, globalStepIn, globalSteppingFile, globalTargetDepth = GetGlobalCoordinator().GetVUStepState(vm.debugger.vuID)
					} else {
						globalNext, globalStepIn, globalSteppingFile, globalTargetDepth = GetGlobalCoordinator().GetGlobalStepState()
					}
					hasGlobalStep = globalNext || globalStepIn
				}

				// Allow step state inheritance if:
				// - Init hasn't completed yet (early phase — stepping through init), OR
				// - The coordinator has explicit step state (user issued a step command
				//   that needs to transfer across VM/VU boundaries, e.g., VU0→VU1)
				shouldInherit := !anyInitCompleted || hasGlobalStep

				if shouldInherit && (globalNext || globalStepIn) {
					vm.debugger.next = globalNext
					vm.debugger.stepIn = globalStepIn
					vm.debugger.steppingFilename = globalSteppingFile
					vm.debugger.stepOverTargetDepth = vm.debugger.callStackDepth()
					if globalTargetDepth > 0 && vm.debugger.stepOverTargetDepth == 0 {
						vm.debugger.stepOverTargetDepth = 1
					}
					// FIX #2: Set stepOverOriginalTargetDepth so that activateWithStepState's
					// "no user command" branch uses the correct depth instead of falling back
					// to savedCallDepth (which can corrupt the target depth mid-step).
					vm.debugger.stepOverOriginalTargetDepth = vm.debugger.stepOverTargetDepth
					justInheritedStepState = true

					vm.debugger.lastBreakpoint.line = vm.debugger.Line()
					vm.debugger.lastBreakpoint.pc = vm.pc
					vm.debugger.lastBreakpoint.filename = vm.debugger.Filename()
					vm.debugger.lastBreakpoint.stackDepth = vm.debugger.callStackDepth()

					if vm.debugger.enableDebugLogging {
						fmt.Printf("[VM] Inherited step state (multiVU=%v, vuID=%d): next=%v, stepIn=%v, file=%s, targetDepth=%d, originalTargetDepth=%d (anyInitCompleted=%v)\n",
							isMultiVU, vm.debugger.vuID, globalNext, globalStepIn, globalSteppingFile, vm.debugger.stepOverTargetDepth, vm.debugger.stepOverOriginalTargetDepth, anyInitCompleted)
					}
					if isMultiVU {
						GetGlobalCoordinator().ClearVUStepState(vm.debugger.vuID)
					} else {
						GetGlobalCoordinator().ClearGlobalStepState()
					}
				}
			}

				// Check breakpoint FIRST before logging
				// When skipBreakpoints is true, we treat hasBreakpoint as false to skip breakpoint activation
				// but we STILL process step-over and step-in
				hasBreakpoint := false
				if !skipBreakpoints {
					hasBreakpoint = vm.debugger.breakpoint()
					// DIAGNOSTIC: Log when breakpoint found during init
					if hasBreakpoint && vm.debugger.initPhase && (debugBreakpoint || debugAll) {
						fmt.Printf("[VM-INIT-BP] ✅ breakpoint() returned true during init at line %d, file=%q, skipBreakpoints=%v, active=%v, hasConnection=%v\n",
							vm.debugger.Line(), vm.debugger.cachedNormFile, skipBreakpoints, vm.debugger.active, vm.debugger.HasConnection())
					}
				} else {
					// DIAGNOSTIC: Always log when skipBreakpoints=true for a line that has a registered breakpoint
					currentLine := vm.debugger.Line()
					normFile := vm.debugger.cachedNormFile
					srcMap := vm.debugger.cachedSrcMapFile
					hasBPGlobal := GetGlobalBreakpoints().HasBreakpoint(normFile, currentLine) ||
						(srcMap != "" && srcMap != normFile && GetGlobalBreakpoints().HasBreakpoint(srcMap, currentLine))
                                        if hasBPGlobal && (debugBreakpoint || debugAll) {
						fmt.Printf("[BP-SKIP-INIT] ⚠️ skipBreakpoints=true BLOCKED breakpoint at line %d, file=%q, srcMap=%q, initPhase=%v, initComplete=%v, vuID=%d\n",
							currentLine, normFile, srcMap, vm.debugger.initPhase, vm.debugger.initComplete, vm.debugger.vuID)
					}
					if vm.debugger.breakpointCheckCount < 3 {
						vm.debugger.breakpointCheckCount++
						if debugVM {
							fmt.Printf("[BP-TRACE] SKIPPED breakpoint() call: skipBreakpoints=true, initPhase=%v, initComplete=%v, normFile=%q\n",
								vm.debugger.initPhase, vm.debugger.initComplete, vm.debugger.cachedNormFile)
						}
					}
				}

				// Skip breaking at module entry point (PC=0) when we just inherited step state.
				// This prevents spurious breaks at the very first bytecode instruction when
				// transitioning between phases (init → setup → default).
				// FIX #4: Use vm.pc == 0 instead of Line() <= 1. Line 1 in the bundled
				// output can correspond to real user code (imports, first statement) that
				// the user may want to break on. PC=0 is always the module/function entry.
				if justInheritedStepState && vm.pc == 0 && !hasBreakpoint {
					goto executeInstruction
				}

				if !vm.debugger.active && (hasBreakpoint || vm.debugger.next || vm.debugger.stepIn) {

					currentFilename := vm.debugger.Filename() // Use source-mapped filename for consistency
					normalizedCurrentFilename := vm.debugger.cachedNormFile
					currentLine := vm.debugger.Line()
					currentStackDepth := vm.debugger.callStackDepth()
					currentPC := vm.pc

					// CRITICAL: Negative PC values are internal VM state (e.g., after
					// yield/await resume via yieldMarker). They don't correspond to real
					// bytecode instructions and their source-map positions are meaningless
					// (often line 1). Never break at a negative PC — it causes the IDE
					// to jump to the first line of the file after any async call.
					if currentPC < 0 {
						goto executeInstruction
					}

					// prevStackDepth only used by commented-out per-instruction logging.
					// prevStackDepth := vm.debugger.lastBreakpoint.stackDepth
					prevLine := vm.debugger.lastBreakpoint.line
					prevPC := vm.debugger.lastBreakpoint.pc
					prevFilename := vm.debugger.lastBreakpoint.filename

					// For "next" operation: only break if we're on a NEW line AND at same/shallower depth
					// For "stepIn" operation: break at next line regardless of depth
					// For regular breakpoint: always break if location changed
					shouldBreak := false
					breakReason := ""

					// FIX: Check if current line is suppressed due to inherited position
					// from a skipped if-body. When a conditional jump skips a block, the
					// instructions after the block inherit the source position of the last
					// statement in the block. We suppress ALL breaks at that line until
					// execution moves to a different line.
				suppressedByInheritedLine := false
					if vm.debugger.suppressedInheritedLine > 0 {
						if currentLine == vm.debugger.suppressedInheritedLine && normalizedCurrentFilename == vm.debugger.suppressedInheritedFile {
							suppressedByInheritedLine = true
							if debugVM {
								fmt.Printf("[VM-SUPPRESS] Suppressing line %d (PC=%d) in %s — inherited from skipped if-body (suppressedInheritedLine=%d)\n",
									currentLine, currentPC, normalizedCurrentFilename, vm.debugger.suppressedInheritedLine)
							}
						} else {
							if debugVM {
								fmt.Printf("[VM-SUPPRESS] Clearing suppressedInheritedLine=%d (was for %s), now at line %d in %s\n",
									vm.debugger.suppressedInheritedLine, vm.debugger.suppressedInheritedFile, currentLine, normalizedCurrentFilename)
							}
							// Line changed — clear the suppression
							vm.debugger.suppressedInheritedLine = 0
							vm.debugger.suppressedInheritedFile = ""
						}
					}

					// CRITICAL: Check if current file is a "user file" (has breakpoints or is the stepping source)
					// This prevents stepping through internal k6 code like handleSummary
					//
					// PERF: The expensive checks (breakpoint lookups, extension checks,
					// normalizeFilenameForMatch) are cached per vm.prg. Only the cheap
					// stepping-filename comparison runs on every instruction.
					isUserFile := false
					steppingFilename := vm.debugger.steppingFilename

					normalizedSteppingFilename := normalizeFilename(steppingFilename)

					// CRITICAL FIX: Skip debugging for internal eval code (like summary wrapper)
					// The <eval> filename indicates runtime-generated code that shouldn't be debugged
					if normalizedCurrentFilename == "<eval>" || strings.HasPrefix(normalizedCurrentFilename, "<eval>") {
						// Clear step flags when entering eval code
						if vm.debugger.next || vm.debugger.stepIn {
							vm.debugger.stepIn = false
							vm.debugger.next = false
							vm.debugger.steppingFilename = ""
						}
						goto executeInstruction
					}

					// CRITICAL FIX: Detect file change and clear step flags immediately
					// This happens when stepping in user code and then k6 starts running internal scripts
					// (like handleSummary). We must stop stepping in those internal scripts.
					fileChanged := normalizedCurrentFilename != normalizedSteppingFilename && normalizedSteppingFilename != ""
					if fileChanged && (vm.debugger.next || vm.debugger.stepIn) {
						// PERF: Use FileHasBreakpoints() instead of GetAllBreakpoints()
						// to avoid map allocation on every file-change check.
						newFileHasGlobalBP := GetGlobalBreakpoints().FileHasBreakpoints(normalizedCurrentFilename)
						vm.debugger.breakpointMutex.RLock()
						_, newFileHasLocalBP := vm.debugger.breakpoints[normalizedCurrentFilename]
						vm.debugger.breakpointMutex.RUnlock()

						// A file is considered a user file if:
						// 1. It has breakpoints, OR
						// 2. It's a local file (starts with /) with a user-code extension (.ts, .js, .mjs)
						// This allows stepping into imported modules from the same project
						isUserSourceFile := newFileHasGlobalBP || newFileHasLocalBP
						if !isUserSourceFile {
							// Check if it looks like a user source file by extension and path
							isUserSourceFile = IsUserSourceFilePath(normalizedCurrentFilename)
						}

						if !isUserSourceFile {
							// Entering non-user file:
							// - For stepIn: clear the flag (we don't want to step through internal code)
							// - For next (step-over): preserve the flag so stepping continues when we return to user code
							//   This is the key fix: step-over should step OVER function calls into non-user code
							vm.debugger.stepIn = false
							// DON'T clear next here - let step-over continue when we return
							// Skip further breakpoint processing for this instruction
							goto executeInstruction
						} else if vm.debugger.stepIn {
							// Entering a user source file during step-in: update the stepping filename
							// This allows stepping to continue in the new file
							vm.debugger.steppingFilename = currentFilename
						}
					}

					// PERF: Use cached isUserFile result when vm.prg hasn't changed.
					// The cache covers breakpoint lookups (RLock), FileHasBreakpoints,
					// extension checks, and normalizeFilenameForMatch — all expensive.
					// Only the stepping-filename match (cheap string ==) runs uncached.
					needCompute := false
					if vm.prg == vm.debugger.cachedIsUserFilePrg {
						isUserFile = vm.debugger.cachedIsUserFile
						// Cheap: also check stepping filename match (not cached since it changes per-step)
						if !isUserFile && normalizedCurrentFilename == normalizedSteppingFilename && normalizedSteppingFilename != "" {
							isUserFile = true
						}
					} else if vm.debugger.cachedIsUserFileByName != nil {
						// PERF: Second-level cache keyed by filename — survives function calls
						// within the same bundled file (where *Program changes but filename stays the same).
						if cached, found := vm.debugger.cachedIsUserFileByName[normalizedCurrentFilename]; found {
							isUserFile = cached
							vm.debugger.cachedIsUserFile = cached
							vm.debugger.cachedIsUserFilePrg = vm.prg
							// Still check stepping filename match
							if !isUserFile && normalizedCurrentFilename == normalizedSteppingFilename && normalizedSteppingFilename != "" {
								isUserFile = true
							}
						} else {
							needCompute = true
						}
					} else {
						needCompute = true
					}
					if needCompute {
						// Check if current file is the stepping file OR has breakpoints OR is a user source file
						if normalizedCurrentFilename == normalizedSteppingFilename && normalizedSteppingFilename != "" {
							isUserFile = true
						} else {
							// PERF: Use FileHasBreakpoints() instead of GetAllBreakpoints()
							if GetGlobalBreakpoints().FileHasBreakpoints(normalizedCurrentFilename) {
								isUserFile = true
							}
							vm.debugger.breakpointMutex.RLock()
							if _, hasLocalBP := vm.debugger.breakpoints[normalizedCurrentFilename]; hasLocalBP {
								isUserFile = true
							}
							vm.debugger.breakpointMutex.RUnlock()
							// Also check if it looks like a user source file by extension and path
							// This allows stepping into imported modules from the same project
							if !isUserFile {
								isUserFile = IsUserSourceFilePath(normalizedCurrentFilename)
							}
						}

						// Fuzzy match for .ts -> .js transpilation
						// PERF: Cache normalizeFilenameForMatch result per-prg
						if vm.debugger.cachedBaseFilePrg != vm.prg {
							vm.debugger.cachedBaseFile = normalizeFilenameForMatch(normalizedCurrentFilename)
							vm.debugger.cachedBaseFilePrg = vm.prg
						}
						baseCurrentFile := vm.debugger.cachedBaseFile

						if !isUserFile && normalizedSteppingFilename != "" {
							if baseCurrentFile == normalizeFilenameForMatch(normalizedSteppingFilename) {
								isUserFile = true
							}
						}

						// Also check globalBPs with fuzzy match (both .ts and .js variants)
						if !isUserFile {
							for _, ext := range []string{".ts", ".js", ".mjs", ".tsx"} {
								if GetGlobalBreakpoints().FileHasBreakpoints(baseCurrentFile + ext) {
									isUserFile = true
									break
								}
							}
						}

						// Cache the result (without the stepping filename match).
						// The stepping filename is checked cheaply above on cache hit.
						cachedResult := isUserFile
						// If isUserFile is true ONLY because of stepping filename match,
						// cache false (the stepping match is done separately on cache hit).
						if isUserFile && normalizedCurrentFilename == normalizedSteppingFilename && normalizedSteppingFilename != "" {
							// Check if it would be true without the stepping match
							hasBP := GetGlobalBreakpoints().FileHasBreakpoints(normalizedCurrentFilename)
							vm.debugger.breakpointMutex.RLock()
							_, hasLocal := vm.debugger.breakpoints[normalizedCurrentFilename]
							vm.debugger.breakpointMutex.RUnlock()
							isExtUser := IsUserSourceFilePath(normalizedCurrentFilename)
							if !hasBP && !hasLocal && !isExtUser {
								cachedResult = false // only true due to stepping match
							}
						}
						vm.debugger.cachedIsUserFile = cachedResult
						vm.debugger.cachedIsUserFilePrg = vm.prg
						// Save to filename-keyed map for cross-function cache hits
						if vm.debugger.cachedIsUserFileByName == nil {
							vm.debugger.cachedIsUserFileByName = make(map[string]bool)
						}
						vm.debugger.cachedIsUserFileByName[normalizedCurrentFilename] = cachedResult
					}

					if vm.debugger.stepIn {
						// For step-in: break only if:
						// 1. We've advanced past the initial PC (ensuring we executed at least one instruction)
						// 2. We're at a DIFFERENT line (currentLine != prevLine), AND
						// 3. VM is in a valid state (vm.sb >= 0, not transitioning contexts)
						//    EXCEPTION: At PC=0 with prevPC=-1 (lifecycle function entry after ResetLastBreakpoint),
						//    vm.sb is -1 because the scope-setup instruction hasn't executed yet.
						//    We treat this as valid to avoid skipping the first line of lifecycle functions.
						// 4. We're in a user file (not internal k6 code)
						// Note: We DON'T check stack depth - we want to step into function calls
						pcAdvanced := currentPC != prevPC
						lineChanged := prevLine != currentLine
						// LIFECYCLE FIX: At function entry (PC=0, prevPC=-1), vm.sb is -1 because
						// the scope-setup instruction at PC=0 hasn't executed yet (debug check runs BEFORE
						// the instruction). Treat this as valid state so the first line of setup(),
						// default(), teardown(), handleSummary() is not skipped during step-in.
						isLifecycleFunctionEntry := currentPC == 0 && prevPC == -1
						vmInValidState := vm.sb >= 0 || isLifecycleFunctionEntry


						// Skip control-flow-only instructions (same as step-over)
						isControlFlowOnly := false
						if currentPC >= 0 && currentPC < len(vm.prg.code) {
							switch vm.prg.code[currentPC].(type) {
							// NOTE: 'jump' is intentionally NOT listed here.
							// User-written continue/break statements compile to jump
							// instructions that the debugger must stop on. Compiler-generated
							// jumps (end-of-if-body, loop back-edge, iteration-scope skips)
							// share the source line of their enclosing statement, so
							// lineChanged=false prevents false stops on them. Try-catch exit
							// jumps are handled by the lastExecPC checks below.
							case *leaveBlock, *enterCatchBlock, leaveTry, enterFinally, *yieldMarker:
								isControlFlowOnly = true
							// Class definition setup instructions: the bytecodes between
							// enterBlock and the finalizing leaveBlock for a class literal
							// interleave source lines (class line → method line → class line),
							// causing false step breaks on the class definition line.
							// Treat them all as non-steppable so the class declaration is
							// executed as a single step.
							case *newClass, *newDerivedClass, *newStaticFieldInit, *initStaticElements,
								defineComputedKey,
								*defineMethodKeyed, *defineGetterKeyed, *defineSetterKeyed,
								*defineMethod, *defineGetter, *defineSetter,
								*definePrivateMethod, *definePrivateGetter, *definePrivateSetter:
								isControlFlowOnly = true
							}
						}
						// Same forward-jump detection as step-over (see comments there).
						// NOTE: Use lastExecPC (the actual last executed instruction's PC),
						// NOT prevPC (which is the last BREAKPOINT PC and may be stale).
						if !isControlFlowOnly && lastExecPC >= 0 && lastExecPC < len(vm.prg.code) {
							switch vm.prg.code[lastExecPC].(type) {
							case leaveTry, enterFinally:
								isControlFlowOnly = true
							case jump:
								if currentPC > lastExecPC {
									nextPC := lastExecPC + 1
									if nextPC < len(vm.prg.code) {
										switch vm.prg.code[nextPC].(type) {
										case *enterCatchBlock, enterFinally:
											isControlFlowOnly = true
										}
									}
								}
							case jneP, jeqP, jne, jeq:
								// Same as step-over: conditional jumps skipping over try blocks.
								if currentPC > lastExecPC {
									nextPC := lastExecPC + 1
									if nextPC < len(vm.prg.code) {
										switch vm.prg.code[nextPC].(type) {
										case try, *enterCatchBlock, enterFinally:
											isControlFlowOnly = true
										}
									}
								}
								// When a conditional jump takes a forward jump (skipping an
								// if-body because the condition is false), the landing instruction
								// may inherit the source-map position of the last instruction in
								// the skipped body. Detect: if the landing line matches any source
								// line in the skipped PC range, it's an inherited/stale position.
								if !isControlFlowOnly && currentPC > lastExecPC+1 && vm.prg.src != nil {
									landingLine := currentLine
									scanLimit := currentPC
									if scanLimit > lastExecPC+64 {
										scanLimit = lastExecPC + 64
									}
									for scanPC := lastExecPC + 1; scanPC < scanLimit; scanPC++ {
										scanPos := vm.prg.src.Position(vm.prg.sourceOffset(scanPC))
										if scanPos.Line == landingLine {
											isControlFlowOnly = true
											vm.debugger.suppressedInheritedLine = landingLine
											vm.debugger.suppressedInheritedFile = normalizedCurrentFilename
											if debugVM {
												fmt.Printf("[VM-STEPIN-CJUMP] Conditional jump from PC=%d landed at PC=%d (line %d) — line matches skipped body PC=%d, marking as control-flow-only\n",
													lastExecPC, currentPC, landingLine, scanPC)
											}
											break
										}
									}
								}
							}
						}

						shouldBreak = pcAdvanced && lineChanged && vmInValidState && isUserFile && !isControlFlowOnly && !suppressedByInheritedLine
						breakReason = "stepIn"

						// CLASS-STEP DIAGNOSTIC: Log every instruction during step-in to trace class issues
						if debugVM && isUserFile {
							instrType := "?"
							if currentPC >= 0 && currentPC < len(vm.prg.code) {
								instrType = fmt.Sprintf("%T", vm.prg.code[currentPC])
							}
							fmt.Printf("[VM-CLASS-DIAG] stepIn PC=%d lastExecPC=%d line=%d prevLine=%d instr=%s pcAdv=%v lineChg=%v validState=%v cfOnly=%v suppressed=%v shouldBreak=%v file=%s\n",
								currentPC, lastExecPC, currentLine, prevLine, instrType,
								pcAdvanced, lineChanged, vmInValidState, isControlFlowOnly, suppressedByInheritedLine, shouldBreak, normalizedCurrentFilename)
						}

						// STEP-IN FIX: When stepping into a function call, the first
						// instructions (enterFunc at PC=0, initStash at PC=1, etc.) are
						// function scope setup. They all map to the function/class
						// declaration line (often the top of the file for imported
						// classes), NOT the first executable statement. Skip any
						// instruction that shares the same source line as PC=0 (the
						// function signature) so the debugger lands on the first real
						// line inside the function body.
						//
						// Phase 1: At function entry (lastExecPC==-1), record the entry line.
						// Phase 2: On subsequent PCs, keep skipping while on the same line.
						if shouldBreak && lastExecPC == -1 && vm.prg.src != nil && len(vm.prg.code) > 0 {
							entryLine := vm.prg.src.Position(vm.prg.sourceOffset(0)).Line
							if currentLine == entryLine {
								shouldBreak = false
								breakReason = "stepIn-skip-func-entry"
								// Record the entry line so subsequent PCs on the same line are also skipped
								vm.debugger.stepInSkipEntryLine = entryLine
								vm.debugger.stepInSkipEntryPrg = vm.prg
							}
						}
						// Phase 2: Continue skipping while on the entry line (covers initStash, etc.)
						if shouldBreak && vm.debugger.stepInSkipEntryLine > 0 && vm.debugger.stepInSkipEntryPrg == vm.prg {
							if currentLine == vm.debugger.stepInSkipEntryLine {
								shouldBreak = false
								breakReason = "stepIn-skip-func-entry-continued"
								if debugVM {
									fmt.Printf("[VM-CLASS-DIAG] Skipping entry-line PC=%d (line=%d == entryLine=%d)\n",
										currentPC, currentLine, vm.debugger.stepInSkipEntryLine)
								}
							} else {
								// We've moved past the entry line — clear the skip
								vm.debugger.stepInSkipEntryLine = 0
								vm.debugger.stepInSkipEntryPrg = nil
							}
						}

						// FIX: Also check inherited position for step-in (same as step-over).
						if shouldBreak && currentPC > 0 && lastExecPC >= 0 && currentPC > lastExecPC+1 && vm.prg.src != nil {
							prevInstrLine := vm.prg.src.Position(vm.prg.sourceOffset(currentPC - 1)).Line
							if prevInstrLine == currentLine {
								shouldBreak = false
								breakReason = "stepIn-inherited-pos-after-jump"
								vm.debugger.suppressedInheritedLine = currentLine
								vm.debugger.suppressedInheritedFile = normalizedCurrentFilename
								if debugVM {
									fmt.Printf("[VM-STEPIN-SKIP] Skipping step-in break at line %d (PC=%d): reached via forward jump from lastExecPC=%d, prev bytecode (PC=%d) has same source line\n",
										currentLine, currentPC, lastExecPC, currentPC-1)
								}
							}
						}

						// DIAGNOSTIC: Log when step-in would break near an if-body to trace false breaks
						if shouldBreak && vm.debugger.enableDebugLogging && lastExecPC >= 0 && currentPC > lastExecPC+1 {
							lastExecInstrType := fmt.Sprintf("%T", vm.prg.code[lastExecPC])
							curInstrType := fmt.Sprintf("%T", vm.prg.code[currentPC])
							prevBytecodeLineStr := "N/A"
							if currentPC > 0 && vm.prg.src != nil {
								prevBytecodeLineStr = fmt.Sprintf("%d", vm.prg.src.Position(vm.prg.sourceOffset(currentPC-1)).Line)
							}
							fmt.Printf("[VM-STEPIN-DIAG] STEPIN WILL FIRE after forward jump: line=%d, PC=%d, lastExecPC=%d, gap=%d, curInstr=%s, lastExecInstr=%s, prevBytecodeLine=%s, isControlFlowOnly=%v, file=%s\n",
								currentLine, currentPC, lastExecPC, currentPC-lastExecPC, curInstrType, lastExecInstrType, prevBytecodeLineStr, isControlFlowOnly, currentFilename)
						}

						// FIX: Skip sub-expressions in multi-line call expressions (stepIn).
						// Two-level guard:
						// Guard 1: Same-depth — use lastPCForLine from lastBreakpoint (existing logic).
						// Guard 2: stepInLastPC — skip until we pass the last PC of the line where
						//   stepIn was initiated, even across depth changes caused by short-lived
						//   call frames (e.g., this.isCacheValid() argument evaluation pushing and
						//   popping a call frame before we reach the next source line).
						//
						// CRITICAL: Only skip when currentPC > lastExecPC (moving forward).
						// If the VM jumped backward, we're in a new loop iteration.
						if shouldBreak {
							// Guard 1: same-depth sub-expression skip
							startDepth := vm.debugger.lastBreakpoint.stackDepth
							if currentStackDepth <= startDepth {
							startPC := vm.debugger.lastBreakpoint.pc
							startLine := vm.debugger.lastBreakpoint.line
							lastPC := vm.prg.lastPCForLine(startLine, startPC, vm.debugger.lastBreakpoint.filename)
							// LOOP GUARD: disable sub-expression skip if range spans a loop body
							if lastPC > startPC && vm.prg.hasBackwardJumpBetween(startPC, lastPC) {
								lastPC = -1
							}
								if lastPC >= 0 && currentPC <= lastPC && currentPC > lastExecPC {
									shouldBreak = false
									breakReason = "stepIn-skip-subexpr"
								}
							}
							// Guard 2: stepInLastPC — skip until we pass the initiation line's
							// last bytecode. This handles the case where argument evaluation
							// temporarily increases depth (e.g., this.isCacheValid() call frame
							// is pushed and popped before we reach the next source line).
							//
							// CRITICAL: Only apply when we're in the SAME program that
							// stepInLastPC was computed for. When a function is entered via
							// __call (e.g., class constructor, instance_members_initializer),
							// vm.prg changes OUTSIDE the debug loop, so the in-loop
							// program-change reset doesn't fire. A stale stepInLastPC from
							// the caller's program would suppress all breaks in the callee.
							if shouldBreak && vm.debugger.stepInLastPC >= 0 && vm.debugger.stepInLastPCPrg == vm.prg {
								if currentPC <= vm.debugger.stepInLastPC && currentPC > lastExecPC {
									shouldBreak = false
									breakReason = "stepIn-skip-initline"
								} else if currentPC > vm.debugger.stepInLastPC {
									// We've passed the initiation line — clear the guard
									vm.debugger.stepInLastPC = -1
									vm.debugger.stepInLastPCPrg = nil
								}
							} else if vm.debugger.stepInLastPC >= 0 && vm.debugger.stepInLastPCPrg != vm.prg {
								// Different program — guard is invalid, clear it
								vm.debugger.stepInLastPC = -1
								vm.debugger.stepInLastPCPrg = nil
							}
						}
						// RETURN-LINE FIX removed: forcing a break when a _ret instruction
						// shares the same source line as the step-start line caused a
						// double-break on the last line of every function with an explicit
						// return (the user had to press step-in twice to leave the function).
						// Standard debugger semantics: stepping from line N must always
						// advance to a DIFFERENT line. The _ret on the same line is simply
						// part of executing that line and should not pause again.

						if isLifecycleFunctionEntry && isUserFile && debugVM {
							fmt.Printf("[VM-LIFECYCLE-ENTRY] 🎯 Lifecycle function entry detected at line %d (PC=0, prevPC=-1, sb=%d). vmInValidState forced to %v (would be %v without fix). shouldBreak=%v\n",
								currentLine, vm.sb, vmInValidState, vm.sb >= 0, shouldBreak)
						}

						// CLASS-STEP DIAGNOSTIC: When step-in is about to break, dump surrounding bytecodes
						if shouldBreak && debugVM && isUserFile {
							fmt.Printf("[VM-CLASS-DIAG] *** STEP-IN WILL BREAK at line=%d PC=%d reason=%s ***\n", currentLine, currentPC, breakReason)
							// Dump bytecodes around the break point
							dumpStart := currentPC - 5
							if dumpStart < 0 {
								dumpStart = 0
							}
							dumpEnd := currentPC + 10
							if dumpEnd > len(vm.prg.code) {
								dumpEnd = len(vm.prg.code)
							}
							for i := dumpStart; i < dumpEnd; i++ {
								marker := "  "
								if i == currentPC {
									marker = ">>"
								}
								instrLine := 0
								if vm.prg.src != nil {
									instrLine = vm.prg.src.Position(vm.prg.sourceOffset(i)).Line
								}
								fmt.Printf("[VM-CLASS-DIAG] %s [PC=%d] line=%d %T %v\n", marker, i, instrLine, vm.prg.code[i], vm.prg.code[i])
							}
						}

						// Per-instruction step-in state logging commented out to reduce noise.
						// Uncomment for low-level step-in tracing.
						// if vm.debugger.enableDebugLogging && isUserFile {
						// 	fmt.Printf("[VM] stepIn=true, PC=%d (prev=%d), line=%d (prev=%d), depth=%d (prev=%d), pcAdvanced=%v, lineChanged=%v, vmInValidState=%v (sb=%d, lifecycleEntry=%v), isUserFile=%v, shouldBreak=%v\n",
						// 		currentPC, prevPC, currentLine, prevLine, currentStackDepth, prevStackDepth, pcAdvanced, lineChanged, vmInValidState, vm.sb, isLifecycleFunctionEntry, isUserFile, shouldBreak)
						// }
						// If we're not in user file during stepIn, clear stepIn flag to stop stepping through internal code
						// BUT preserve next flag so step-over continues to work when we return to user code
						// CRITICAL FIX: Don't clear stepIn if this is a lifecycle transition
						// During lifecycle transitions (setup->teardown->handleSummary), we want to preserve stepIn
						// until we reach the first line of the user's function
						if !isUserFile && pcAdvanced && !vm.debugger.lifecycleTransition {
							vm.debugger.stepIn = false
							// DON'T clear next here - let step-over continue working after we return from non-user code
							// vm.debugger.next = false
							// vm.debugger.steppingFilename = ""
						}
					} else if vm.debugger.next {
						// For step-over: break only if:
						// 1. We've advanced past the initial PC (ensuring we executed at least one instruction)
						// 2. We're at a DIFFERENT line from where step-over STARTED (not from previous instruction), AND
						// 3. We're at the same depth or returned from a call (shallower than where we STARTED), AND
						// 4. VM is in a valid state (vm.sb >= 0, not transitioning contexts)
						// 5. We're in a user file (not internal k6 code)
						// CRITICAL FIX: Compare against stepOverStartLine (where we STARTED the step-over), not prevLine
						// which can change erratically when entering/exiting native Go functions.
						// This prevents the "requires 2 clicks" bug on lines like http.get() or sleep()
						pcAdvanced := currentPC != prevPC
						startLine := vm.debugger.stepOverStartLine
						// Line is considered changed if we're on a different line from where step-over started
						// We use startLine (captured at step-over start) instead of prevLine because:
						// - prevLine can become -1 or invalid during native function calls
						// - When returning from native calls, prevLine != currentLine could be true
						//   even though we're back on the same source line where step-over started
						// - Multiple bytecode instructions can exist on the same source line
						//
						// CRITICAL: Only use stepOverStartLine when it's VALID (positive).
						// If it's 0 or negative, it means step-over was just initiated and we haven't captured
						// the start line yet - in this case, DON'T break (wait for proper setup).
						lineChanged := false
						if startLine > 0 {
							lineChanged = startLine != currentLine
						} else if currentLine > 0 {
							// SELF-HEAL: stepOverStartLine is invalid but we found a valid
							// source line. Capture it as the new start line so the NEXT
							// instruction on a different line triggers the break immediately.
							// Without this, the debugger loops through thousands of instructions
							// (3000+) looking for a valid state, causing hangs during error handling.
							vm.debugger.stepOverStartLine = currentLine
							startLine = currentLine
							// Don't set lineChanged yet — we just established the baseline.
							// The very next instruction on a different line will trigger the break.
						} else {
							// Both startLine and currentLine are invalid (no source map entries).
							// Increment a safety counter to prevent infinite looping during error
							// handling where the VM never reaches code with source maps.
							vm.debugger.stepOverMissCount++
							if vm.debugger.stepOverMissCount > 500 {
								// Safety valve: clear step flags after 500 instructions with no
								// valid source lines. This prevents the debugger from hanging
								// when errors occur during init/module loading.
								if debugVM {
									fmt.Printf("[VM] next=true, SAFETY: clearing step flags after %d instructions with no valid source line\n", vm.debugger.stepOverMissCount)
								}
								vm.debugger.next = false
								vm.debugger.stepIn = false
								vm.debugger.stepOverStartLine = 0
								vm.debugger.stepOverMissCount = 0
								goto executeInstruction
							}
						}

						// Log if we're skipping due to invalid startLine (only first few to avoid log spam)
						if startLine <= 0 && vm.debugger.enableDebugLogging && isUserFile && vm.debugger.stepOverMissCount <= 5 {
							fmt.Printf("[VM] next=true, SKIPPING: invalid startLine=%d (waiting for valid state, miss=%d)\n", startLine, vm.debugger.stepOverMissCount)
						}

						atValidDepth := currentStackDepth <= vm.debugger.stepOverTargetDepth
						// LIFECYCLE FIX: Same as stepIn - at function entry (PC=0, prevPC=-1),
						// vm.sb is -1 because the scope-setup instruction hasn't executed yet.
						// Treat this as valid state for lifecycle function entry.
						isLifecycleFunctionEntry := currentPC == 0 && prevPC == -1
						vmInValidState := vm.sb >= 0 || isLifecycleFunctionEntry

						// Skip breaking on control-flow-only instructions.
						// The source map may map these to a source line inside a catch/finally block,
						// but the VM is just jumping over it — the code on that line does not execute.
						// Without this check, step-over falsely stops inside non-executing catch blocks.
						// NOTE: The gate must NOT be vm.debugger.active — active=true only when paused,
						// so it's always false during the instruction loop. Check the PC directly.
						//
						// NOTE: 'jump' is intentionally NOT listed here.
						// User-written continue/break statements compile to jump instructions
						// that the debugger must stop on. Compiler-generated jumps share the
						// source line of their enclosing statement (lineChanged=false prevents
						// false stops). Try-catch exit jumps are handled by the lastExecPC
						// checks below.
						isControlFlowOnly := false
						if currentPC >= 0 && currentPC < len(vm.prg.code) {
							switch vm.prg.code[currentPC].(type) {
							case *leaveBlock, *enterCatchBlock, leaveTry, enterFinally, *yieldMarker:
								isControlFlowOnly = true
							// Class definition setup — same as step-in (see comment there).
							case *newClass, *newDerivedClass, *newStaticFieldInit, *initStaticElements,
								defineComputedKey,
								*defineMethodKeyed, *defineGetterKeyed, *defineSetterKeyed,
								*defineMethod, *defineGetter, *defineSetter,
								*definePrivateMethod, *definePrivateGetter, *definePrivateSetter:
								isControlFlowOnly = true
							}
						}
						// Also detect forward jumps that skip over try-catch blocks.
						// The source map often maps the post-try cleanup PC to the catch/finally
						// source line, causing false breaks in non-executing catch blocks.
						//
						// NOTE: Use lastExecPC (the actual last executed instruction's PC),
						// NOT prevPC (which is the last BREAKPOINT PC and may be stale).
						// Check 1: Previous instruction was leaveTry/enterFinally (explicit try exit).
						// Check 2: Previous instruction was an unconditional jump whose next bytecode
						//          is enterCatchBlock/enterFinally — i.e., a try-catch exit jump.
						//          Regular if/else forward jumps are NOT suppressed.
						if !isControlFlowOnly && lastExecPC >= 0 && lastExecPC < len(vm.prg.code) {
							switch vm.prg.code[lastExecPC].(type) {
							case leaveTry, enterFinally:
								isControlFlowOnly = true
							case jump:
								// Only mark as control-flow-only if this jump is a try-catch exit:
								// the instruction immediately after the jump is enterCatchBlock or
								// enterFinally. Regular if/else forward jumps (skipping the else body)
								// must NOT be suppressed — otherwise the debugger skips lines after
								// if/else blocks and in else branches.
								if currentPC > lastExecPC {
									nextPC := lastExecPC + 1
									if nextPC < len(vm.prg.code) {
										switch vm.prg.code[nextPC].(type) {
										case *enterCatchBlock, enterFinally:
											isControlFlowOnly = true
										}
									}
								}
							case jneP, jeqP, jne, jeq:
								// Conditional jumps that skip over a try block.
								// When an if-condition (e.g., `if (cond) { try { ... } catch { ... } }`)
								// is false, the conditional jump skips the entire if-body. If the
								// if-body starts with a `try` instruction, the jump lands PAST the
								// try-catch, at a PC whose source map points to the catch-block line.
								// Detect this by checking if the instruction right after the conditional
								// jump is `try` — meaning we jumped over a try-catch block.
								// This does NOT affect regular if/else: else bodies don't start with `try`.
								if currentPC > lastExecPC {
									nextPC := lastExecPC + 1
									if nextPC < len(vm.prg.code) {
										switch vm.prg.code[nextPC].(type) {
										case try, *enterCatchBlock, enterFinally:
											isControlFlowOnly = true
										}
									}
								}
								// When a conditional jump takes a forward jump (skipping an
								// if-body because the condition is false), the landing instruction
								// may inherit the source-map position of the last instruction in
								// the skipped body. Detect: if the landing line matches any source
								// line in the skipped PC range, it's an inherited/stale position.
								// This does NOT affect else branches: else-body lines are distinct
								// from if-body lines, so the landing line won't match.
								if !isControlFlowOnly && currentPC > lastExecPC+1 && vm.prg.src != nil {
									landingLine := currentLine
									scanLimit := currentPC
									if scanLimit > lastExecPC+64 {
										scanLimit = lastExecPC + 64
									}
									for scanPC := lastExecPC + 1; scanPC < scanLimit; scanPC++ {
										scanPos := vm.prg.src.Position(vm.prg.sourceOffset(scanPC))
										if scanPos.Line == landingLine {
											isControlFlowOnly = true
											// Remember this line so subsequent instructions
											// with the same inherited position are also suppressed
											vm.debugger.suppressedInheritedLine = landingLine
											vm.debugger.suppressedInheritedFile = normalizedCurrentFilename
											if debugVM {
												fmt.Printf("[VM-STEPOVER-CJUMP] Conditional jump from PC=%d landed at PC=%d (line %d) — line matches skipped body PC=%d, marking as control-flow-only\n",
													lastExecPC, currentPC, landingLine, scanPC)
											}
											break
										}
									}
								}
							}
						}

						shouldBreak = pcAdvanced && lineChanged && atValidDepth && vmInValidState && isUserFile && !isControlFlowOnly && !suppressedByInheritedLine
						breakReason = "next"

						// FIX: Also check inherited position for step-over.
						// The isControlFlowOnly scan above catches the FIRST instruction
						// after a conditional jump, but subsequent instructions at the
						// jump target may also have inherited source positions. Check
						// if we reached this PC via a forward jump and the previous
						// bytecode has the same source line (inherited position).
						if shouldBreak && currentPC > 0 && lastExecPC >= 0 && currentPC > lastExecPC+1 && vm.prg.src != nil {
							prevInstrLine := vm.prg.src.Position(vm.prg.sourceOffset(currentPC - 1)).Line
							if prevInstrLine == currentLine {
								shouldBreak = false
								breakReason = "next-inherited-pos-after-jump"
								vm.debugger.suppressedInheritedLine = currentLine
								vm.debugger.suppressedInheritedFile = normalizedCurrentFilename
								if debugVM {
									fmt.Printf("[VM-STEPOVER-SKIP] Skipping step-over break at line %d (PC=%d): reached via forward jump from lastExecPC=%d, prev bytecode (PC=%d) has same source line\n",
										currentLine, currentPC, lastExecPC, currentPC-1)
								}
							}
						}

						// DIAGNOSTIC: Log when step-over would break after a forward jump
						if shouldBreak && vm.debugger.enableDebugLogging && lastExecPC >= 0 && currentPC > lastExecPC+1 {
							lastExecInstrType := fmt.Sprintf("%T", vm.prg.code[lastExecPC])
							curInstrType := fmt.Sprintf("%T", vm.prg.code[currentPC])
							prevBytecodeLineStr := "N/A"
							if currentPC > 0 && vm.prg.src != nil {
								prevBytecodeLineStr = fmt.Sprintf("%d", vm.prg.src.Position(vm.prg.sourceOffset(currentPC-1)).Line)
							}
							fmt.Printf("[VM-STEPOVER-FWDJUMP] STEPOVER WILL FIRE after forward jump: line=%d, PC=%d, lastExecPC=%d, gap=%d, curInstr=%s, lastExecInstr=%s, prevBytecodeLine=%s, isControlFlowOnly=%v, file=%s\n",
								currentLine, currentPC, lastExecPC, currentPC-lastExecPC, curInstrType, lastExecInstrType, prevBytecodeLineStr, isControlFlowOnly, currentFilename)
						}


						// FIX: Skip sub-expressions in multi-line call expressions.
						// When stepping over from line N, the compiler may emit bytecodes
						// for argument evaluation on different source lines (e.g., object
						// properties), but the call instruction itself maps BACK to line N.
						// stepOverLastPC is the last PC mapping to the start line — don't
						// break until we've passed it. This matches Node.js/V8 behaviour.
						//
						// CRITICAL: Only skip when currentPC > lastExecPC (moving forward).
						// If the VM jumped backward (currentPC < lastExecPC), we're in a
						// new loop iteration — NOT a sub-expression. lastExecPC tracks the
						// actual last executed instruction, so it catches backward jumps
						// from any point in the loop (header, body, or continuation check).
						//
						// CRITICAL: Only skip when vm.prg matches the program where
						// stepOverLastPC was computed. When a function returns to its
						// caller (different vm.prg), the caller's PCs are unrelated
						// to stepOverLastPC — comparing them causes ALL breakpoints
						// in the caller to be skipped (the "loop back" / "runs through"
						// bug when stepping over a function call).
						sameProgram := vm.debugger.stepOverLastPCPrg == nil || vm.debugger.stepOverLastPCPrg == vm.prg
						if shouldBreak && vm.debugger.stepOverLastPC >= 0 && sameProgram && currentPC <= vm.debugger.stepOverLastPC && currentPC > lastExecPC {
							shouldBreak = false
							breakReason = "next-skip-subexpr"
							if debugVM {
								fmt.Printf("[VM-STEP-OVER] Skipping sub-expression at line %d (PC=%d <= lastPC=%d for start line %d)\n",
									currentLine, currentPC, vm.debugger.stepOverLastPC, startLine)
							}
						}

						// RETURN-LINE FIX removed: forcing a break when a _ret instruction
						// shares the same source line as the step-over start line caused a
						// double-break on the last line of every imported function with an
						// explicit return (the user had to press Next twice to leave the
						// function). Standard debugger semantics: step-over from line N must
						// always advance to a DIFFERENT line. The _ret on the same line is
						// simply part of executing that line and should not pause again.
						// The implicit return case (_loadUndef + _ret) was already handled
						// by the isControlFlowOnly detection earlier in this code path.

						if isLifecycleFunctionEntry && isUserFile && debugVM {
							fmt.Printf("[VM-LIFECYCLE-ENTRY] 🎯 Lifecycle function entry (next) at line %d (PC=0, prevPC=-1, sb=%d). vmInValidState forced to %v. shouldBreak=%v\n",
								currentLine, vm.sb, vmInValidState, shouldBreak)
						}
						// Per-instruction step-over state logging commented out to reduce noise.
						// Uncomment for low-level step-over tracing.
						// if vm.debugger.enableDebugLogging && isUserFile {
						// 	fmt.Printf("[VM] next=true, PC=%d (prev=%d), line=%d (start=%d, prev=%d), depth=%d (target=%d, prev=%d), pcAdvanced=%v, lineChanged=%v, atValidDepth=%v, vmInValidState=%v (sb=%d, lifecycleEntry=%v), isUserFile=%v, shouldBreak=%v\n",
						// 		currentPC, prevPC, currentLine, startLine, prevLine, currentStackDepth, vm.debugger.stepOverTargetDepth, prevStackDepth, pcAdvanced, lineChanged, atValidDepth, vmInValidState, vm.sb, isLifecycleFunctionEntry, isUserFile, shouldBreak)
						// }
						// IMPORTANT: Log when step-over overrides a breakpoint to avoid confusion
						// The BREAKPOINT-CHECK log may have said "breakpoint detected" but step-over takes precedence
						if !shouldBreak && hasBreakpoint && debugVM {
							var skipReason string
							if !lineChanged {
								skipReason = fmt.Sprintf("still on start line %d", startLine)
							} else if !atValidDepth {
								skipReason = fmt.Sprintf("at deeper depth %d > target %d", currentStackDepth, vm.debugger.stepOverTargetDepth)
							} else if !pcAdvanced {
								skipReason = "PC not advanced"
							} else if !vmInValidState {
								skipReason = "VM not in valid state"
							} else if !isUserFile {
								skipReason = "not in user file"
							}
							if debugVM {
								fmt.Printf("[VM-STEP-OVER] ⚠️ Breakpoint at line %d SKIPPED due to step-over (%s)\n",
									currentLine, skipReason)
							}
						}
						// NOTE: For step-over, we do NOT clear next flag when in non-user file
						// This is intentional: step-over should step OVER function calls into non-user code
						// and continue stepping when we return to user code at the correct depth
						// The next flag will be cleared when we actually break (in the shouldBreak block below)
				} else {
					// For regular breakpoint: break if the SOURCE LINE or SOURCE FILE changed from where we last paused.
					// We compare the line number AND the source-mapped filename because:
					// 1. breakpoint() already confirmed this is a valid breakpoint location
					// 2. Multiple bytecodes map to the same source line — after Continue, the user
					//    should not be stopped again on subsequent PCs that are still on the same line
					// 3. In bundled TypeScript, different source files (CcsApi.ts vs Stores.ts) can
					//    have the same line number. We must compare the source-mapped filename too,
					//    otherwise breakpoints in file B on the same line as file A are skipped.
					sameFile := true
					srcMapFile := vm.debugger.cachedSrcMapFile
					if srcMapFile != "" && prevFilename != "" {
						sameFile = srcMapFile == prevFilename || normalizeFilenameForMatch(srcMapFile) == normalizeFilenameForMatch(prevFilename)
					}
					sameLine := prevLine == currentLine && prevLine > 0 && sameFile
					if sameLine {
						shouldBreak = false
						breakReason = "same-line-skip"
					} else {
						shouldBreak = true
						breakReason = "breakpoint"
					}

					// CRITICAL FIX: For explicit breakpoints (hasBreakpoint=true), do NOT
					// suppress via inherited-position heuristics. The user explicitly set a
					// breakpoint at this line — it MUST fire when the VM reaches any instruction
					// mapped to that line. This matches Node.js/V8 debugger semantics.
					//
					// The inherited-position suppression (suppressedByInheritedLine and the
					// forward-jump heuristic) are still applied for step operations (stepIn,
					// next) where false stops at inherited positions are confusing. But for
					// explicit breakpoints, the user's intent takes priority.
					//
					// Previously, these checks would suppress breakpoints during init phase
					// (module-level code) where forward jumps from import/require calls and
					// class constructors are common, causing breakpoints at lines like
					// `const x = value` to never fire.
					if !hasBreakpoint {
						// Only apply inherited-position suppression when there's no explicit breakpoint
						if suppressedByInheritedLine {
							shouldBreak = false
							breakReason = "suppressed-inherited-line"
						}

						// Inherited position check: detect forward jumps that land on instructions
						// with inherited source positions from skipped blocks.
						if shouldBreak && currentPC > 0 && lastExecPC >= 0 && currentPC > lastExecPC+1 && vm.prg.src != nil {
							prevInstrLine := vm.prg.src.Position(vm.prg.sourceOffset(currentPC - 1)).Line
							if prevInstrLine == currentLine {
								shouldBreak = false
								breakReason = "inherited-pos-after-jump"
								vm.debugger.suppressedInheritedLine = currentLine
								vm.debugger.suppressedInheritedFile = normalizedCurrentFilename
								if debugVM {
									fmt.Printf("[VM-BP-SKIP] Skipping break at line %d (PC=%d): reached via forward jump from lastExecPC=%d, prev bytecode (PC=%d) has same source line (inherited position)\n",
										currentLine, currentPC, lastExecPC, currentPC-1)
								}
							}
						}
					} else if suppressedByInheritedLine {
						// Clear the suppression — explicit breakpoint overrides inherited-position suppression
						vm.debugger.suppressedInheritedLine = 0
						vm.debugger.suppressedInheritedFile = ""
						if debugVM {
							fmt.Printf("[VM-BP-OVERRIDE] Explicit breakpoint at line %d overrides inherited-position suppression (PC=%d, lastExecPC=%d)\n",
								currentLine, currentPC, lastExecPC)
						}
					}
					// DIAGNOSTIC: Log when breakpoint fires at a line that was reached via forward jump
					// to diagnose cases where inherited-pos-after-jump didn't trigger
					if shouldBreak && vm.debugger.enableDebugLogging {
						curInstrType := fmt.Sprintf("%T", vm.prg.code[currentPC])
						lastExecInstrType := "N/A"
						if lastExecPC >= 0 && lastExecPC < len(vm.prg.code) {
							lastExecInstrType = fmt.Sprintf("%T", vm.prg.code[lastExecPC])
						}
						prevBytecodeLineStr := "N/A"
						if currentPC > 0 && vm.prg.src != nil {
							prevBytecodeLineStr = fmt.Sprintf("%d", vm.prg.src.Position(vm.prg.sourceOffset(currentPC-1)).Line)
						}
						fmt.Printf("[VM-BP-DIAG] BREAKPOINT WILL FIRE: line=%d, PC=%d, lastExecPC=%d, gap=%d, curInstr=%s, lastExecInstr=%s, prevBytecodeLine=%s, file=%s\n",
							currentLine, currentPC, lastExecPC, currentPC-lastExecPC, curInstrType, lastExecInstrType, prevBytecodeLineStr, currentFilename)
					}

					// Clear continuing unconditionally — it's now redundant with the line check
					// but we clear it for cleanliness so other code paths don't see stale state.
					vm.debugger.continuing = false
					if vm.debugger.enableDebugLogging {
						fmt.Printf("[VM] breakpoint check: sameLine=%v (line:%d->%d, file:%s->%s, PC:%d->%d), shouldBreak=%v, reason=%s\n",
							sameLine, prevLine, currentLine, prevFilename, currentFilename, prevPC, currentPC, shouldBreak, breakReason)
					}
				}

					// In the shouldBreak computation for regular breakpoints,
					// after hasBreakpoint is set to true:
					if hasBreakpoint && breakReason == "breakpoint" {
						// CONDITIONAL BP CHECK — wrapped in debug-enabled guard since it calls Evaluate
						if vm.debugger.conditionalBPs != nil {
							if !vm.debugger.shouldFireBreakpoint(normalizedCurrentFilename, currentLine) {
								hasBreakpoint = false // treat as no breakpoint
								shouldBreak = false
							}
						}
					}

					// DIAGNOSTIC: Log when a breakpoint was found but won't cause a break
					if hasBreakpoint && !shouldBreak && (debugBreakpoint || debugAll) {
						fmt.Printf("[BP-NO-BREAK] ⚠️ breakpoint found but shouldBreak=false: line=%d, file=%q, reason=%q, prevLine=%d, prevFile=%q, active=%v, vuID=%d\n",
							currentLine, normalizedCurrentFilename, breakReason, prevLine, prevFilename, vm.debugger.active, vm.debugger.vuID)
					}

						if shouldBreak {
						// DIAGNOSTIC: Log ALL breaks with forward-jump info
						if vm.debugger.enableDebugLogging {
							lastExecInstrType := "N/A"
							if lastExecPC >= 0 && lastExecPC < len(vm.prg.code) {
								lastExecInstrType = fmt.Sprintf("%T", vm.prg.code[lastExecPC])
							}
							curInstrType := "N/A"
							if currentPC >= 0 && currentPC < len(vm.prg.code) {
								curInstrType = fmt.Sprintf("%T", vm.prg.code[currentPC])
							}
							prevBytecodeLineStr := "N/A"
							if currentPC > 0 && vm.prg.src != nil {
								prevBytecodeLineStr = fmt.Sprintf("%d", vm.prg.src.Position(vm.prg.sourceOffset(currentPC-1)).Line)
							}
							fmt.Printf("[VM-BREAK-TRACE] WILL BREAK: reason=%s, line=%d, PC=%d, lastExecPC=%d, gap=%d, curInstr=%s, lastExecInstr=%s, prevBytecodeLine=%s, hasBreakpoint=%v, file=%s\n",
								breakReason, currentLine, currentPC, lastExecPC, currentPC-lastExecPC, curInstrType, lastExecInstrType, prevBytecodeLineStr, hasBreakpoint, currentFilename)
						}
						// SKIP-PHASE-ENTRY: When RunOnce() enabled stepIn for a lifecycle
						// transition AND set skipPhaseEntryBreak, don't stop at the
						// function-signature line (PC=0).  Record the position so that
						// the very next source line triggers the break instead.
						// This saves the user one unnecessary step-over.
						if vm.debugger.skipPhaseEntryBreak && currentPC == 0 && prevPC == -1 {
							if debugVM {
								fmt.Printf("[VM-LIFECYCLE-ENTRY] Skipping phase-entry break at line %d (PC=0) — will break at first statement\n", currentLine)
							}
							vm.debugger.skipPhaseEntryBreak = false
							// Record position so lineChanged becomes true on the next line
							vm.debugger.lastBreakpoint.filename = currentFilename
							vm.debugger.lastBreakpoint.line = currentLine
							vm.debugger.lastBreakpoint.pc = currentPC
							vm.debugger.lastBreakpoint.stackDepth = currentStackDepth
							goto executeInstruction
						}
						// Consume the flag if it's still set (we broke for another reason)
						vm.debugger.skipPhaseEntryBreak = false

						if vm.debugger.enableDebugLogging {
							// Clarify when we stopped due to step command but there's also a breakpoint here
							if hasBreakpoint && (breakReason == "next" || breakReason == "stepIn") {
								if debugVM {
									fmt.Printf("[VM] BREAKING at line %d (PC=%d), reason=%s (NOTE: also has breakpoint, step takes precedence)\n", currentLine, currentPC, breakReason)
								}
							} else if breakReason == "next" {
								if debugVM {
									fmt.Printf("[VM] BREAKING at line %d (PC=%d), reason=%s (step-over from line %d completed)\n",
									currentLine, currentPC, breakReason, vm.debugger.stepOverStartLine)
								}
							} else {
								if debugVM {
									fmt.Printf("[VM] BREAKING at line %d (PC=%d), reason=%s\n", currentLine, currentPC, breakReason)
								}
							}
						}
						vm.debugger.lastBreakpoint.filename = currentFilename
						vm.debugger.lastBreakpoint.line = currentLine
						vm.debugger.lastBreakpoint.pc = currentPC
						vm.debugger.lastBreakpoint.stackDepth = currentStackDepth

						// DIAGNOSTIC: Log when debugger will pause
						if debugVM || debugAll {
							phase := "default"
							if vm.debugger.initPhase {
								phase = "init"
							}
							fmt.Printf("[VM-WILL-BREAK] 🛑 PAUSING at %s:%d (PC=%d, reason=%s, phase=%s, vuID=%d, hasBreakpoint=%v)\n",
								currentFilename, currentLine, currentPC, breakReason, phase, vm.debugger.vuID, hasBreakpoint)
						}

						// CRITICAL FIX: Capture step flags BEFORE clearing them.
						// This allows activate() to know whether we broke due to a step command.
						wasStepIn := vm.debugger.stepIn
						wasNext := vm.debugger.next

						// Clear step flags BEFORE calling activate().
						// When we break, the current step operation is COMPLETE.
						// The user's NEXT command will set these flags again.
						vm.debugger.stepIn = false
						vm.debugger.next = false

						vm.debugger.stepOverStartLine = 0 // Clear start line for next step operation
						vm.debugger.stepInLastPC = -1     // Clear stepIn sub-expression guard
						vm.debugger.stepInLastPCPrg = nil // Clear stepIn program reference
						vm.debugger.stepInStartLine = 0   // Clear stepIn start line
						vm.debugger.stepInSkipEntryLine = 0 // Clear entry-line skip
						vm.debugger.stepInSkipEntryPrg = nil
						vm.debugger.continuing = false    // Clear continuing flag when we break
						vm.debugger.suppressedInheritedLine = 0 // Clear inherited-line suppression
						vm.debugger.suppressedInheritedFile = ""
						// NOTE: Do NOT clear global step state here! The activate() function reads and
						// clears it after applying it. Clearing here would race with activate() and
						// cause the global step state (e.g., set by EnableStepIn() for lifecycle transitions)
						// to be lost before activate() can read it.
						vm.debugger.updateCurrentLine()

						// Use the correct activation reason based on how we stopped
						var activationReason ActivationReason
						if breakReason == "stepIn" || breakReason == "next" {
							activationReason = StepActivation
						} else {
							activationReason = BreakpointActivation
						}

						// DIAGNOSTIC: Log step flags that were active when we decided to break
						if debugVM {
							fmt.Printf("[VM-PRE-ACTIVATE] VU=%d About to call activate(): wasStepIn=%v, wasNext=%v, lifecycleTransition=%v, reason=%s, line=%d\n",
								vm.debugger.vuID, wasStepIn, wasNext, vm.debugger.lifecycleTransition, breakReason, vm.debugger.currentLine)
						}

						// Pass the captured step flags to activate so it knows the context of the break
						vm.debugger.activateWithStepState(activationReason, vm.debugger.Filename(), vm.debugger.currentLine, wasStepIn, wasNext)

						// NOTE: activate() handles all flag clearing based on userCommandIssued.
						// We don't clear flags here anymore to avoid race conditions.
					}
				}
				// NOTE: We deliberately DON'T reset lastBreakpoint to -1 when the condition is false.
				// This is critical for proper "same location" checking - when execution enters code
				// without breakpoints (like a function call) and then returns to breakpoint-having code,
				// we need to preserve the last known breakpoint location to detect if we're still on
				// the same line or have moved to a new location.
				//
				// PERF: lastBreakpoint.stackDepth is updated inside the shouldBreak block
				// (along with line/filename/pc) and in activate(). No need to update it
				// on every instruction — it only matters at pause points.
			}
		}
	executeInstruction:
		if vm.prg == nil {
			break
		}
		pc := vm.pc
		if pc < 0 || pc >= len(vm.prg.code) {
			break
		}
		// Track actual previous instruction PC for forward-jump detection.
		lastExecPC = pc
		// Track vm.prg BEFORE exec — if it changes (function call pushes a new
		// program, or return pops back to a previous one), we must reset lastExecPC
		// to prevent cross-program PC contamination. Without this, the sub-expression
		// skip compares PCs from different programs, which is invalid and can cause
		// incorrect skip decisions (e.g., suppressing a break at a line that should
		// pause because lastExecPC from the callee happens to be < currentPC in the
		// caller).
		prevPrg := vm.prg
		// [VM-EXEC] and [VM-POST] per-instruction logging commented out to reduce noise.
		// These produce ~10 lines per bytecode instruction and dominate the log.
		// Uncomment for low-level instruction tracing when debugging step logic.
		// if vm.debugger != nil && debugVM && (vm.debugger.next || vm.debugger.stepIn) {
		// 	fmt.Printf("[VM-EXEC] PC=%d, instr=%T, next=%v, stepIn=%v, suppress=%v, depth=%d\n",
		// 		pc, vm.prg.code[pc], vm.debugger.next, vm.debugger.stepIn, vm.debugger.suppressDebugger, len(vm.callStack))
		// }
		vm.prg.code[pc].exec(vm)
		// Reset lastExecPC when program changes (call/return) to prevent
		// cross-program PC contamination in the sub-expression skip.
		if vm.prg != prevPrg {
			lastExecPC = -1
			// CRITICAL FIX: Invalidate stepInLastPC when the program changes.
			// stepInLastPC is computed by lastPCForLine() for the program where
			// step-in was initiated. After a function call, vm.prg points to a
			// completely different program whose PCs are an independent address
			// space. Comparing the new program's PCs against a value from the old
			// program causes Guard 2 to suppress breaks incorrectly — e.g.,
			// stepping into getAllStores would skip the first ~N instructions
			// (where N is the old stepInLastPC) and land on the catch block
			// instead of the first line.
			//
			// NOTE: stepOverLastPC is intentionally NOT cleared here. During
			// step-over, function calls don't trigger breaks (the depth check
			// prevents it). When the function returns, vm.prg reverts to the
			// original caller's program — so stepOverLastPC (computed for the
			// caller's PC space) is still valid and needed to skip sub-expressions
			// on the same line. Clearing it would remove the guard that prevents
			// false breaks at try-catch exit points whose source maps map to the
			// catch block's line.
			if vm.debugger != nil {
				vm.debugger.stepInLastPC = -1
				vm.debugger.stepInLastPCPrg = nil
			}
		}
		// if vm.debugger != nil && debugVM && (vm.debugger.next || vm.debugger.stepIn) {
		// 	newPC := vm.pc
		// 	halted := vm.prg == nil || newPC < 0 || newPC >= len(vm.prg.code)
		// 	fmt.Printf("[VM-POST] PC=%d->%d, halted=%v, next=%v, suppress=%v, depth=%d\n",
		// 		pc, newPC, halted, vm.debugger.next, vm.debugger.suppressDebugger, len(vm.callStack))
		// }
	}

	// When a VM finishes executing with a step operation active, we need to decide
	// whether to propagate the step intent to the next lifecycle phase.
	//
	// When the user was stepping through init code and init finishes, we want the
	// debugger to break at the FIRST LINE of the next lifecycle function (setup/default/teardown),
	// NOT at line 1 of the module (which would re-step through imports/init code).
	// We use waitForFunctionEntry to achieve this: the new VM skips module-level code
	// and only enables stepping when the call depth increases (entering the function body).
	//
	// SAFETY: Check vm.debugger != nil first — Detach() could have been called during execution.
	if vm.debugger != nil && (vm.debugger.next || vm.debugger.stepIn) {
		// Only handle this at top-level (callStackDepth <= 1 means we're exiting the main function)
		if vm.debugger.callStackDepth() <= 1 {
			if debugVM {
				fmt.Printf("[VM-EXIT] 🔄 Step operation active when VM exited (next=%v, stepIn=%v, depth=%d, lastLine=%d), setting waitForFunctionEntry for next lifecycle phase\n",
					vm.debugger.next, vm.debugger.stepIn, vm.debugger.callStackDepth(), vm.debugger.Line())
			}
			// Mark this debugger's VM as exited so Continue() won't send to its dead local channel
			vm.debugger.vmExited = true
			// Close vmDoneCh to instantly notify any waiting Continue() that this VM is done
			if vm.debugger.vmDoneCh != nil {
				select {
				case <-vm.debugger.vmDoneCh:
					// Already closed
				default:
					close(vm.debugger.vmDoneCh)
				}
			}
			// Clear the local step flags since this VM is done
			vm.debugger.next = false
			vm.debugger.stepIn = false
			// Clear any stale global step state
			GetGlobalCoordinator().ClearGlobalStepState()
			// Set waitForFunctionEntry so the next lifecycle phase (setup/default/teardown)
			// breaks at its first line, but does NOT re-step through module init code
			GetGlobalCoordinator().SetWaitForFunctionEntry(true)
		} else {
			// VM exited at depth > 1 with step flags still active. This is a
			// nested vm.runTry() (e.g., class field initializer). Do NOT clear
			// the step flags — they were set by the user (step-over at a
			// breakpoint inside the nested program) and must survive to the
			// outer vm.debug() loop. The caller (_initFields) only resets
			// vmExited/vmDoneCh.
			if debugVM {
				fmt.Printf("[VM-EXIT] 🔄 Step operation active at nested exit (next=%v, stepIn=%v, depth=%d) — preserving step flags for outer loop\n",
					vm.debugger.next, vm.debugger.stepIn, vm.debugger.callStackDepth())
			}
		}
	} else if vm.debugger != nil && debugVM {
		// Only log normal VM exits at shallow depths to avoid massive spam
		// during handleSummary text rendering (hundreds of function calls at depth 5-16)
		depth := vm.debugger.callStackDepth()
		if depth <= 2 {
			if debugVM {
				fmt.Printf("[VM-EXIT] VM exited normally (no step active, next=%v, stepIn=%v, depth=%d)\n",
				vm.debugger.next, vm.debugger.stepIn, depth)
			}
		}
	}

	if interrupted {
		vm.interruptLock.Lock()
		v := &InterruptedError{
			iface: vm.interruptVal,
		}
		v.stack = vm.captureStack(nil, 0)
		vm.interruptLock.Unlock()
		panic(v)
	}
}

// normalizeFilenameForMatch strips extension for comparison.
// Used only in isUserFile checks, NOT for breakpoint lookup.
func normalizeFilenameForMatch(f string) string {
	f = normalizeFilename(f)
	// Strip .ts/.tsx/.js/.mjs extension for fuzzy matching
	for _, ext := range []string{".ts", ".tsx", ".js", ".mjs"} {
		if strings.HasSuffix(f, ext) {
			return f[:len(f)-len(ext)]
		}
	}
	return f
}

//	if vm.profTracker != nil && !vm.runWithProfiler() {
//		return
//	}
//	count := 0
//	interrupted := false
//	for {
//		if count == 0 {
//			if atomic.LoadInt32(&globalProfiler.enabled) == 1 && !vm.runWithProfiler() {
//				return
//			}
//			count = 100
//		} else {
//			count--
//		}
//		if interrupted = atomic.LoadUint32(&vm.interrupted) != 0; interrupted {
//			break
//		}
//
//		if vm.debugger != nil {
//			if !vm.debugger.active && (vm.debugger.breakpoint() || vm.debugger.next) {
//				if vm.debugger.lastBreakpoint.filename == vm.debugger.Filename() &&
//					vm.debugger.lastBreakpoint.line == vm.debugger.Line() &&
//					vm.debugger.callStackDepth() <= vm.debugger.lastBreakpoint.stackDepth {
//					// Staying on same breakpoint, do nothing.
//				} else {
//					prevStackDepth := vm.debugger.lastBreakpoint.stackDepth
//					vm.debugger.lastBreakpoint.filename = vm.debugger.Filename()
//					vm.debugger.lastBreakpoint.line = vm.debugger.Line()
//					vm.debugger.lastBreakpoint.stackDepth = vm.debugger.callStackDepth()
//					if vm.debugger.lastBreakpoint.stackDepth >= prevStackDepth {
//						vm.debugger.next = false
//						vm.debugger.updateCurrentLine()
//						vm.debugger.activate(BreakpointActivation, vm.debugger.Filename(), vm.debugger.currentLine)
//					}
//
//				}
//			} else {
//				vm.debugger.lastBreakpoint.filename = ""
//				vm.debugger.lastBreakpoint.line = -1
//			}
//			if vm.debugger != nil {
//				vm.debugger.lastBreakpoint.stackDepth = vm.debugger.callStackDepth()
//			}
//		}
//		pc := vm.pc
//		if pc < 0 || pc >= len(vm.prg.code) {
//			break
//		}
//		vm.prg.code[pc].exec(vm)
//	}
//
//	if interrupted {
//		vm.interruptLock.Lock()
//		v := &InterruptedError{
//			iface: vm.interruptVal,
//		}
//		v.stack = vm.captureStack(nil, 0)
//		vm.interruptLock.Unlock()
//		panic(v)
//	}
//}
