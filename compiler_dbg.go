package sobek

// compiler_dbg.go — Debug-only compiler types and methods.
// Separated from compiler.go to minimize upstream diffs.

import (
	"fmt"
	"sort"
)

// debugScopeEndPCs tracks the ending PC for each scope during compilation.
// Only populated in debug mode (via markScopeEndPC called from popScope).
// Used by collectAllDebugSymbols to produce accurate PC ranges for
// block-scoped variables, preventing them from appearing at PCs where
// their stash has been popped by leaveBlock.

// markScopeEndPC records the current code length as the ending PC for
// the scope being popped. Called from popScope when c.debug is true.
func (c *compiler) markScopeEndPC() {
	if c.debugScopeEndPCs == nil {
		c.debugScopeEndPCs = make(map[*scope]int)
	}
	if _, exists := c.debugScopeEndPCs[c.scope]; !exists {
		c.debugScopeEndPCs[c.scope] = len(c.p.code)
	}
}

// getScopeEndPC returns the ending PC for a scope, or 0 if not recorded.
func (s *scope) getScopeEndPC() int {
	if s.c == nil || s.c.debugScopeEndPCs == nil {
		return 0
	}
	return s.c.debugScopeEndPCs[s]
}

type DebugSymbols struct {
	// Range-based variable scope storage. Each entry covers a [StartPC, EndPC]
	// range with its visible variables. Sorted by StartPC for binary search.
	// This replaces the per-PC map which had O(N*M) memory (one entry per
	// instruction per variable) causing OOM with 20+ bundled files.
	ranges []PCRange
	sorted bool // true after ranges have been sorted

	// Map line number to PCs
	lineToPCs map[int][]int
}

// PCRange maps a contiguous range of PCs to the variables visible within it.
type PCRange struct {
	StartPC, EndPC int
	Vars           []VarLocation
}

// LookupVarsAtPC returns all variables visible at the given PC.
func (ds *DebugSymbols) LookupVarsAtPC(pc int) []VarLocation {
	if ds == nil || len(ds.ranges) == 0 {
		return nil
	}
	// Sort on first access
	if !ds.sorted {
		sort.Slice(ds.ranges, func(i, j int) bool {
			return ds.ranges[i].StartPC < ds.ranges[j].StartPC
		})
		ds.sorted = true
	}
	// Collect all ranges that contain this PC.
	// Ranges can overlap (nested scopes), so we scan all matches.
	var result []VarLocation
	for i := range ds.ranges {
		r := &ds.ranges[i]
		if r.StartPC > pc {
			break // sorted by StartPC — no more ranges can start before pc
		}
		if pc <= r.EndPC {
			result = append(result, r.Vars...)
		}
	}
	return result
}

type VarLocation struct {
	Name       string
	InStash    bool
	StashIdx   uint32 // if InStash=true, the stash index within that stash level
	StackIdx   int    // if InStash=false, the stack index
	StashLevel int    // 0 = innermost (current) stash, 1 = parent stash, etc.
	IsParam    bool
	IsConst    bool
	StartPC    int // PC where variable becomes available
	EndPC      int // PC where variable goes out of scope
}


func (p *Program) addStmtPC() {
	pc := len(p.code)
	if len(p.stmtPCs) > 0 && p.stmtPCs[len(p.stmtPCs)-1] == pc {
		return
	}
	p.stmtPCs = append(p.stmtPCs, pc)
}

// isStatementStart returns true if pc corresponds to the beginning of a
// statement (as opposed to a sub-expression like an argument evaluation).
// Used by the debugger during step-in/step-over to skip argument evaluation
// in multi-line call expressions. Returns true when stmtPCs is empty
// (non-debug mode or very old programs) to preserve backward compatibility.
func (p *Program) isStatementStart(pc int) bool {
	if len(p.stmtPCs) == 0 {
		return true // no data — treat every PC as a potential break point
	}
	idx := sort.SearchInts(p.stmtPCs, pc)
	return idx < len(p.stmtPCs) && p.stmtPCs[idx] == pc
}

// lastPCForLine scans the program's srcMap and returns the LAST PC whose
// source-mapped line equals the given line, with pc >= startPC.
// When filename is non-empty, only PCs whose source-mapped filename matches
// are considered. This prevents cross-file line-number collisions in bundled
// TypeScript (where a single *Program contains bytecodes from multiple
// original .ts files via source maps) from inflating the PC range.
// Used by the sub-expression skip in step-over/step-in to find the end of
// a multi-line expression (e.g., a function call whose arguments span
// multiple source lines). The caller must combine this with a backward-jump
// check (currentPC > lastExecPC) to avoid skipping loop bodies that sit
// between two occurrences of the same source line.
// Returns -1 if no match is found.
func (p *Program) lastPCForLine(line int, startPC int, filename string) int {
	if p.src == nil || len(p.srcMap) == 0 {
		return -1
	}
	if startPC < 0 {
		startPC = 0
	}
	// Normalize the filter filename once so comparisons are consistent.
	filterByFile := filename != ""
	if filterByFile {
		filename = normalizeFilename(filename)
	}

	// Find the srcMap index corresponding to startPC (or the first entry after it).
	startIdx := -1
	for i, entry := range p.srcMap {
		if entry.pc >= startPC {
			startIdx = i
			break
		}
	}
	if startIdx < 0 {
		return -1
	}

	// Scan forward from startPC. When we encounter a gap (entries on different
	// source lines between two occurrences of the target line), we must decide
	// whether to continue past the gap or stop:
	//
	//   LOOP PATTERNS (stop at the gap):
	//   • for(init; test; update): init+test → jneP(forward) → body → update → jump(backward)
	//   • while(test):             test → jneP(forward) → body → jump(backward)
	//   • for(init; ; update):     init → body → update → jump(backward)  [no test]
	//   • while(true):             body → jump(backward)                  [const test]
	//   Detection: (a) conditional forward jump in the first block, OR
	//              (b) backward unconditional jump in the second block after the gap.
	//
	//   MULTI-LINE CALL (continue past the gap):
	//   • foo(\n arg1,\n arg2\n):  load_foo → args → call_foo
	//   No conditional forward jump in first block, no backward jump in second block.
	//
	//   DO-WHILE: condition line appears only once (at the bottom), no gap issue.
	//
	lastPC := -1
	sawMatch := false  // true once we've seen at least one target-line entry
	inGap := false     // true while scanning entries on different lines after a block
	gapHasLoopHeader := false // first block ends with conditional forward jump

	for i := startIdx; i < len(p.srcMap); i++ {
		entry := p.srcMap[i]
		pos := p.src.Position(entry.srcPos)

		// Skip entries from other files when filtering.
		if filterByFile && pos.Filename != "" {
			if normalizeFilename(pos.Filename) != filename {
				continue
			}
		}

		if pos.Line == line {
			if inGap {
				// We're seeing the target line again after a gap.
				// CASE 1: The first block had a conditional forward jump → loop header, stop.
				if gapHasLoopHeader {
					break
				}
				// CASE 2: Check if this second block contains a backward jump.
				// Peek ahead through the remaining entries on the target line.
				if p.hasBackwardJumpInBlock(i, line, filterByFile, filename) {
					break
				}
				// CASE 3: No loop signals → multi-line expression, continue.
				inGap = false
			}
			sawMatch = true
			if entry.pc > lastPC {
				lastPC = entry.pc
			}
		} else if sawMatch && !inGap {
			// First entry on a different line after a contiguous block.
			inGap = true
			gapStartPC := entry.pc
			gapHasLoopHeader = p.hasConditionalForwardJumpInRange(startPC, gapStartPC-1)
			if gapHasLoopHeader {
				break // early exit — no need to scan the gap
			}
		}
	}
	return lastPC
}

// hasConditionalForwardJumpInRange checks whether any instruction in
// [fromPC, toPC] is a conditional jump with a positive (forward) offset.
// This is the signature of a loop header: the condition test emits
// a conditional forward jump to skip the loop body when the test is false.
// Also detects enumNext/iterNext (for-in/for-of loop headers) which jump
// forward when the iterator is exhausted.
func (p *Program) hasConditionalForwardJumpInRange(fromPC, toPC int) bool {
	if fromPC < 0 {
		fromPC = 0
	}
	for pc := fromPC; pc <= toPC && pc < len(p.code); pc++ {
		switch j := p.code[pc].(type) {
		case jneP:
			if int32(j) > 0 {
				return true
			}
		case jeqP:
			if int32(j) > 0 {
				return true
			}
		case jne:
			if int32(j) > 0 {
				return true
			}
		case jeq:
			if int32(j) > 0 {
				return true
			}
		case enumNext:
			// for-in loop header: jumps forward when enumerator is exhausted
			if int32(j) > 0 {
				return true
			}
		case iterNext:
			// for-of loop header: jumps forward when iterator is done
			if int32(j) > 0 {
				return true
			}
		}
	}
	return false
}

// hasBackwardJumpInBlock checks whether any srcMap entry starting at index
// startIdx that maps to the given target line has a backward unconditional
// jump instruction. This detects loop back-edges in constructs like
// for(;;) and while(true) where no conditional forward jump exists.
func (p *Program) hasBackwardJumpInBlock(startIdx int, targetLine int, filterByFile bool, filename string) bool {
	for i := startIdx; i < len(p.srcMap); i++ {
		entry := p.srcMap[i]
		pos := p.src.Position(entry.srcPos)
		if filterByFile && pos.Filename != "" {
			if normalizeFilename(pos.Filename) != filename {
				continue
			}
		}
		if pos.Line != targetLine {
			break // left the block
		}
		if entry.pc >= 0 && entry.pc < len(p.code) {
			if j, ok := p.code[entry.pc].(jump); ok && int32(j) < 0 {
				return true
			}
		}
	}
	return false
}

// hasBackwardJumpBetween scans all bytecodes in [fromPC, toPC] and returns
// true if any instruction is a backward jump (unconditional or conditional
// with a negative offset). This detects loop bodies: the backward jump at
// the end of a for/while loop is the loop's back-edge. If the range
// [fromPC, toPC] contains such a jump, the range spans a loop body and
// should NOT be used for the sub-expression skip.
func (p *Program) hasBackwardJumpBetween(fromPC, toPC int) bool {
	if fromPC < 0 {
		fromPC = 0
	}
	if toPC >= len(p.code) {
		toPC = len(p.code) - 1
	}
	for pc := fromPC; pc <= toPC; pc++ {
		switch j := p.code[pc].(type) {
		case jump:
			if int32(j) < 0 {
				return true
			}
		case jneP:
			if int32(j) < 0 {
				return true
			}
		case jeqP:
			if int32(j) < 0 {
				return true
			}
		case jne:
			if int32(j) < 0 {
				return true
			}
		case jeq:
			if int32(j) < 0 {
				return true
			}
		}
	}
	return false
}


func (s *scope) collectAllDebugSymbols(stackOffset, finalStashIdx, finalStackIdx int) {
	if s.c.p.debugSymbols == nil {
		return
	}

	stashIdx := 0
	stackIdx := 0

	// Compute the stash nesting level of THIS scope relative to the enclosing
	// function. The function scope itself is level 0. Each stash-creating block
	// scope inside the function increments the level by 1.
	// At runtime, vm.stash is the innermost; getValueFromLocation uses this to
	// compute how many .outer hops are needed.
	stashLevel := 0
	if !s.isFunction() {
		// Count all stash-creating scopes from our parent up to (not including)
		// the function scope, then add 1 for ourselves.
		for p := s.outer; p != nil && !p.isFunction(); p = p.outer {
			if p.needStash || p.isDynamic() || (p.c != nil && p.c.debug && len(p.bindings) > 0) {
				stashLevel++
			}
		}
		// The current scope itself is one level deeper than whatever we counted.
		if s.needStash || s.isDynamic() || (s.c != nil && s.c.debug && len(s.bindings) > 0) {
			stashLevel++
		}
	}
	// stashLevel=0 for the function scope, 1 for try/catch/block directly in function, etc.

	// First, let's see ALL bindings to understand the mismatch
	if debugCompiler {
		fmt.Printf("[COMPILER-DEBUG] collectAllDebugSymbols: Processing %d bindings (stashLevel=%d)\n", len(s.bindings), stashLevel)
		for i, b := range s.bindings {
			fmt.Printf("[COMPILER-DEBUG]   Binding[%d]: name=%s, inStash=%v, isArg=%v\n", i, b.name, b.inStash, b.isArg)
		}
	}

	// CRITICAL: Use the SAME logic as the main allocation loop to determine if binding goes in stash
	allInStash := s.isDynamic() || s.c.debug

	for i, b := range s.bindings {
		// Check if this is the 'this' binding
		isThisBinding := b.name == thisBindingName

		// CRITICAL: Use the SAME logic as main loop: allInStash || b.inStash
		bindingInStash := allInStash || b.inStash

		// Create debug symbols for all bindings, including 'this'.
		// For 'this' bindings (stored as " this" with leading space), use
		// display name "this" so the IDE locals panel shows it correctly.
		{
			displayName := b.name.String()
			if isThisBinding {
				displayName = "this"
			}
			varLoc := VarLocation{
				Name:       displayName,
				InStash:    bindingInStash,
				IsParam:    b.isArg,
				IsConst:    b.isConst,
				StashLevel: stashLevel,
			}

			if bindingInStash {
				// Variable is in stash
				varLoc.StashIdx = uint32(stashIdx)
			} else {
				// Variable is on stack
				if b.isArg {
					varLoc.StackIdx = -(i + 1)
				} else {
					varLoc.StackIdx = stackOffset + stackIdx
				}
			}

			// Find PC range where this variable is accessible.
			//
			// Use the ACTUAL scope boundaries: [s.base, s.endPC).
			// For function scopes, endPC defaults to len(code) (set by
			// popScope or fallback below), covering the entire function.
			// For block scopes (for/try/if/catch), endPC is set by
			// popScope to the PC where leaveBlock pops the stash.
			//
			// Previously, block-scope ranges were widened to the entire
			// enclosing function "to match Chrome DevTools". But this
			// caused variables from inactive block scopes (popped by
			// leaveBlock) to appear in LookupVarsAtPC, then FAIL in
			// getValueFromLocation because their stash no longer exists.
			// The stash-chain fallback then found the variables were
			// truly gone and left them as _undefined — polluting the
			// locals panel with dozens of false entries and hiding the
			// variables the user actually cares about.
			//
			// With accurate ranges:
			// - Block-scoped variables (let/const in for/try/if) are
			//   visible only when their block stash is active.
			// - Function-scoped variables remain visible everywhere in
			//   the function (their scope naturally spans the whole fn).
			// - The stash-chain fallback still picks up any named
			//   variables from outer scopes that debug symbols miss.
			scopeStart := s.base
			scopeEnd := s.getScopeEndPC()
			if scopeEnd == 0 {
				scopeEnd = len(s.c.p.code) // fallback for function scopes
			}

			minPC := scopeEnd
			maxPC := scopeStart

			// Narrow down based on access points if available
			for scope, aps := range b.accessPoints {
				for _, pc := range *aps {
					absolutePC := scope.base + pc
					if absolutePC < minPC {
						minPC = absolutePC
					}
					if absolutePC > maxPC {
						maxPC = absolutePC
					}
				}
			}

			// Extend to cover the full (possibly widened) scope range.
			if minPC > maxPC || minPC >= scopeEnd {
				minPC = scopeStart
				maxPC = scopeEnd - 1
			} else {
				if scopeStart < minPC {
					minPC = scopeStart
				}
				if maxPC < scopeEnd-1 {
					maxPC = scopeEnd - 1
				}
			}

			varLoc.StartPC = minPC
			varLoc.EndPC = maxPC

			// Add as a range entry — one entry per variable instead of one per PC.
			// This is O(variables) instead of O(instructions * variables), preventing
			// OOM with bundled 20+ file projects.
			s.c.p.debugSymbols.ranges = append(s.c.p.debugSymbols.ranges, PCRange{
				StartPC: minPC,
				EndPC:   maxPC,
				Vars:    []VarLocation{varLoc},
			})

			if debugCompiler {
				fmt.Printf("[COMPILER-DEBUG]   Debug symbol: %s, inStash=%v, stashIdx=%d, stackIdx=%d, stashLevel=%d, PC range=[%d-%d]\n",
					varLoc.Name, varLoc.InStash, varLoc.StashIdx, varLoc.StackIdx, varLoc.StashLevel, minPC, maxPC)
			}
		}

		// Mirror finaliseVarAlloc counter increments exactly — including 'this'
		if bindingInStash {
			stashIdx++
		} else {
			if !isThisBinding && !b.isArg {
				stackIdx++
			}
		}
	}
}

