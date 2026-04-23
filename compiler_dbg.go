package sobek

// compiler_dbg.go — Debug-only compiler types and methods.
// Separated from compiler.go to minimize upstream diffs.

import (
	"fmt"
	"sort"
)

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
	// Normalize the filter filename once so comparisons are consistent.
	filterByFile := filename != ""
	if filterByFile {
		filename = normalizeFilename(filename)
	}
	lastPC := -1
	for i := len(p.srcMap) - 1; i >= 0; i-- {
		entry := p.srcMap[i]
		if entry.pc < startPC {
			break // no need to scan before start
		}
		pos := p.src.Position(entry.srcPos)
		if pos.Line == line {
			// When a filename filter is active, skip entries from other files.
			if filterByFile && pos.Filename != "" {
				if normalizeFilename(pos.Filename) != filename {
					continue
				}
			}
			if entry.pc > lastPC {
				lastPC = entry.pc
			}
		}
	}
	return lastPC
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
			// In debug mode, for block-scoped variables (let/const inside
			// try/catch/for/if), we extend the range to cover the ENTIRE
			// enclosing function — not just the block scope. This matches
			// Chrome DevTools behaviour: all function-local variables are
			// visible at every PC inside the function, regardless of which
			// block they were declared in. Without this, a `let` inside a
			// try block would be invisible at any breakpoint outside it,
			// while a `const` at the function top level would be visible.
			scopeStart := s.base
			scopeEnd := len(s.c.p.code)

			// In debug mode, widen scopeStart to the enclosing function's
			// base so block-scoped bindings are visible everywhere in the
			// function. This is a debugger-only change — runtime semantics
			// are unaffected (the stash walk still determines the actual
			// value availability at runtime).
			if s.c.debug && !s.isFunction() {
				for p := s.outer; p != nil; p = p.outer {
					if p.base < scopeStart {
						scopeStart = p.base
					}
					if p.isFunction() {
						break
					}
				}
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

