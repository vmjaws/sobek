package sobek

// async_dbg.go — Debug support for async/await and Promise-based code.
//
// This file contains all debugger logic for handling async functions, promises,
// and await expressions. Separated from debugger.go to keep async concerns
// isolated and easy to update during rebases.
//
// Key concepts:
//
// 1. ASYNC STEP PRESERVATION: When the user is stepping (stepIn/next) through
//    an async function and execution hits an `await`, the generator suspends.
//    Between the suspension and the promise resolution, other microtasks run
//    in the event loop — if step flags remained set, the debugger would stop
//    at random lines in unrelated code ("steps in into async function randomly").
//
//    Fix: When the debug loop exits due to a yieldMarker (await) while step
//    flags are active, we save the step intent on the asyncRunner and clear
//    the debugger's step flags. When the asyncRunner resumes (onFulfilled/
//    onRejected), the step state is restored. This ensures:
//    a) Intermediate microtasks don't trigger false step pauses
//    b) The debugger pauses at the first line after the await
//    c) This matches Node.js / Chrome DevTools async stepping behavior
//
// 2. PROMISE UNWRAPPING IN VARIABLE DISPLAY: When inspecting variables in the
//    Variables panel or on hover, fulfilled Promises should show their resolved
//    value, not the Promise wrapper. This matches Node.js / Chrome DevTools
//    behavior where `await fn()` shows the resolved result.
//
// 3. GO-BACKED OBJECT INSPECTION: k6 browser module objects are Go-backed
//    (*Object with a Go struct as `self`). The debugger needs to present their
//    properties correctly in the Variables panel and on hover.

import (
	"fmt"
)

// ── Async Step State on asyncRunner ────────────────────────────────────────

// asyncDebugState holds the debugger's step intent that was active when an
// async function hit an await expression. Stored on the asyncRunner itself
// (not a global map) to avoid cross-function interference when multiple
// async functions are pending simultaneously.
type asyncDebugState struct {
	stepIn           bool
	next             bool
	steppingFilename string
	targetDepth      int
	startLine        int
	vuID             uint64
}

// onAsyncYield is called when an async function's generator suspends at an
// await point while the debugger has step flags active. It saves the step
// state on the asyncRunner and clears the debugger's flags so intermediate
// microtasks don't trigger false step pauses.
//
// Called from vm_dbg.go's debug loop exit handler when it detects the exit
// was caused by a yieldMarker (vm.pc < 0) and step flags are active.
func onAsyncYield(v *vm) {
	if v == nil || v.debugger == nil || v.curAsyncRunner == nil {
		return
	}
	dbg := v.debugger
	if !dbg.stepIn && !dbg.next {
		return
	}
	ar := v.curAsyncRunner
	ar.savedDebugState = &asyncDebugState{
		stepIn:           dbg.stepIn,
		next:             dbg.next,
		steppingFilename: dbg.steppingFilename,
		targetDepth:      dbg.stepOverTargetDepth,
		startLine:        dbg.stepOverStartLine,
		vuID:             dbg.vuID,
	}
	// Clear step flags so intermediate microtasks (other promise reactions,
	// event loop jobs) don't trigger false step pauses.
	dbg.stepIn = false
	dbg.next = false
	if debugVM || dbg.enableDebugLogging {
		fmt.Printf("[ASYNC-DBG] onAsyncYield: saved step state on asyncRunner — stepIn=%v, next=%v, file=%s, depth=%d, line=%d, vuID=%d\n",
			ar.savedDebugState.stepIn, ar.savedDebugState.next,
			ar.savedDebugState.steppingFilename, ar.savedDebugState.targetDepth,
			ar.savedDebugState.startLine, ar.savedDebugState.vuID)
	}
}

// onAsyncResume is called when an asyncRunner's onFulfilled or onRejected
// callback is about to enter gen.next(). If step state was saved during
// the yield, it restores it on the debugger so the debug loop pauses at
// the first line after the await.
func onAsyncResume(ar *asyncRunner) {
	if ar == nil || ar.savedDebugState == nil || ar.gen.vm == nil {
		return
	}
	dbg := ar.gen.vm.debugger
	if dbg == nil {
		return
	}
	saved := ar.savedDebugState
	ar.savedDebugState = nil // consume — only restore once
	// Only restore if the debugger doesn't already have step state
	// (the user may have issued a new command while the promise was pending)
	if dbg.stepIn || dbg.next {
		if debugVM || dbg.enableDebugLogging {
			fmt.Printf("[ASYNC-DBG] onAsyncResume: NOT restoring — debugger already has step state (stepIn=%v, next=%v)\n",
				dbg.stepIn, dbg.next)
		}
		return
	}
	dbg.stepIn = saved.stepIn
	dbg.next = saved.next
	dbg.steppingFilename = saved.steppingFilename
	// CRITICAL FIX: When an async function resumes from a promise reaction,
	// the VM call stack is much deeper than when the step was initiated (due to
	// the job queue execution context: runWrapped → try → promiseReactionJob
	// → callJobCallback → onFulfilled → gen.enterNext → pushCtx + context).
	// The saved targetDepth is stale and unusable. If we were doing step-over
	// (next=true), convert to stepIn so the debugger breaks on the next line
	// regardless of call stack depth. This matches Chrome DevTools behavior
	// where stepping over an await always pauses at the next line in the
	// same function.
	if saved.next && !saved.stepIn {
		dbg.stepIn = true
		dbg.next = false
	}
	dbg.stepOverTargetDepth = dbg.callStackDepth()
	dbg.stepOverStartLine = saved.startLine
	// Reset lastBreakpoint.pc so pcAdvanced is true on the first instruction
	// after the await resumes. Without this, the debugger might skip the line.
	dbg.lastBreakpoint.pc = -1
	// Also reset lastBreakpoint.line to the await line so that lineChanged
	// correctly detects the first new line after the await.
	dbg.lastBreakpoint.line = saved.startLine
	// Clear any inherited-position suppression from before the yield.
	// After async resume, try-catch exit bytecodes around the await can
	// trigger the inherited-position heuristic and suppress the break on
	// the very next user line (e.g., line 120 after stepping over line 119).
	dbg.suppressedInheritedLine = 0
	dbg.suppressedInheritedFile = ""
	// Signal the debug loop that we just resumed from an async await.
	// The file-change check should update steppingFilename instead of
	// clearing step flags, because the VM context may not match.
	dbg.asyncResumeActive = true
	if debugVM || dbg.enableDebugLogging {
		fmt.Printf("[ASYNC-DBG] onAsyncResume: restored step state — stepIn=%v, next=%v, file=%s, depth=%d, line=%d\n",
			saved.stepIn, saved.next, saved.steppingFilename, saved.targetDepth, saved.startLine)
	}
}

// ── Promise Unwrapping for Variable Display ────────────────────────────────

// UnwrapPromiseForDisplay checks if a Value is a settled Promise and returns
// an appropriate display value. For fulfilled promises, returns the resolved
// value. For rejected promises, returns the rejection reason wrapped in a
// descriptive string. For pending promises, returns a descriptive string.
// For non-promise values, returns the value unchanged.
//
// This is used by the variable display layer (GetLocalVariables, buildPausedVarSnapshot)
// to show meaningful values instead of opaque Promise objects — matching
// Node.js / Chrome DevTools behavior.
func UnwrapPromiseForDisplay(val Value) Value {
	if val == nil {
		return val
	}
	obj, ok := val.(*Object)
	if !ok {
		return val
	}
	promise, ok := obj.self.(*Promise)
	if !ok {
		return val
	}
	switch promise.State() {
	case PromiseStateFulfilled:
		result := promise.Result()
		if result == nil {
			return _undefined
		}
		return result
	case PromiseStateRejected:
		result := promise.Result()
		if result != nil {
			return asciiString(fmt.Sprintf("Promise <rejected>: %s", result.String()))
		}
		return asciiString("Promise <rejected>")
	default:
		return asciiString("Promise <pending>")
	}
}

// IsPromise returns true if the value is a Promise object.
func IsPromise(val Value) bool {
	if val == nil {
		return false
	}
	obj, ok := val.(*Object)
	if !ok {
		return false
	}
	_, ok = obj.self.(*Promise)
	return ok
}

// PromiseStateString returns a human-readable state of a Promise value.
// Returns "" if the value is not a Promise.
func PromiseStateString(val Value) string {
	if val == nil {
		return ""
	}
	obj, ok := val.(*Object)
	if !ok {
		return ""
	}
	promise, ok := obj.self.(*Promise)
	if !ok {
		return ""
	}
	switch promise.State() {
	case PromiseStateFulfilled:
		return "fulfilled"
	case PromiseStateRejected:
		return "rejected"
	default:
		return "pending"
	}
}

// ── Go-Backed Object Inspection ────────────────────────────────────────────

// IsGoBacked returns true if the value is a Go-backed object (e.g., k6 browser
// module objects like Page, ElementHandle, etc.). These objects have a *Object
// wrapper but their `self` is a Go struct that implements objectImpl.
func IsGoBacked(val Value) bool {
	if val == nil {
		return false
	}
	obj, ok := val.(*Object)
	if !ok {
		return false
	}
	switch obj.self.(type) {
	case *objectGoReflect, *objectGoMapReflect, *objectGoArrayReflect,
		*objectGoSliceReflect:
		return true
	}
	return false
}

// SafeGetObjectKeys returns the enumerable string property keys of an object,
// recovering from any panics that might occur when accessing Go-backed objects.
// This is essential for k6 browser objects where property access can trigger
// Go-side operations that may panic.
func SafeGetObjectKeys(val Value) []string {
	if val == nil {
		return nil
	}
	obj, ok := val.(*Object)
	if !ok {
		return nil
	}
	var keys []string
	func() {
		defer func() {
			if r := recover(); r != nil {
				if debugVM {
					fmt.Printf("[ASYNC-DBG] SafeGetObjectKeys panicked: %v\n", r)
				}
				keys = nil
			}
		}()
		keys = safeStringKeys(obj)
	}()
	return keys
}

// SafeGetProperty safely retrieves a property from an object, recovering from
// panics. Returns nil if the property doesn't exist or access fails.
func SafeGetProperty(val Value, prop string) Value {
	if val == nil {
		return nil
	}
	obj, ok := val.(*Object)
	if !ok {
		return nil
	}
	var result Value
	func() {
		defer func() {
			if r := recover(); r != nil {
				if debugVM {
					fmt.Printf("[ASYNC-DBG] SafeGetProperty(%q) panicked: %v\n", prop, r)
				}
				result = nil
			}
		}()
		result = obj.Get(prop)
	}()
	return result
}

