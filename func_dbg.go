package sobek

import "strings"

// func_dbg.go — Debug-mode fixes for class function operations.
// Separated from func.go to keep debugger changes isolated.

// prepareInitFieldsDebug is called by _initFields before running the field
// initializer program in debug mode. It resets vm.args to 0 because field
// initializers have no arguments. Without this, the enterFunc instruction
// (emitted by the debug compiler for stash access) computes vm.sb incorrectly
// using the stale vm.args from the outer constructor call, causing
// definePrivateProp to read the wrong stack slot and panic with:
//   "interface conversion: objectImpl is *wrappedFuncObject, not *classFuncObject"
//
// In non-debug mode, enterFunc is not emitted for field initializers (because
// thisBinding is unused and allInStash is false), so vm.args doesn't matter.
func prepareInitFieldsDebug(vm *vm) {
	vm.args = 0
}

// shouldSuppressInitFields returns true when the field-initializer program
// should run with suppressDebugger=true, i.e. the debug loop must NOT
// pause inside it.  This mirrors Node.js "skip node_modules" behaviour:
// any class whose source comes from an external URL (https://) or has no
// source at all (native Go-backed classes like k6 http.Client) is treated
// as library internals and skipped transparently.
//
// Without this guard, tempo's instrumentHTTP class construction causes the
// debug loop to run thousands of instructions through full breakpoint checks
// for every HTTP call, adding ~14s overhead per request in debug mode and
// potentially triggering the "false pause" deadlock described in vm_dbg.go #7.
func shouldSuppressInitFields(initFields *Program) bool {
	if initFields == nil {
		return false
	}
	if initFields.src == nil {
		// No source info — native/generated code, always suppress.
		return true
	}
	name := initFields.src.Name()
	if name == "" {
		return true
	}
	return strings.HasPrefix(name, "https://") || strings.HasPrefix(name, "http://")
}

// shouldSuppressClassConstructDebug returns true when class constructor
// execution should run with suppressDebugger=true in debug mode.
//
// This targets constructors with no user-source body (prg==nil or src=nil)
// and external URL constructors (tempo/httpx jslib). Node.js debuggers
// treat these as library/native internals and do not step through them.
func shouldSuppressClassConstructDebug(prg *Program) bool {
	if prg == nil || prg.src == nil {
		return true
	}
	name := prg.src.Name()
	if name == "" {
		return true
	}
	return strings.HasPrefix(name, "https://") || strings.HasPrefix(name, "http://")
}

// asyncRunnerDebugMixin adds the savedDebugState field to asyncRunner.
// This is used by the async step state preservation mechanism in async_dbg.go.
// The field is set by onAsyncYield (when an await suspends the generator while
// stepping) and consumed by onAsyncResume (when the promise resolves and
// the generator resumes).
//
// NOTE: This field is added to the asyncRunner struct directly in func.go
// (guarded by a comment explaining the debug purpose) because Go doesn't
// support struct mixins. The actual logic lives in async_dbg.go.
