package sobek

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

// asyncRunnerDebugMixin adds the savedDebugState field to asyncRunner.
// This is used by the async step state preservation mechanism in async_dbg.go.
// The field is set by onAsyncYield (when an await suspends the generator while
// stepping) and consumed by onAsyncResume (when the promise resolves and
// the generator resumes).
//
// NOTE: This field is added to the asyncRunner struct directly in func.go
// (guarded by a comment explaining the debug purpose) because Go doesn't
// support struct mixins. The actual logic lives in async_dbg.go.
