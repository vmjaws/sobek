package sobek

// runtime_dbg.go — Debug-only Runtime methods.
// Separated from runtime.go to minimize upstream diffs during rebase.

import (
	js_ast "github.com/grafana/sobek/ast"
)

// AttachDebugger will attach and return a Debugger instance to the runtime.
// This will also compile all future scripts directly ran through it in a debug mode until it's detached
// Another way to compile in debug mode is to use CompileASTDebug
// Only 1 debugger can be attached at a time
// This method needs to be called before running any script and to call Continue on the debugger before running a script
// in order to get when it blocks on a debugger statement or breakpoint
// There can only be 1 debugger attached at a time, attaching more is has undefined behaviour
func (r *Runtime) AttachDebugger() *Debugger {
	if r.vm.debugger != nil {
		r.vm.debugMode = true
		r.vm.dbgHooks = newVMDebugHooks(r.vm)
		return r.vm.debugger
	}
	r.vm.debugMode = true
	r.vm.debugger = newDebugger(r.vm)
	r.vm.dbgHooks = newVMDebugHooks(r.vm)
	return r.vm.debugger
}

// GetDebugger returns the attached debugger, or nil if no debugger is attached
func (r *Runtime) GetDebugger() *Debugger {
	return r.vm.debugger
}

// IsDebugMode returns true if the runtime is in debug mode
func (r *Runtime) IsDebugMode() bool {
	return r.vm.debugMode
}

// SetDebugMode enables debug mode on the runtime without attaching a full debugger.
// Used by the throwaway VU 0 in newBundle() which runs debug-compiled code (stash-based
// variable allocation) but doesn't need a DAP server or debugger instance.
// Without this, loadStashLex throws TDZ errors for class declarations because the
// debug-mode TDZ relaxation check (vm.debugMode) is false.
func (r *Runtime) SetDebugMode(enabled bool) {
	r.vm.debugMode = enabled
	if enabled {
		if r.vm.dbgHooks == nil {
			r.vm.dbgHooks = newVMDebugHooks(r.vm)
		}
	} else {
		r.vm.dbgHooks = nil
	}
}

// CompileASTDebug is like CompileAST but enables debug mode when compiling
func CompileASTDebug(prg *js_ast.Program, strict bool) (*Program, error) {
	return compileAST(prg, strict, true, nil, true)
}

// RunStringWithoutDebug executes the given string in the global context without debug mode.
// This is useful for running internal/system code that should not be affected by debug mode settings.
func (r *Runtime) RunStringWithoutDebug(str string) (Value, error) {
	return r.RunScriptWithoutDebug("", str)
}

// RunScriptWithoutDebug executes the given string in the global context without debug mode.
// This compiles the code without debug symbols, even if the runtime is in debug mode.
func (r *Runtime) RunScriptWithoutDebug(name, src string) (Value, error) {
	// Compile without debug mode (pass false explicitly)
	p, err := compile(name, src, false, true, nil, false, r.parserOptions...)
	if err != nil {
		switch x1 := err.(type) {
		case *CompilerSyntaxError:
			err = &Exception{
				val: r.builtin_new(r.getSyntaxError(), []Value{newStringValue(x1.Error())}),
			}
		case *CompilerReferenceError:
			err = &Exception{
				val: r.newError(r.getReferenceError(), x1.Message),
			}
		}
		return nil, err
	}

	return r.RunProgram(p)
}

