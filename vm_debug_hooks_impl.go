package sobek

// vm_debug_hooks_impl.go — Concrete implementation of debugHooks.
// This file implements all the debug hooks that vm.go dispatches to.
// When a debugger is attached, vm.dbgHooks is set to a *vmDebugHooksImpl.

import (
	"fmt"

	"github.com/grafana/sobek/unistring"
)

// vmDebugHooksImpl implements debugHooks for an attached debugger.
type vmDebugHooksImpl struct {
	vm *vm
}

func newVMDebugHooks(v *vm) *vmDebugHooksImpl {
	return &vmDebugHooksImpl{vm: v}
}

// --- Execution loop ---

func (h *vmDebugHooksImpl) runDebug() {
	h.vm.debug()
}

// --- Stash safety ---

func (h *vmDebugHooksImpl) stashGetSafe(s *stash, idx uint32) (Value, bool) {
	if int(idx) >= len(s.values) {
		return _undefined, true
	}
	return nil, false
}

func (h *vmDebugHooksImpl) stashInitGrow(s *stash, idx uint32) {
	if int(idx) >= len(s.values) {
		needed := int(idx) + 1
		extra := make([]Value, needed-len(s.values))
		s.values = append(s.values, extra...)
	}
}

func (h *vmDebugHooksImpl) stashGetByNameRelaxed(s *stash, idx uint32) Value {
	return _undefined
}

func (h *vmDebugHooksImpl) stashRefLexRelaxed() Value {
	return _undefined
}

// --- Names map copy ---

func (h *vmDebugHooksImpl) copyNamesMap(names map[unistring.String]uint32) map[unistring.String]uint32 {
	m := make(map[unistring.String]uint32, len(names))
	for k, v := range names {
		m[k] = v
	}
	return m
}

// --- This binding copy ---

func (h *vmDebugHooksImpl) copyThisToStash(vm *vm, stash *stash, names map[unistring.String]uint32) {
	if names == nil {
		return
	}
	if thisIdx, ok := names[unistring.String(thisBindingName)]; ok {
		idx := thisIdx & 0x00FFFFFF
		if int(idx) < len(stash.values) && stash.values[idx] == nil {
			stash.initByIdx(idx, vm.stack[vm.sb])
		}
	}
}

// --- Exception handling ---

func (h *vmDebugHooksImpl) onThrowCaptureState(vm *vm, ex *Exception) {
	if ex == nil || len(ex.stack) == 0 {
		return
	}
	frame := &ex.stack[0]
	pos := frame.Position()
	throwFile := normalizeFilename(pos.Filename)
	_ = pos.Line // throwLine used by caller
	if throwFile == "" && vm.prg != nil && vm.prg.src != nil {
		pos = vm.prg.src.Position(vm.prg.sourceOffset(vm.pc))
		_ = normalizeFilename(pos.Filename)
	}
	vm.debugger.exceptionStash = vm.stash
	vm.debugger.exceptionSB = vm.sb
	vm.debugger.exceptionPrg = vm.prg
}

func (h *vmDebugHooksImpl) onCaughtException(vm *vm, ex *Exception, throwFile string, throwLine int) {
	if vm.debugger == nil || ex == nil || vm.debugger.inEvalContext {
		return
	}
	currentFile := ""
	if vm.prg != nil && vm.prg.src != nil {
		currentFile = vm.prg.src.Name()
	}
	if currentFile != "<debugger-eval>" {
		vm.debugger.BreakOnException(ex.val, true, throwFile, throwLine)
	}
}

func (h *vmDebugHooksImpl) onUncaughtException(vm *vm, ex *Exception) {
	if vm.debugger == nil || vm.debugger.inEvalContext {
		return
	}
	currentFile := ""
	if vm.prg != nil && vm.prg.src != nil {
		currentFile = vm.prg.src.Name()
	}
	if currentFile != "<debugger-eval>" {
		vm.debugger.SetLastExceptionStack(ex.stack)
		var throwFile string
		var throwLine int
		if len(ex.stack) > 0 {
			pos := ex.stack[0].Position()
			throwFile = normalizeFilename(pos.Filename)
			throwLine = pos.Line
		}
		if debugActivate {
			fmt.Printf("[EXCEPTION-TRACE] vm.throw: calling BreakOnException from throw(), throwFile=%s, throwLine=%d, exception=%q\n",
				throwFile, throwLine, ex.val.String())
		}
		vm.debugger.BreakOnException(ex.val, false, throwFile, throwLine)
		if debugActivate {
			fmt.Printf("[EXCEPTION-TRACE] vm.throw: BreakOnException returned, about to panic\n")
		}
	}
}

func (h *vmDebugHooksImpl) onRunTryInnerException(vm *vm, ex *Exception) {
	if vm.debugger == nil {
		return
	}
	if len(ex.stack) > 0 {
		vm.debugger.SetLastExceptionStack(ex.stack)
	}
	if debugActivate {
		fmt.Printf("[EXCEPTION-TRACE] runTryInner defer: recovered exception=%q, pendingUncaughtException=%v, inEvalContext=%v\n",
			ex.val.String(), vm.debugger.pendingUncaughtException != nil, vm.debugger.inEvalContext)
	}

	if !vm.debugger.inEvalContext && vm.debugger.pendingUncaughtException == nil {
		var throwFile string
		var throwLine int
		if len(ex.stack) > 0 {
			pos := ex.stack[0].Position()
			throwFile = normalizeFilename(pos.Filename)
			throwLine = pos.Line
		}
		if debugActivate {
			fmt.Printf("[EXCEPTION-TRACE] runTryInner defer: calling BreakOnException (no pending yet, throwFile=%s, throwLine=%d)\n",
				throwFile, throwLine)
		}
		vm.debugger.BreakOnException(ex.val, false, throwFile, throwLine)
	} else if debugActivate {
		fmt.Printf("[EXCEPTION-TRACE] runTryInner defer: SKIPPED BreakOnException (pending=%v, inEval=%v)\n",
			vm.debugger.pendingUncaughtException != nil, vm.debugger.inEvalContext)
	}

	vm.debugger.uncaughtExceptionExit = !vm.debugger.inEvalContext

	if debugActivate {
		fmt.Printf("[EXCEPTION-TRACE] runTryInner defer: closing vmDoneCh, vmExited=true\n")
	}
	if !vm.debugger.inEvalContext {
		vm.debugger.vmExited = true
		if vm.debugger.vmDoneCh != nil {
			select {
			case <-vm.debugger.vmDoneCh:
			default:
				close(vm.debugger.vmDoneCh)
			}
		}
		vm.debugger.next = false
		vm.debugger.stepIn = false
		GetGlobalCoordinator().ClearGlobalStepState()
		if GetGlobalCoordinator().IsMultiVUDebug() {
			GetGlobalCoordinator().ClearVUStepState(vm.debugger.vuID)
		}
	} else if debugActivate {
		fmt.Printf("[EXCEPTION-TRACE] runTryInner defer: SKIPPED vmExited/vmDoneCh (inEvalContext=true)\n")
	}

	if !vm.debugger.inEvalContext && vm.debugger.exceptionWaitCh != nil {
		if debugActivate {
			fmt.Printf("[EXCEPTION-TRACE] runTryInner defer: BLOCKING on exceptionWaitCh — waiting for IDE user to dismiss\n")
		}
		<-vm.debugger.exceptionWaitCh
		if debugActivate {
			fmt.Printf("[EXCEPTION-TRACE] runTryInner defer: exceptionWaitCh RELEASED — VM continuing exit\n")
		}
	} else if debugActivate {
		fmt.Printf("[EXCEPTION-TRACE] runTryInner defer: exceptionWaitCh is nil — NOT blocking (breakOnUncaughtExceptions likely disabled)\n")
	}
}

// --- Debugger statement ---

func (h *vmDebugHooksImpl) onDebuggerStatement(vm *vm) {
	if vm.debugger != nil && !vm.debugger.active {
		vm.debugger.activate(DebuggerStatementActivation, vm.debugger.Filename(), vm.debugger.Line())
	}
}

// --- Call diagnostics ---

func (h *vmDebugHooksImpl) onCallNonFunction(vm *vm, obj *Object, numargs int) {
	if _, ok := obj.self.assertCallable(); !ok {
		posFile := ""
		posLine := 0
		if vm.prg != nil && vm.prg.src != nil {
			pos := vm.prg.src.Position(vm.prg.sourceOffset(vm.pc))
			posFile = pos.Filename
			posLine = pos.Line
		}
		if debugVM {
			fmt.Printf("[CALL-DEBUG] About to call non-function: %s (%T) at %s:%d (pc=%d, numargs=%d)\n",
				obj.String(), obj.self, posFile, posLine, vm.pc, numargs)
		}
		if vm.prg != nil {
			start := vm.pc - 5
			if start < 0 {
				start = 0
			}
			end := vm.pc + 3
			if end > len(vm.prg.code) {
				end = len(vm.prg.code)
			}
			for i := start; i < end; i++ {
				marker := "  "
				if i == vm.pc {
					marker = ">>"
				}
				if debugVM {
					fmt.Printf("[CALL-DEBUG] %s [PC=%d] %T\n", marker, i, vm.prg.code[i])
				}
			}
		}
	}
}

func (h *vmDebugHooksImpl) needStash() bool {
	return true
}

