package sobek

import "github.com/grafana/sobek/unistring"

// vm_debug_hooks.go — Debug hook interface for the VM.
//
// This file defines the debugHooks interface that the VM uses to dispatch
// debug-related behavior. When vm.dbgHooks is nil (the default), no debug
// code runs — all call sites use a simple nil check. When a debugger is
// attached, vm.dbgHooks is set to an implementation that provides the
// actual debug behavior.
//
// This keeps the original vm.go nearly identical to upstream: the only
// changes are the `dbgHooks` field on the vm struct and single-line nil
// checks at each hook call site.

// debugHooks defines the interface for debug behavior injected into the VM.
// Each method corresponds to a category of inline debug checks that were
// previously scattered throughout vm.go.
type debugHooks interface {
	// --- Execution loop ---

	// runDebug is called instead of vm.run() when debug mode is active.
	// It implements the debug-aware execution loop (breakpoints, stepping, etc.)
	runDebug()

	// --- Stash safety (TDZ relaxation) ---

	// stashGetSafe returns the value at idx, or _undefined if out of bounds.
	// In non-debug mode, out-of-bounds returns nil (causing TDZ panic).
	stashGetSafe(s *stash, idx uint32) (Value, bool)

	// stashInitGrow grows the stash values slice if idx is out of bounds.
	stashInitGrow(s *stash, idx uint32)

	// stashGetByNameRelaxed returns _undefined for uninitialized variables
	// instead of panicking with errAccessBeforeInit.
	stashGetByNameRelaxed(s *stash, idx uint32) Value

	// stashRefLexRelaxed returns _undefined instead of panicking for
	// uninitialized lexical bindings accessed via ref.
	stashRefLexRelaxed() Value

	// loadStashLexRelaxed returns _undefined instead of throwing TDZ error
	// for uninitialized stash bindings in debug mode. In debug mode,
	// allInStash=true forces all variables to stash. Their slots start as nil,
	// which loadStashLex/loadMixedLex interprets as TDZ. But these variables
	// work fine in non-debug mode (stack slots are always initialized).
	// The compiler fix (loadStackLex → loadStash) handles most cases, but
	// class field initializers (#privateFields) and module-level bindings
	// are compiled in separate programs where the compiler fix doesn't apply.
	loadStashLexRelaxed() Value

	// --- Names map copy (prevents shared mutation) ---

	// copyNamesMap returns a copy of the names map instead of sharing it.
	// In debug mode, names maps must be copied because the debugger may
	// mutate them (e.g., adding variables).
	copyNamesMap(names map[unistring.String]uint32) map[unistring.String]uint32

	// --- This binding copy ---

	// copyThisToStash copies 'this' from the stack to the stash slot.
	// In debug mode, allInStash=true moves 'this' to stash, but enterFunc
	// doesn't know about it — this hook fills the gap.
	copyThisToStash(vm *vm, stash *stash, names map[unistring.String]uint32)

	// --- Exception handling ---

	// onThrowCaptureState captures throw-site location and stash before unwind.
	onThrowCaptureState(vm *vm, ex *Exception)

	// onCaughtException is called when an exception is caught by a try/catch.
	onCaughtException(vm *vm, ex *Exception, throwFile string, throwLine int)

	// onUncaughtException is called when an exception escapes (no catch).
	onUncaughtException(vm *vm, ex *Exception)

	// onRunTryInnerException is called from runTryInner's defer/recover.
	onRunTryInnerException(vm *vm, ex *Exception)

	// --- Debugger statement ---

	// onDebuggerStatement is called when the JS `debugger;` statement executes.
	onDebuggerStatement(vm *vm)

	// --- Call diagnostics ---

	// onCallNonFunction is called when attempting to call a non-callable object.
	onCallNonFunction(vm *vm, obj *Object, numargs int)

	// needStash returns true if an empty scope still needs a stash in debug mode.
	needStash() bool
}

