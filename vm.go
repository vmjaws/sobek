package sobek

import (
	"fmt"
	"math"
	"math/big"
	"os"
	"reflect"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/grafana/sobek/unistring"
)

// Debug logging control via environment variables (same as debugger.go)
var vmDebugEnabled = os.Getenv("SOBEK_DEBUG_VM") == "1" || os.Getenv("SOBEK_DEBUG_ALL") == "1"

const (
	maxInt = 1 << 53

	tryPanicMarker = -2
)

type valueStack []Value

type stash struct {
	values    []Value
	extraArgs []Value
	names     map[unistring.String]uint32
	obj       *Object

	outer *stash
	vm    *vm

	// If this is a top-level function stash, sets the type of the function. If set, dynamic var declarations
	// created by direct eval go here.
	funcType funcType
}

type context struct {
	prg       *Program
	stash     *stash
	privEnv   *privateEnv
	newTarget Value
	result    Value
	pc, sb    int
	args      int
}

type tryFrame struct {
	// holds an uncaught exception for the 'finally' block
	exception *Exception

	callStackLen, iterLen, refLen uint32

	sp      int32
	stash   *stash
	privEnv *privateEnv

	catchPos, finallyPos, finallyRet int32
}

type execCtx struct {
	context
	stack     []Value
	tryStack  []tryFrame
	iterStack []iterStackItem
	refStack  []ref
}

func (vm *vm) suspend(ectx *execCtx, tryStackLen, iterStackLen, refStackLen uint32) {
	vm.saveCtx(&ectx.context)
	ectx.stack = append(ectx.stack[:0], vm.stack[vm.sb-1:vm.sp]...)
	if len(vm.tryStack) > int(tryStackLen) {
		ectx.tryStack = append(ectx.tryStack[:0], vm.tryStack[tryStackLen:]...)
		vm.tryStack = vm.tryStack[:tryStackLen]
		sp := int32(vm.sb - 1)
		for i := range ectx.tryStack {
			tf := &ectx.tryStack[i]
			tf.iterLen -= iterStackLen
			tf.refLen -= refStackLen
			tf.sp -= sp
		}
	}
	if len(vm.iterStack) > int(iterStackLen) {
		ectx.iterStack = append(ectx.iterStack[:0], vm.iterStack[iterStackLen:]...)
		vm.iterStack = vm.iterStack[:iterStackLen]
	}
	if len(vm.refStack) > int(refStackLen) {
		ectx.refStack = append(ectx.refStack[:0], vm.refStack[refStackLen:]...)
		vm.refStack = vm.refStack[:refStackLen]
	}
}

func (vm *vm) resume(ctx *execCtx) {
	vm.restoreCtx(&ctx.context)
	sp := vm.sp
	vm.sb = sp + 1
	vm.stack.expand(sp + len(ctx.stack))
	copy(vm.stack[sp:], ctx.stack)
	vm.sp += len(ctx.stack)
	for i := range ctx.tryStack {
		tf := &ctx.tryStack[i]
		tf.callStackLen = uint32(len(vm.callStack))
		tf.iterLen += uint32(len(vm.iterStack))
		tf.refLen += uint32(len(vm.refStack))
		tf.sp += int32(sp)
	}
	vm.tryStack = append(vm.tryStack, ctx.tryStack...)
	vm.iterStack = append(vm.iterStack, ctx.iterStack...)
	vm.refStack = append(vm.refStack, ctx.refStack...)
}

type iterStackItem struct {
	val  Value
	f    iterNextFunc
	iter *iteratorRecord
}

type ref interface {
	get() Value
	set(Value)
	init(Value)
	refname() unistring.String
}

type stashRef struct {
	n   unistring.String
	v   *[]Value
	idx int
	vm  *vm
}

func (r *stashRef) get() Value {
	return nilSafe((*r.v)[r.idx])
}

func (r *stashRef) set(v Value) {
	(*r.v)[r.idx] = v
}

func (r *stashRef) init(v Value) {
	r.set(v)
}

func (r *stashRef) refname() unistring.String {
	return r.n
}

type thisRef struct {
	v   *[]Value
	idx int
}

func (r *thisRef) get() Value {
	v := (*r.v)[r.idx]
	if v == nil {
		panic(referenceError("Must call super constructor in derived class before accessing 'this'"))
	}

	return v
}

func (r *thisRef) set(v Value) {
	ptr := &(*r.v)[r.idx]
	if *ptr != nil {
		panic(referenceError("Super constructor may only be called once"))
	}
	*ptr = v
}

func (r *thisRef) init(v Value) {
	r.set(v)
}

func (r *thisRef) refname() unistring.String {
	return thisBindingName
}

type stashRefLex struct {
	stashRef
}

func (r *stashRefLex) get() Value {
	v := (*r.v)[r.idx]
	if v == nil {
		if r.vm != nil && r.vm.debugger != nil {
			return _undefined
		}
		panic(errAccessBeforeInit)
	}
	return v
}

func (r *stashRefLex) set(v Value) {
	p := &(*r.v)[r.idx]
	if *p == nil {
		panic(errAccessBeforeInit)
	}
	*p = v
}

func (r *stashRefLex) init(v Value) {
	(*r.v)[r.idx] = v
}

type stashRefConst struct {
	stashRefLex
	strictConst bool
}

func (r *stashRefConst) set(v Value) {
	if r.strictConst {
		panic(errAssignToConst)
	}
}

type objRef struct {
	base   *Object
	name   Value
	this   Value
	strict bool

	nameConverted bool
}

func (r *objRef) getKey() Value {
	if !r.nameConverted {
		r.name = toPropertyKey(r.name)
		r.nameConverted = true
	}
	return r.name
}

func (r *objRef) get() Value {
	return r.base.get(r.getKey(), r.this)
}

func (r *objRef) set(v Value) {
	key := r.getKey()
	if r.this != nil {
		r.base.set(key, v, r.this, r.strict)
	} else {
		r.base.setOwn(key, v, r.strict)
	}
}

func (r *objRef) init(v Value) {
	if r.this != nil {
		r.base.set(r.getKey(), v, r.this, r.strict)
	} else {
		r.base.setOwn(r.getKey(), v, r.strict)
	}
}

func (r *objRef) refname() unistring.String {
	return r.getKey().string()
}

type objStrRef struct {
	base    *Object
	name    unistring.String
	this    Value
	strict  bool
	binding bool
}

func (r *objStrRef) get() Value {
	if v := r.base.self.getStr(r.name, r.this); v != nil {
		return v
	}
	if r.binding {
		rt := r.base.runtime
		panic(rt.newReferenceError(r.name))
	}
	return _undefined
}

func (r *objStrRef) set(v Value) {
	if r.strict && r.binding && !r.base.self.hasOwnPropertyStr(r.name) {
		panic(referenceError(fmt.Sprintf("%s is not defined", r.name)))
	}
	if r.this != nil {
		r.base.setStr(r.name, v, r.this, r.strict)
	} else {
		r.base.self.setOwnStr(r.name, v, r.strict)
	}
}

func (r *objStrRef) init(v Value) {
	if r.this != nil {
		r.base.setStr(r.name, v, r.this, r.strict)
	} else {
		r.base.self.setOwnStr(r.name, v, r.strict)
	}
}

func (r *objStrRef) refname() unistring.String {
	return r.name
}

type privateRefRes struct {
	base *Object
	name *resolvedPrivateName
}

func (p *privateRefRes) get() Value {
	return (*getPrivatePropRes)(p.name)._get(p.base, p.base.runtime.vm)
}

func (p *privateRefRes) set(value Value) {
	(*setPrivatePropRes)(p.name)._set(p.base, value, p.base.runtime.vm)
}

func (p *privateRefRes) init(value Value) {
	panic("not supported")
}

func (p *privateRefRes) refname() unistring.String {
	return p.name.string()
}

type privateRefId struct {
	base *Object
	id   *privateId
}

func (p *privateRefId) get() Value {
	return p.base.runtime.vm.getPrivateProp(p.base, p.id.name, p.id.typ, p.id.idx, p.id.isMethod)
}

func (p *privateRefId) set(value Value) {
	p.base.runtime.vm.setPrivateProp(p.base, p.id.name, p.id.typ, p.id.idx, p.id.isMethod, value)
}

func (p *privateRefId) init(value Value) {
	panic("not supported")
}

func (p *privateRefId) refname() unistring.String {
	return p.id.string()
}

type unresolvedRef struct {
	runtime *Runtime
	name    unistring.String
}

func (r *unresolvedRef) get() Value {
	r.runtime.throwReferenceError(r.name)
	panic("Unreachable")
}

func (r *unresolvedRef) set(Value) {
	r.get()
}

func (r *unresolvedRef) init(Value) {
	r.get()
}

func (r *unresolvedRef) refname() unistring.String {
	return r.name
}

type vm struct {
	r            *Runtime
	prg          *Program
	pc           int
	stack        valueStack
	sp, sb, args int

	stash     *stash
	privEnv   *privateEnv
	callStack []context
	iterStack []iterStackItem
	refStack  []ref
	tryStack  []tryFrame
	newTarget Value
	result    Value

	maxCallStackSize int

	stashAllocs int

	interrupted   uint32
	interruptVal  interface{}
	interruptLock sync.Mutex

	curAsyncRunner *asyncRunner

	profTracker *profTracker
	debugger    *Debugger
	debugMode   bool // TODO drop this as we can just check debugger is nil or not
}

type instruction interface {
	exec(*vm)
}

func intToValue(i int64) Value {
	if idx := 256 + i; idx >= 0 && idx < 256 {
		return intCache[idx]
	}
	if i >= -maxInt && i <= maxInt {
		return valueInt(i)
	}
	return valueFloat(i)
}

func floatToInt(f float64) (result int64, ok bool) {
	if (f != 0 || !math.Signbit(f)) && !math.IsInf(f, 0) && f == math.Trunc(f) && f >= -maxInt && f <= maxInt {
		return int64(f), true
	}
	return 0, false
}

func floatToValue(f float64) (result Value) {
	if i, ok := floatToInt(f); ok {
		return intToValue(i)
	}
	switch {
	case f == 0:
		return _negativeZero
	case math.IsNaN(f):
		return _NaN
	case math.IsInf(f, 1):
		return _positiveInf
	case math.IsInf(f, -1):
		return _negativeInf
	}
	return valueFloat(f)
}

func toNumeric(value Value) Value {
	switch v := value.(type) {
	case valueInt, *valueBigInt:
		return v
	case valueFloat:
		return floatToValue(float64(v))
	case *Object:
		primValue := v.toPrimitiveNumber()
		if bigint, ok := primValue.(*valueBigInt); ok {
			return bigint
		}
		return primValue.ToNumber()
	}
	return value.ToNumber()
}

func (s *valueStack) expand(idx int) {
	if idx < len(*s) {
		return
	}
	idx++
	if idx < cap(*s) {
		*s = (*s)[:idx]
	} else {
		var newCap int
		if idx < 1024 {
			newCap = idx * 2
		} else {
			newCap = (idx + 1025) &^ 1023
		}
		n := make([]Value, idx, newCap)
		copy(n, *s)
		*s = n
	}
}

func stashObjHas(obj *Object, name unistring.String) bool {
	if obj.self.hasPropertyStr(name) {
		if unscopables, ok := obj.self.getSym(SymUnscopables, nil).(*Object); ok {
			if b := unscopables.self.getStr(name, nil); b != nil {
				return !b.ToBoolean()
			}
		}
		return true
	}
	return false
}

func (s *stash) isVariable() bool {
	return s.funcType != funcNone
}

func (s *stash) initByIdx(idx uint32, v Value) {
	if s.obj != nil {
		panic("Attempt to init by idx into an object scope")
	}

	if s.vm != nil && s.vm.debugMode {
		// Grow the values slice defensively if the compiler emitted a higher index than preallocated.
		if int(idx) >= len(s.values) {
			needed := int(idx) + 1
			extra := make([]Value, needed-len(s.values))
			s.values = append(s.values, extra...)
		}
	}
	s.values[idx] = v
}

func (s *stash) initByName(name unistring.String, v Value) {
	if idx, exists := s.names[name]; exists {
		s.values[idx&^maskTyp] = v
	} else {
		panic(referenceError(fmt.Sprintf("%s is not defined", name)))
	}
}

func (s *stash) getByIdx(idx uint32) Value {
	if int(idx) >= len(s.values) {
		// In debug mode, accessing an out-of-bounds index can happen when
		// code is compiled with different debug symbol info
		if s.vm != nil && s.vm.debugMode {
			return _undefined
		}
		return nil
	}
	return s.values[idx]
}

func (s *stash) getByName(name unistring.String) (v Value, exists bool) {
	if s.obj != nil {
		if stashObjHas(s.obj, name) {
			return nilSafe(s.obj.self.getStr(name, nil)), true
		}
		return nil, false
	}
	if idx, exists := s.names[name]; exists {
		v := s.values[idx&^maskTyp]
		if v == nil {
			if s.vm != nil && s.vm.debugMode {
				// In debug mode, return undefined instead of panicking
				// This handles function parameters and variables that haven't been initialized yet
				v = _undefined
			} else {
				if idx&maskVar == 0 {
					panic(errAccessBeforeInit)
				} else {
					v = _undefined
				}
			}
		} else if idx&maskIndirect != 0 {
			var f func(*vm) Value
			_ = s.vm.r.ExportTo(v, &f)
			v = f(s.vm)
		}
		return v, true
	}
	return nil, false
}

func (s *stash) getRefByName(name unistring.String, strict bool) ref {
	if obj := s.obj; obj != nil {
		if stashObjHas(obj, name) {
			return &objStrRef{
				base:    obj,
				name:    name,
				strict:  strict,
				binding: true,
			}
		}
	} else {
		if idx, exists := s.names[name]; exists {
			if idx&maskVar == 0 {
				if idx&maskConst == 0 {
					return &stashRefLex{
						stashRef: stashRef{
							n:   name,
							v:   &s.values,
							idx: int(idx &^ maskTyp),
							vm:  s.vm,
						},
					}
				} else {
					return &stashRefConst{
						stashRefLex: stashRefLex{
							stashRef: stashRef{
								n:   name,
								v:   &s.values,
								idx: int(idx &^ maskTyp),
								vm:  s.vm,
							},
						},
						strictConst: strict || (idx&maskStrict != 0),
					}
				}
			} else {
				return &stashRef{
					n:   name,
					v:   &s.values,
					idx: int(idx &^ maskTyp),
					vm:  s.vm,
				}
			}
		}
	}
	return nil
}

func (s *stash) createBinding(name unistring.String, deletable bool) {
	if s.names == nil {
		s.names = make(map[unistring.String]uint32)
	}
	if _, exists := s.names[name]; !exists {
		idx := uint32(len(s.names)) | maskVar
		if deletable {
			idx |= maskDeletable
		}
		s.names[name] = idx
		s.values = append(s.values, _undefined)
	}
}

func (s *stash) createLexBinding(name unistring.String, isConst bool) {
	if s.names == nil {
		s.names = make(map[unistring.String]uint32)
	}
	if _, exists := s.names[name]; !exists {
		idx := uint32(len(s.names))
		if isConst {
			idx |= maskConst | maskStrict
		}
		s.names[name] = idx
		s.values = append(s.values, nil)
	}
}

func (s *stash) deleteBinding(name unistring.String) {
	delete(s.names, name)
}

func (vm *vm) newStash() {
	vm.stash = &stash{
		outer: vm.stash,
		vm:    vm, // NOTE(@mstoykov): it will be nice if we do not have cyclic dependency
	}
	vm.stashAllocs++
}

func (vm *vm) init() {
	vm.sb = -1
	vm.stash = &vm.r.global.stash
	vm.maxCallStackSize = math.MaxInt32
}

func (vm *vm) halted() bool {
	if vm.prg == nil {
		return true
	}
	pc := vm.pc
	return pc < 0 || pc >= len(vm.prg.code)
}

func (vm *vm) run() {
	if vm.profTracker != nil && !vm.runWithProfiler() {
		return
	}
	count := 0
	interrupted := false
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
		pc := vm.pc
		if vm.prg == nil || pc < 0 || pc >= len(vm.prg.code) {
			break
		}
		vm.prg.code[pc].exec(vm)
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

func (vm *vm) runWithProfiler() bool {
	pt := vm.profTracker
	if pt == nil {
		pt = globalProfiler.p.registerVm()
		vm.profTracker = pt
		defer func() {
			atomic.StoreInt32(&vm.profTracker.finished, 1)
			vm.profTracker = nil
		}()
	}
	interrupted := false
	for {
		if interrupted = atomic.LoadUint32(&vm.interrupted) != 0; interrupted {
			return true
		}
		pc := vm.pc
		if vm.prg == nil || pc < 0 || pc >= len(vm.prg.code) {
			break
		}
		vm.prg.code[pc].exec(vm)
		req := atomic.LoadInt32(&pt.req)
		if req == profReqStop {
			return true
		}
		if req == profReqDoSample {
			pt.stop = time.Now()

			pt.numFrames = len(vm.r.CaptureCallStack(len(pt.frames), pt.frames[:0]))
			pt.frames[0].pc = pc
			atomic.StoreInt32(&pt.req, profReqSampleReady)
		}
	}

	return false
}

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

						wasHitDuringInit := vm.debugger.wasHitDuringInit(normalizedFilename, currentLine)

						if wasHitDuringInit {
							skipBreakpoints = true
							if vmDebugEnabled || vm.debugger.enableDebugLogging {
								fmt.Printf("[VM-INIT-CHECK] Skipping init breakpoint at line %d for '%s' (snapshotDone=%v, snapshotSize=%d)\n",
									currentLine, normalizedFilename, vm.debugger.initBPSnapshotDone, len(vm.debugger.initBPSnapshot))
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
			if !vm.debugger.next && !vm.debugger.stepIn {
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
				} else if vm.debugger.breakpointCheckCount < 3 {
					vm.debugger.breakpointCheckCount++
					if debugVM {
						fmt.Printf("[BP-TRACE] SKIPPED breakpoint() call: skipBreakpoints=true, initPhase=%v, initComplete=%v, normFile=%q\n",
						vm.debugger.initPhase, vm.debugger.initComplete, vm.debugger.cachedNormFile)
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
							fmt.Printf("[VM-SUPPRESS] Suppressing line %d (PC=%d) in %s — inherited from skipped if-body (suppressedInheritedLine=%d)\n",
								currentLine, currentPC, normalizedCurrentFilename, vm.debugger.suppressedInheritedLine)
						} else {
							fmt.Printf("[VM-SUPPRESS] Clearing suppressedInheritedLine=%d (was for %s), now at line %d in %s\n",
								vm.debugger.suppressedInheritedLine, vm.debugger.suppressedInheritedFile, currentLine, normalizedCurrentFilename)
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
							case jump, *leaveBlock, *enterCatchBlock, leaveTry, enterFinally:
								isControlFlowOnly = true
							case _loadUndef:
								// Detect implicit return pattern: _loadUndef followed by _ret.
								// See step-over path for full explanation.
								nextPC := currentPC + 1
								if nextPC < len(vm.prg.code) {
									if _, isRet := vm.prg.code[nextPC].(_ret); isRet {
										isControlFlowOnly = true
									}
								}
							case _ret:
								// Also skip _ret after _loadUndef (implicit return pattern).
								if currentPC > 0 {
									if _, isLU := vm.prg.code[currentPC-1].(_loadUndef); isLU {
										isControlFlowOnly = true
									}
								}
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

						// FIX: Also check inherited position for step-in (same as step-over).
						if shouldBreak && currentPC > 0 && lastExecPC >= 0 && currentPC > lastExecPC+1 && vm.prg.src != nil {
							prevInstrLine := vm.prg.src.Position(vm.prg.sourceOffset(currentPC - 1)).Line
							if prevInstrLine == currentLine {
								shouldBreak = false
								breakReason = "stepIn-inherited-pos-after-jump"
								vm.debugger.suppressedInheritedLine = currentLine
								vm.debugger.suppressedInheritedFile = normalizedCurrentFilename
								fmt.Printf("[VM-STEPIN-SKIP] Skipping step-in break at line %d (PC=%d): reached via forward jump from lastExecPC=%d, prev bytecode (PC=%d) has same source line\n",
									currentLine, currentPC, lastExecPC, currentPC-1)
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
						isControlFlowOnly := false
						if currentPC >= 0 && currentPC < len(vm.prg.code) {
							switch vm.prg.code[currentPC].(type) {
							case jump, *leaveBlock, *enterCatchBlock, leaveTry, enterFinally:
								isControlFlowOnly = true
							case _loadUndef:
								// Detect implicit return pattern: _loadUndef followed by _ret.
								// The compiler emits this at the end of functions without an explicit
								// return. These instructions inherit the source position of the last
								// compiled statement, which may be in the ELSE branch of an if/else.
								// When stepping past the if-body (via jump), the debugger would
								// incorrectly break at the else body's source line. Marking the
								// implicit return as control-flow-only prevents this false stop.
								nextPC := currentPC + 1
								if nextPC < len(vm.prg.code) {
									if _, isRet := vm.prg.code[nextPC].(_ret); isRet {
										isControlFlowOnly = true
									}
								}
							case _ret:
								// Also skip the _ret that follows _loadUndef in the implicit return
								// pattern. After _loadUndef is skipped (above), _ret would still
								// trigger a break because it inherits the same wrong source position.
								if currentPC > 0 {
									if _, isLU := vm.prg.code[currentPC-1].(_loadUndef); isLU {
										isControlFlowOnly = true
									}
								}
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
								fmt.Printf("[VM-STEPOVER-SKIP] Skipping step-over break at line %d (PC=%d): reached via forward jump from lastExecPC=%d, prev bytecode (PC=%d) has same source line\n",
									currentLine, currentPC, lastExecPC, currentPC-1)
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

					// Also suppress if this line was already identified as inherited
					if suppressedByInheritedLine {
						shouldBreak = false
						breakReason = "suppressed-inherited-line"
					}

					// FIX: Skip breakpoints/steps at ANY instruction whose source position
					// was inherited from code inside a skipped block (if-body, else-body,
					// loop body, etc.).
					//
					// When the compiler emits bytecodes, instructions without explicit source
					// positions inherit the position of the last instruction that had one.
					// If the last compiled statement is inside an if-body, instructions emitted
					// AFTER that body (implicit returns, next statements, etc.) inherit the
					// source line of that last body statement.
					//
					// When the if-condition is false, the conditional jump skips the body and
					// lands on these inherited-position instructions. If the user has a
					// breakpoint on that inherited line (or is stepping), the debugger falsely
					// pauses — the IDE shows "I'm at line X inside the if-body" even though
					// the body was never entered.
					//
					// Detection: current PC was reached via a forward jump (gap between
					// lastExecPC and currentPC > 1), AND the bytecode immediately before the
					// current PC maps to the same source line (confirming position inheritance
					// from the skipped block's last compiled instruction).
					//
					// This does NOT affect code reached sequentially (lastExecPC + 1 == currentPC),
					// so explicit statements on the same line are not suppressed.
					if shouldBreak && currentPC > 0 && lastExecPC >= 0 && currentPC > lastExecPC+1 && vm.prg.src != nil {
						prevInstrLine := vm.prg.src.Position(vm.prg.sourceOffset(currentPC - 1)).Line
						if prevInstrLine == currentLine {
							shouldBreak = false
							breakReason = "inherited-pos-after-jump"
							vm.debugger.suppressedInheritedLine = currentLine
							vm.debugger.suppressedInheritedFile = normalizedCurrentFilename
							fmt.Printf("[VM-BP-SKIP] Skipping break at line %d (PC=%d): reached via forward jump from lastExecPC=%d, prev bytecode (PC=%d) has same source line (inherited position)\n",
								currentLine, currentPC, lastExecPC, currentPC-1)
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

func (vm *vm) Interrupt(v interface{}) {
	vm.interruptLock.Lock()
	vm.interruptVal = v
	atomic.StoreUint32(&vm.interrupted, 1)
	vm.interruptLock.Unlock()
}

func (vm *vm) ClearInterrupt() {
	atomic.StoreUint32(&vm.interrupted, 0)
}

func getFuncName(stack []Value, sb int) unistring.String {
	if sb > 0 {
		if f, ok := stack[sb-1].(*Object); ok {
			if _, isProxy := f.self.(*proxyObject); isProxy {
				return "proxy"
			}
			return nilSafe(f.self.getStr("name", nil)).string()
		}
	}
	return ""
}

func (vm *vm) captureStack(stack []StackFrame, ctxOffset int) []StackFrame {
	// Unroll the context stack
	if vm.prg != nil || vm.sb > 0 {
		var funcName unistring.String
		if vm.prg != nil {
			funcName = vm.prg.funcName
		} else {
			funcName = getFuncName(vm.stack, vm.sb)
		}
		stack = append(stack, StackFrame{prg: vm.prg, pc: vm.pc, funcName: funcName})
	}
	for i := len(vm.callStack) - 1; i > ctxOffset-1; i-- {
		frame := &vm.callStack[i]
		if frame.prg != nil || frame.sb > 0 {
			var funcName unistring.String
			if prg := frame.prg; prg != nil {
				funcName = prg.funcName
			} else {
				funcName = getFuncName(vm.stack, frame.sb)
			}
			stack = append(stack, StackFrame{prg: vm.callStack[i].prg, pc: frame.pc, funcName: funcName})
		}
	}
	if ctxOffset == 0 && vm.curAsyncRunner != nil {
		stack = vm.captureAsyncStack(stack, vm.curAsyncRunner)
	}
	return stack
}

func (vm *vm) captureAsyncStack(stack []StackFrame, runner *asyncRunner) []StackFrame {
	if promise, _ := runner.promiseCap.promise.self.(*Promise); promise != nil {
		if len(promise.fulfillReactions) == 1 {
			if r := promise.fulfillReactions[0].asyncRunner; r != nil {
				ctx := &r.gen.ctx
				if ctx.prg != nil || ctx.sb > 0 {
					var funcName unistring.String
					if prg := ctx.prg; prg != nil {
						funcName = prg.funcName
					} else {
						funcName = getFuncName(ctx.stack, 1)
					}
					stack = append(stack, StackFrame{prg: ctx.prg, pc: ctx.pc, funcName: funcName})
				}
				stack = vm.captureAsyncStack(stack, r)
			}
		}
	}

	return stack
}

func (vm *vm) pushTryFrame(catchPos, finallyPos int32) {
	vm.tryStack = append(vm.tryStack, tryFrame{
		callStackLen: uint32(len(vm.callStack)),
		iterLen:      uint32(len(vm.iterStack)),
		refLen:       uint32(len(vm.refStack)),
		sp:           int32(vm.sp),
		stash:        vm.stash,
		privEnv:      vm.privEnv,
		catchPos:     catchPos,
		finallyPos:   finallyPos,
		finallyRet:   -1,
	})
}

func (vm *vm) popTryFrame() {
	vm.tryStack = vm.tryStack[:len(vm.tryStack)-1]
}

func (vm *vm) restoreStacks(iterLen, refLen uint32) (ex *Exception) {
	// Restore other stacks
	iterTail := vm.iterStack[iterLen:]
	for i := len(iterTail) - 1; i >= 0; i-- {
		if iter := iterTail[i].iter; iter != nil {
			ex1 := vm.try(func() {
				iter.returnIter()
			})
			if ex1 != nil && ex == nil {
				ex = ex1
			}
		}
		iterTail[i] = iterStackItem{}
	}
	vm.iterStack = vm.iterStack[:iterLen]
	refTail := vm.refStack[refLen:]
	for i := range refTail {
		refTail[i] = nil
	}
	vm.refStack = vm.refStack[:refLen]
	return
}

func (vm *vm) handleThrow(arg interface{}) *Exception {
	ex := vm.exceptionFromValue(arg)

	// ── Debugger: capture the throw-site location BEFORE unwinding ──────
	// handleThrow restores vm.prg/vm.pc from the call stack when unwinding
	// to a try frame, which clobbers the position where the throw occurred.
	// Capture the throw-site file+line NOW (from the exception's stack trace
	// which was populated by exceptionFromValue) so BreakOnException can
	// show the correct source location — matching Node.js/Chrome DevTools.
	var throwFile string
	var throwLine int
	if vm.debugMode && vm.debugger != nil && ex != nil && len(ex.stack) > 0 {
		frame := &ex.stack[0]
		pos := frame.Position()
		throwFile = normalizeFilename(pos.Filename)
		throwLine = pos.Line
		// If the stack frame's position is empty (native code), try current vm state
		if throwFile == "" && vm.prg != nil && vm.prg.src != nil {
			pos = vm.prg.src.Position(vm.prg.sourceOffset(vm.pc))
			throwFile = normalizeFilename(pos.Filename)
			throwLine = pos.Line
		}

		// Capture the stash chain at the throw site BEFORE unwinding.
		// handleThrow restores vm.stash from the try frame (tf.stash),
		// losing all local variables at the throw point. Save them so
		// buildPausedVarSnapshot can show throw-site variables when paused
		// on an exception — matching Chrome DevTools / Node.js behaviour.
		vm.debugger.exceptionStash = vm.stash
		vm.debugger.exceptionSB = vm.sb
		vm.debugger.exceptionPrg = vm.prg
	}

	for len(vm.tryStack) > 0 {
		tf := &vm.tryStack[len(vm.tryStack)-1]
		if tf.catchPos == -1 && tf.finallyPos == -1 || ex == nil && tf.catchPos != tryPanicMarker {
			tf.exception = nil
			vm.popTryFrame()
			continue
		}
		if int(tf.callStackLen) < len(vm.callStack) {
			ctx := &vm.callStack[tf.callStackLen]
			vm.prg, vm.newTarget, vm.result, vm.pc, vm.sb, vm.args = ctx.prg, ctx.newTarget, ctx.result, ctx.pc, ctx.sb, ctx.args
			vm.callStack = vm.callStack[:tf.callStackLen]
		}
		vm.sp = int(tf.sp)
		vm.stash = tf.stash
		vm.privEnv = tf.privEnv
		_ = vm.restoreStacks(tf.iterLen, tf.refLen)

		if tf.catchPos == tryPanicMarker {
			break
		}

		if tf.catchPos >= 0 {
			// exception is caught
			// Break on caught exception if the debugger has that filter enabled.
			// Don't break on exceptions from eval/debugger-internal code.
			// CRITICAL: Pass throwFile/throwLine (captured BEFORE stack unwind)
			// so the debugger pauses at the THROW site, not the catch handler.
			if vm.debugMode && vm.debugger != nil && ex != nil && !vm.debugger.inEvalContext {
				currentFile := ""
				if vm.prg != nil && vm.prg.src != nil {
					currentFile = vm.prg.src.Name()
				}
				if currentFile != "<debugger-eval>" {
					vm.debugger.BreakOnException(ex.val, true, throwFile, throwLine)
				}
				if debugVM {
					fmt.Printf("[HANDLETHROW] After BreakOnException(caught): next=%v, stepIn=%v, suppress=%v, pc will be=%d, depth=%d\n",
						vm.debugger.next, vm.debugger.stepIn, vm.debugger.suppressDebugger, int(tf.catchPos), len(vm.callStack))
				}
			}
			vm.push(ex.val)
			vm.pc = int(tf.catchPos)
			tf.catchPos = -1
			return nil
		}
		if tf.finallyPos >= 0 {
			// no 'catch' block, but there is a 'finally' block
			tf.exception = ex
			vm.pc = int(tf.finallyPos)
			tf.finallyPos = -1
			tf.finallyRet = -1
			return nil
		}
	}
	if ex == nil {
		panic(arg)
	}
	return ex
}

// Calls to this method must be made from the run() loop and must be the last statement before 'return'.
// In all other cases exceptions must be thrown using panic().
func (vm *vm) throw(v interface{}) {
	if ex := vm.handleThrow(v); ex != nil {
		if vm.debugMode && vm.debugger != nil && !vm.debugger.inEvalContext {
			currentFile := ""
			if vm.prg != nil && vm.prg.src != nil {
				currentFile = vm.prg.src.Name()
			}
			if currentFile != "<debugger-eval>" {
				// Save the exception stack frames in the debugger BEFORE they're lost.
				// handleThrow has already unwound vm.callStack, so CaptureCallStack()
				// will return empty after this point. ex.stack has the original frames.
				vm.debugger.SetLastExceptionStack(ex.stack)

				// Extract the throw-site location from the exception's stack trace.
				// handleThrow has already unwound vm.prg/vm.pc so we cannot use
				// the debugger's Filename()/Line() — they'd point to the wrong place.
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
		panic(ex)
	}
}

func (vm *vm) try(f func()) (ex *Exception) {
	vm.pushTryFrame(tryPanicMarker, -1)
	defer vm.popTryFrame()

	defer func() {
		if x := recover(); x != nil {
			ex = vm.handleThrow(x)
		}
	}()

	f()
	return
}

func (vm *vm) runTry() (ex *Exception) {
	vm.pushTryFrame(tryPanicMarker, -1)
	defer vm.popTryFrame()

	for {
		ex = vm.runTryInner()
		if ex != nil || vm.halted() {
			return
		}
	}
}

func (vm *vm) runTryInner() (ex *Exception) {
	defer func() {
		if x := recover(); x != nil {
			ex = vm.handleThrow(x)
			if ex != nil && vm.debugMode && vm.debugger != nil {
				// Save exception stack frames (may already be set by vm.throw,
				// but also save here for exceptions caught only by runTryInner).
				if len(ex.stack) > 0 {
					vm.debugger.SetLastExceptionStack(ex.stack)
				}
				if debugActivate {
					fmt.Printf("[EXCEPTION-TRACE] runTryInner defer: recovered exception=%q, pendingUncaughtException=%v, inEvalContext=%v\n",
						ex.val.String(), vm.debugger.pendingUncaughtException != nil, vm.debugger.inEvalContext)
				}

				if !vm.debugger.inEvalContext && vm.debugger.pendingUncaughtException == nil {
					// Extract throw-site from the exception stack trace
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
				// CRITICAL: Do NOT mark the VM as exited when the exception
				// originated inside a debugger eval (evaluateComplexExpression).
				// Eval exceptions (e.g., ReferenceError for a variable preview)
				// are caught by eval's own recovery handler and must not poison
				// the real VM's lifecycle state.  Closing vmDoneCh here causes
				// Continue() to think the VM terminated, breaking the entire
				// debug session.
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
		}
	}()

	if vm.debugMode {
		vm.debug()
	} else {
		vm.run()
	}
	return
}

func (vm *vm) push(v Value) {
	vm.stack.expand(vm.sp)
	vm.stack[vm.sp] = v
	vm.sp++
}

func (vm *vm) pop() Value {
	vm.sp--
	return vm.stack[vm.sp]
}

func (vm *vm) peek() Value {
	return vm.stack[vm.sp-1]
}

func (vm *vm) saveCtx(ctx *context) {
	ctx.prg, ctx.stash, ctx.privEnv, ctx.newTarget, ctx.result, ctx.pc, ctx.sb, ctx.args = vm.prg, vm.stash, vm.privEnv, vm.newTarget, vm.result, vm.pc, vm.sb, vm.args
}

func (vm *vm) pushCtx() {
	if len(vm.callStack) > vm.maxCallStackSize {
		ex := &StackOverflowError{}
		ex.stack = vm.captureStack(nil, 0)
		panic(ex)
	}
	vm.callStack = append(vm.callStack, context{})
	ctx := &vm.callStack[len(vm.callStack)-1]
	vm.saveCtx(ctx)
}

func (vm *vm) restoreCtx(ctx *context) {
	vm.prg, vm.stash, vm.privEnv, vm.newTarget, vm.result, vm.pc, vm.sb, vm.args = ctx.prg, ctx.stash, ctx.privEnv, ctx.newTarget, ctx.result, ctx.pc, ctx.sb, ctx.args
}

func (vm *vm) popCtx() {
	l := len(vm.callStack) - 1
	ctx := &vm.callStack[l]
	vm.restoreCtx(ctx)

	if ctx.prg != nil {
		*ctx = context{}
	}

	vm.callStack = vm.callStack[:l]
}

func (vm *vm) toCallee(v Value) *Object {
	if obj, ok := v.(*Object); ok {
		return obj
	}
	switch unresolved := v.(type) {
	case valueUnresolved:
		unresolved.throw()
		panic("Unreachable")
	case memberUnresolved:
		panic(vm.r.NewTypeError("Object has no member '%s'", unresolved.ref))
	}
	panic(vm.r.NewTypeError("Value is not an object: %s", v.toString()))
}

type loadVal struct {
	v Value
}

func (l loadVal) exec(vm *vm) {
	vm.push(l.v)
	vm.pc++
}

type _loadUndef struct{}

var loadUndef _loadUndef

func (_loadUndef) exec(vm *vm) {
	vm.push(_undefined)
	vm.pc++
}

type _loadNil struct{}

var loadNil _loadNil

func (_loadNil) exec(vm *vm) {
	vm.push(nil)
	vm.pc++
}

type _saveResult struct{}

var saveResult _saveResult

func (_saveResult) exec(vm *vm) {
	vm.sp--
	vm.result = vm.stack[vm.sp]
	vm.pc++
}

type _loadResult struct{}

var loadResult _loadResult

func (_loadResult) exec(vm *vm) {
	vm.push(vm.result)
	vm.pc++
}

type _clearResult struct{}

var clearResult _clearResult

func (_clearResult) exec(vm *vm) {
	vm.result = _undefined
	vm.pc++
}

type _loadGlobalObject struct{}

var loadGlobalObject _loadGlobalObject

func (_loadGlobalObject) exec(vm *vm) {
	vm.push(vm.r.globalObject)
	vm.pc++
}

type loadStack int

func (l loadStack) exec(vm *vm) {
	// l > 0 -- var<l-1>
	// l == 0 -- this

	if l > 0 {
		vm.push(nilSafe(vm.stack[vm.sb+vm.args+int(l)]))
	} else {
		vm.push(vm.stack[vm.sb])
	}
	vm.pc++
}

type loadStack1 int

func (l loadStack1) exec(vm *vm) {
	// args are in stash
	// l > 0 -- var<l-1>
	// l == 0 -- this

	if l > 0 {
		vm.push(nilSafe(vm.stack[vm.sb+int(l)]))
	} else {
		vm.push(vm.stack[vm.sb])
	}
	vm.pc++
}

type loadStackLex int

func (l loadStackLex) exec(vm *vm) {
	// l < 0 -- arg<-l-1>
	// l > 0 -- var<l-1>
	// l == 0 -- this
	var p *Value
	if l <= 0 {
		arg := int(-l)
		if arg > vm.args {
			vm.push(_undefined)
			vm.pc++
			return
		} else {
			p = &vm.stack[vm.sb+arg]
		}
	} else {
		p = &vm.stack[vm.sb+vm.args+int(l)]
	}
	if *p == nil {
		vm.throw(errAccessBeforeInit)
		return
	}
	vm.push(*p)
	vm.pc++
}

type loadStack1Lex int

func (l loadStack1Lex) exec(vm *vm) {
	p := &vm.stack[vm.sb+int(l)]
	if *p == nil {
		vm.throw(errAccessBeforeInit)
		return
	}
	vm.push(*p)
	vm.pc++
}

type _loadCallee struct{}

var loadCallee _loadCallee

func (_loadCallee) exec(vm *vm) {
	vm.push(vm.stack[vm.sb-1])
	vm.pc++
}

func (vm *vm) storeStack(s int) {
	// l > 0 -- var<l-1>

	if s > 0 {
		vm.stack[vm.sb+vm.args+s] = vm.stack[vm.sp-1]
	} else {
		panic("Illegal stack var index")
	}
	vm.pc++
}

func (vm *vm) storeStack1(s int) {
	// args are in stash
	// l > 0 -- var<l-1>

	if s > 0 {
		vm.stack[vm.sb+s] = vm.stack[vm.sp-1]
	} else {
		panic("Illegal stack var index")
	}
	vm.pc++
}

func (vm *vm) storeStackLex(s int) {
	// l < 0 -- arg<-l-1>
	// l > 0 -- var<l-1>
	var p *Value
	if s < 0 {
		p = &vm.stack[vm.sb-s]
	} else {
		p = &vm.stack[vm.sb+vm.args+s]
	}

	if *p != nil {
		*p = vm.stack[vm.sp-1]
	} else {
		panic(errAccessBeforeInit)
	}
	vm.pc++
}

func (vm *vm) storeStack1Lex(s int) {
	// args are in stash
	// s > 0 -- var<l-1>
	if s <= 0 {
		panic("Illegal stack var index")
	}
	p := &vm.stack[vm.sb+s]
	if *p != nil {
		*p = vm.stack[vm.sp-1]
	} else {
		panic(errAccessBeforeInit)
	}
	vm.pc++
}

func (vm *vm) initStack(s int) {
	if s <= 0 {
		vm.stack[vm.sb-s] = vm.stack[vm.sp-1]
	} else {
		vm.stack[vm.sb+vm.args+s] = vm.stack[vm.sp-1]
	}
	vm.pc++
}

func (vm *vm) initStack1(s int) {
	if s <= 0 {
		panic("Illegal stack var index")
	}
	vm.stack[vm.sb+s] = vm.stack[vm.sp-1]
	vm.pc++
}

type storeStack int

func (s storeStack) exec(vm *vm) {
	vm.storeStack(int(s))
}

type storeStack1 int

func (s storeStack1) exec(vm *vm) {
	vm.storeStack1(int(s))
}

type storeStackLex int

func (s storeStackLex) exec(vm *vm) {
	vm.storeStackLex(int(s))
}

type storeStack1Lex int

func (s storeStack1Lex) exec(vm *vm) {
	vm.storeStack1Lex(int(s))
}

type initStack int

func (s initStack) exec(vm *vm) {
	vm.initStack(int(s))
}

type initStackP int

func (s initStackP) exec(vm *vm) {
	vm.initStack(int(s))
	vm.sp--
}

type initStack1 int

func (s initStack1) exec(vm *vm) {
	vm.initStack1(int(s))
}

type initStack1P int

func (s initStack1P) exec(vm *vm) {
	vm.initStack1(int(s))
	vm.sp--
}

type importNamespace struct {
	module ModuleRecord
}

func (i importNamespace) exec(vm *vm) {
	vm.push(vm.r.NamespaceObjectFor(i.module))
	vm.pc++
}

type export struct {
	idx      uint32
	callback func(*vm, func() Value)
}

func (e export) exec(vm *vm) {
	// from loadStash
	level := int(e.idx >> 24)
	idx := uint32(e.idx & 0x00FFFFFF)
	stash := vm.stash
	for i := 0; i < level; i++ {
		stash = stash.outer
	}
	e.callback(vm, func() Value {
		if vm != nil && vm.debugMode {
			v := stash.getByIdx(idx)
			if v == nil {
				return _undefined
			}
			return v
		} else {
			return stash.getByIdx(idx)
		}
	})
	vm.pc++
}

type exportLex struct {
	idx      uint32
	callback func(*vm, func() Value)
}

func (e exportLex) exec(vm *vm) {
	// from loadStashLex
	level := int(e.idx >> 24)
	idx := uint32(e.idx & 0x00FFFFFF)
	stash := vm.stash
	for i := 0; i < level; i++ {
		stash = stash.outer
	}
	e.callback(vm, func() Value {
		v := stash.getByIdx(idx)
		if v == nil {
			if vm != nil && vm.debugMode {
				// In debug mode, return undefined instead of panicking for uninitialized variables
				return _undefined
			}
			panic(errAccessBeforeInit)
		}
		return v
	})
	vm.pc++
}

type exportIndirect struct {
	callback func(*vm)
}

func (e exportIndirect) exec(vm *vm) {
	e.callback(vm)
	vm.pc++
}

type storeStackP int

func (s storeStackP) exec(vm *vm) {
	vm.storeStack(int(s))
	vm.sp--
}

type storeStack1P int

func (s storeStack1P) exec(vm *vm) {
	vm.storeStack1(int(s))
	vm.sp--
}

type storeStackLexP int

func (s storeStackLexP) exec(vm *vm) {
	vm.storeStackLex(int(s))
	vm.sp--
}

type storeStack1LexP int

func (s storeStack1LexP) exec(vm *vm) {
	vm.storeStack1Lex(int(s))
	vm.sp--
}

type _toNumber struct{}

var toNumber _toNumber

func (_toNumber) exec(vm *vm) {
	vm.stack[vm.sp-1] = toNumeric(vm.stack[vm.sp-1])
	vm.pc++
}

type _add struct{}

var add _add

func (_add) exec(vm *vm) {
	right := vm.stack[vm.sp-1]
	left := vm.stack[vm.sp-2]

	if o, ok := left.(*Object); ok {
		left = o.toPrimitive()
	}

	if o, ok := right.(*Object); ok {
		right = o.toPrimitive()
	}

	var ret Value

	leftString, isLeftString := left.(String)
	rightString, isRightString := right.(String)

	if isLeftString || isRightString {
		if !isLeftString {
			leftString = left.toString()
		}
		if !isRightString {
			rightString = right.toString()
		}
		ret = leftString.Concat(rightString)
	} else {
		switch left := left.(type) {
		case valueInt:
			switch right := right.(type) {
			case valueInt:
				ret = intToValue(int64(left) + int64(right))
			case *valueBigInt:
				panic(errMixBigIntType)
			default:
				ret = floatToValue(float64(left) + right.ToFloat())
			}
		case *valueBigInt:
			if right, ok := right.(*valueBigInt); ok {
				ret = (*valueBigInt)(new(big.Int).Add((*big.Int)(left), (*big.Int)(right)))
			} else {
				panic(errMixBigIntType)
			}
		default:
			if _, ok := right.(*valueBigInt); ok {
				panic(errMixBigIntType)
			}
			ret = floatToValue(left.ToFloat() + right.ToFloat())
		}
	}

	vm.stack[vm.sp-2] = ret
	vm.sp--
	vm.pc++
}

type _sub struct{}

var sub _sub

func (_sub) exec(vm *vm) {
	right := vm.stack[vm.sp-1]
	left := vm.stack[vm.sp-2]

	left = toNumeric(left)
	right = toNumeric(right)

	var result Value

	switch left := left.(type) {
	case valueInt:
		switch right := right.(type) {
		case valueInt:
			result = intToValue(int64(left) - int64(right))
			goto end
		case *valueBigInt:
			panic(errMixBigIntType)
		}
	case valueFloat:
		if _, ok := right.(*valueBigInt); ok {
			panic(errMixBigIntType)
		}
	case *valueBigInt:
		if right, ok := right.(*valueBigInt); ok {
			result = (*valueBigInt)(new(big.Int).Sub((*big.Int)(left), (*big.Int)(right)))
			goto end
		}
		panic(errMixBigIntType)
	}

	result = floatToValue(left.ToFloat() - right.ToFloat())
end:
	vm.sp--
	vm.stack[vm.sp-1] = result
	vm.pc++
}

type _mul struct{}

var mul _mul

func (_mul) exec(vm *vm) {
	left := toNumeric(vm.stack[vm.sp-2])
	right := toNumeric(vm.stack[vm.sp-1])

	var result Value

	switch left := left.(type) {
	case valueInt:
		switch right := right.(type) {
		case valueInt:
			if left == 0 && right == -1 || left == -1 && right == 0 {
				result = _negativeZero
				goto end
			}
			res := left * right
			// check for overflow
			if left == 0 || right == 0 || res/left == right {
				result = intToValue(int64(res))
				goto end
			}
		case *valueBigInt:
			panic(errMixBigIntType)
		}
	case valueFloat:
		if _, ok := right.(*valueBigInt); ok {
			panic(errMixBigIntType)
		}
	case *valueBigInt:
		if right, ok := right.(*valueBigInt); ok {
			result = (*valueBigInt)(new(big.Int).Mul((*big.Int)(left), (*big.Int)(right)))
			goto end
		}
		panic(errMixBigIntType)
	}

	result = floatToValue(left.ToFloat() * right.ToFloat())

end:
	vm.sp--
	vm.stack[vm.sp-1] = result
	vm.pc++
}

type _exp struct{}

var exp _exp

func (_exp) exec(vm *vm) {
	vm.sp--
	x := vm.stack[vm.sp-1]
	y := vm.stack[vm.sp]

	x = toNumeric(x)
	y = toNumeric(y)

	var result Value
	if x, ok := x.(*valueBigInt); ok {
		if y, ok := y.(*valueBigInt); ok {
			if (*big.Int)(y).Cmp(big.NewInt(0)) < 0 {
				panic(vm.r.newError(vm.r.getRangeError(), "exponent must be positive"))
			}
			result = (*valueBigInt)(new(big.Int).Exp((*big.Int)(x), (*big.Int)(y), nil))
			goto end
		}
		panic(errMixBigIntType)
	} else if _, ok := y.(*valueBigInt); ok {
		panic(errMixBigIntType)
	}

	result = pow(x, y)
end:
	vm.stack[vm.sp-1] = result
	vm.pc++
}

type _div struct{}

var div _div

func (_div) exec(vm *vm) {
	leftValue := toNumeric(vm.stack[vm.sp-2])
	rightValue := toNumeric(vm.stack[vm.sp-1])

	var (
		result      Value
		left, right float64
	)

	if left, ok := leftValue.(*valueBigInt); ok {
		if right, ok := rightValue.(*valueBigInt); ok {
			if (*big.Int)(right).Cmp(big.NewInt(0)) == 0 {
				panic(vm.r.newError(vm.r.getRangeError(), "Division by zero"))
			}
			if (*big.Int)(left).CmpAbs((*big.Int)(right)) < 0 {
				result = (*valueBigInt)(big.NewInt(0))
			} else {
				i, _ := new(big.Int).QuoRem((*big.Int)(left), (*big.Int)(right), big.NewInt(0))
				result = (*valueBigInt)(i)
			}
			goto end
		}
		panic(errMixBigIntType)
	} else if _, ok := rightValue.(*valueBigInt); ok {
		panic(errMixBigIntType)
	}
	left, right = leftValue.ToFloat(), rightValue.ToFloat()

	if math.IsNaN(left) || math.IsNaN(right) {
		result = _NaN
		goto end
	}
	if math.IsInf(left, 0) && math.IsInf(right, 0) {
		result = _NaN
		goto end
	}
	if left == 0 && right == 0 {
		result = _NaN
		goto end
	}

	if math.IsInf(left, 0) {
		if math.Signbit(left) == math.Signbit(right) {
			result = _positiveInf
			goto end
		} else {
			result = _negativeInf
			goto end
		}
	}
	if math.IsInf(right, 0) {
		if math.Signbit(left) == math.Signbit(right) {
			result = _positiveZero
			goto end
		} else {
			result = _negativeZero
			goto end
		}
	}
	if right == 0 {
		if math.Signbit(left) == math.Signbit(right) {
			result = _positiveInf
			goto end
		} else {
			result = _negativeInf
			goto end
		}
	}

	result = floatToValue(left / right)

end:
	vm.sp--
	vm.stack[vm.sp-1] = result
	vm.pc++
}

type _mod struct{}

var mod _mod

func (_mod) exec(vm *vm) {
	left := toNumeric(vm.stack[vm.sp-2])
	right := toNumeric(vm.stack[vm.sp-1])

	var result Value

	switch left := left.(type) {
	case valueInt:
		switch right := right.(type) {
		case valueInt:
			if right == 0 {
				result = _NaN
				goto end
			}
			r := left % right
			if r == 0 && left < 0 {
				result = _negativeZero
			} else {
				result = intToValue(int64(left % right))
			}
			goto end
		case *valueBigInt:
			panic(errMixBigIntType)
		}
	case valueFloat:
		if _, ok := right.(*valueBigInt); ok {
			panic(errMixBigIntType)
		}
	case *valueBigInt:
		if right, ok := right.(*valueBigInt); ok {
			switch {
			case (*big.Int)(right).Cmp(big.NewInt(0)) == 0:
				panic(vm.r.newError(vm.r.getRangeError(), "Division by zero"))
			case (*big.Int)(left).Cmp(big.NewInt(0)) < 0:
				abs := new(big.Int).Abs((*big.Int)(left))
				v := new(big.Int).Mod(abs, (*big.Int)(right))
				result = (*valueBigInt)(v.Neg(v))
			default:
				result = (*valueBigInt)(new(big.Int).Mod((*big.Int)(left), (*big.Int)(right)))
			}
			goto end
		}
		panic(errMixBigIntType)
	}

	result = floatToValue(math.Mod(left.ToFloat(), right.ToFloat()))
end:
	vm.sp--
	vm.stack[vm.sp-1] = result
	vm.pc++
}

type _neg struct{}

var neg _neg

func (_neg) exec(vm *vm) {
	operand := vm.stack[vm.sp-1]

	var result Value

	switch n := toNumeric(operand).(type) {
	case *valueBigInt:
		result = (*valueBigInt)(new(big.Int).Neg((*big.Int)(n)))
	case valueInt:
		if n == 0 {
			result = _negativeZero
		} else {
			result = -n
		}
	default:
		f := operand.ToFloat()
		if !math.IsNaN(f) {
			f = -f
		}
		result = valueFloat(f)
	}

	vm.stack[vm.sp-1] = result
	vm.pc++
}

type _plus struct{}

var plus _plus

func (_plus) exec(vm *vm) {
	vm.stack[vm.sp-1] = vm.stack[vm.sp-1].ToNumber()
	vm.pc++
}

type _inc struct{}

var inc _inc

func (_inc) exec(vm *vm) {
	v := vm.stack[vm.sp-1]

	switch n := v.(type) {
	case *valueBigInt:
		v = (*valueBigInt)(new(big.Int).Add((*big.Int)(n), big.NewInt(1)))
	case valueInt:
		v = intToValue(int64(n + 1))
	default:
		v = valueFloat(n.ToFloat() + 1)
	}

	vm.stack[vm.sp-1] = v
	vm.pc++
}

type _dec struct{}

var dec _dec

func (_dec) exec(vm *vm) {
	v := vm.stack[vm.sp-1]

	switch n := v.(type) {
	case *valueBigInt:
		v = (*valueBigInt)(new(big.Int).Sub((*big.Int)(n), big.NewInt(1)))
	case valueInt:
		v = intToValue(int64(n - 1))
	default:
		v = valueFloat(n.ToFloat() - 1)
	}

	vm.stack[vm.sp-1] = v
	vm.pc++
}

type _and struct{}

var and _and

func (_and) exec(vm *vm) {
	left := toNumeric(vm.stack[vm.sp-2])
	right := toNumeric(vm.stack[vm.sp-1])
	var result Value

	if left, ok := left.(*valueBigInt); ok {
		if right, ok := right.(*valueBigInt); ok {
			result = (*valueBigInt)(new(big.Int).And((*big.Int)(left), (*big.Int)(right)))
			goto end
		}
		panic(errMixBigIntType)
	} else if _, ok := right.(*valueBigInt); ok {
		panic(errMixBigIntType)
	}

	result = intToValue(int64(toInt32(left) & toInt32(right)))
end:
	vm.stack[vm.sp-2] = result
	vm.sp--
	vm.pc++
}

type _or struct{}

var or _or

func (_or) exec(vm *vm) {
	left := toNumeric(vm.stack[vm.sp-2])
	right := toNumeric(vm.stack[vm.sp-1])
	var result Value

	if left, ok := left.(*valueBigInt); ok {
		if right, ok := right.(*valueBigInt); ok {
			result = (*valueBigInt)(new(big.Int).Or((*big.Int)(left), (*big.Int)(right)))
			goto end
		}
		panic(errMixBigIntType)
	} else if _, ok := right.(*valueBigInt); ok {
		panic(errMixBigIntType)
	}

	result = intToValue(int64(toInt32(left) | toInt32(right)))
end:
	vm.stack[vm.sp-2] = result
	vm.sp--
	vm.pc++
}

type _xor struct{}

var xor _xor

func (_xor) exec(vm *vm) {
	left := toNumeric(vm.stack[vm.sp-2])
	right := toNumeric(vm.stack[vm.sp-1])
	var result Value

	if left, ok := left.(*valueBigInt); ok {
		if right, ok := right.(*valueBigInt); ok {
			result = (*valueBigInt)(new(big.Int).Xor((*big.Int)(left), (*big.Int)(right)))
			goto end
		}
		panic(errMixBigIntType)
	} else if _, ok := right.(*valueBigInt); ok {
		panic(errMixBigIntType)
	}

	result = intToValue(int64(toInt32(left) ^ toInt32(right)))
end:
	vm.stack[vm.sp-2] = result
	vm.sp--
	vm.pc++
}

type _bnot struct{}

var bnot _bnot

func (_bnot) exec(vm *vm) {
	v := vm.stack[vm.sp-1]
	switch n := toNumeric(v).(type) {
	case *valueBigInt:
		v = (*valueBigInt)(new(big.Int).Not((*big.Int)(n)))
	default:
		v = intToValue(int64(^toInt32(n)))
	}
	vm.stack[vm.sp-1] = v
	vm.pc++
}

type _sal struct{}

var sal _sal

func (_sal) exec(vm *vm) {
	left := toNumeric(vm.stack[vm.sp-2])
	right := toNumeric(vm.stack[vm.sp-1])
	var result Value

	if left, ok := left.(*valueBigInt); ok {
		if right, ok := right.(*valueBigInt); ok {
			n := uint((*big.Int)(right).Uint64())
			if (*big.Int)(right).Sign() < 0 {
				result = (*valueBigInt)(new(big.Int).Rsh((*big.Int)(left), n))
			} else {
				result = (*valueBigInt)(new(big.Int).Lsh((*big.Int)(left), n))
			}
			goto end
		}
		panic(errMixBigIntType)
	} else if _, ok := right.(*valueBigInt); ok {
		panic(errMixBigIntType)
	}

	result = intToValue(int64(toInt32(left) << (toUint32(right) & 0x1F)))
end:
	vm.stack[vm.sp-2] = result
	vm.sp--
	vm.pc++
}

type _sar struct{}

var sar _sar

func (_sar) exec(vm *vm) {
	left := toNumeric(vm.stack[vm.sp-2])
	right := toNumeric(vm.stack[vm.sp-1])
	var result Value

	if left, ok := left.(*valueBigInt); ok {
		if right, ok := right.(*valueBigInt); ok {
			n := uint((*big.Int)(right).Uint64())
			if (*big.Int)(right).Sign() < 0 {
				result = (*valueBigInt)(new(big.Int).Lsh((*big.Int)(left), n))
			} else {
				result = (*valueBigInt)(new(big.Int).Rsh((*big.Int)(left), n))
			}
			goto end
		}
		panic(errMixBigIntType)
	} else if _, ok := right.(*valueBigInt); ok {
		panic(errMixBigIntType)
	}

	result = intToValue(int64(toInt32(left) >> (toUint32(right) & 0x1F)))
end:
	vm.stack[vm.sp-2] = result
	vm.sp--
	vm.pc++
}

type _shr struct{}

var shr _shr

func (_shr) exec(vm *vm) {
	left := toNumeric(vm.stack[vm.sp-2])
	right := toNumeric(vm.stack[vm.sp-1])

	if _, ok := left.(*valueBigInt); ok {
		_ = toNumeric(right)
		panic(vm.r.NewTypeError("BigInts have no unsigned right shift, use >> instead"))
	} else if _, ok := right.(*valueBigInt); ok {
		panic(vm.r.NewTypeError("BigInts have no unsigned right shift, use >> instead"))
	}

	vm.stack[vm.sp-2] = intToValue(int64(toUint32(left) >> (toUint32(right) & 0x1F)))
	vm.sp--
	vm.pc++
}

type _debugger struct{}

var debugger _debugger

func (_debugger) exec(vm *vm) {
	vm.pc++
	if vm.debugMode && !vm.debugger.active { // this jumps over debugger statements
		vm.debugger.activate(DebuggerStatementActivation, vm.debugger.Filename(), vm.debugger.Line())
	}
}

type jump int32

func (j jump) exec(vm *vm) {
	vm.pc += int(j)
}

type _toPropertyKey struct{}

func (_toPropertyKey) exec(vm *vm) {
	p := vm.sp - 1
	vm.stack[p] = toPropertyKey(vm.stack[p])
	vm.pc++
}

type _toString struct{}

func (_toString) exec(vm *vm) {
	p := vm.sp - 1
	vm.stack[p] = vm.stack[p].toString()
	vm.pc++
}

type _getElemRef struct{}

var getElemRef _getElemRef

func (_getElemRef) exec(vm *vm) {
	obj := vm.stack[vm.sp-2].ToObject(vm.r)
	propName := vm.stack[vm.sp-1]
	vm.refStack = append(vm.refStack, &objRef{
		base: obj,
		name: propName,
	})
	vm.sp -= 2
	vm.pc++
}

type _getElemRefRecv struct{}

var getElemRefRecv _getElemRefRecv

func (_getElemRefRecv) exec(vm *vm) {
	obj := vm.stack[vm.sp-1].ToObject(vm.r)
	propName := vm.stack[vm.sp-2]
	vm.refStack = append(vm.refStack, &objRef{
		base: obj,
		name: propName,
		this: vm.stack[vm.sp-3],
	})
	vm.sp -= 3
	vm.pc++
}

type _getElemRefStrict struct{}

var getElemRefStrict _getElemRefStrict

func (_getElemRefStrict) exec(vm *vm) {
	obj := vm.stack[vm.sp-2].ToObject(vm.r)
	propName := vm.stack[vm.sp-1]
	vm.refStack = append(vm.refStack, &objRef{
		base:   obj,
		name:   propName,
		strict: true,
	})
	vm.sp -= 2
	vm.pc++
}

type _getElemRefRecvStrict struct{}

var getElemRefRecvStrict _getElemRefRecvStrict

func (_getElemRefRecvStrict) exec(vm *vm) {
	obj := vm.stack[vm.sp-1].ToObject(vm.r)
	propName := vm.stack[vm.sp-2]
	vm.refStack = append(vm.refStack, &objRef{
		base:   obj,
		name:   propName,
		this:   vm.stack[vm.sp-3],
		strict: true,
	})
	vm.sp -= 3
	vm.pc++
}

type _setElem struct{}

var setElem _setElem

func (_setElem) exec(vm *vm) {
	obj := vm.stack[vm.sp-3].ToObject(vm.r)
	propName := toPropertyKey(vm.stack[vm.sp-2])
	val := vm.stack[vm.sp-1]

	obj.setOwn(propName, val, false)

	vm.sp -= 2
	vm.stack[vm.sp-1] = val
	vm.pc++
}

type _setElem1 struct{}

var setElem1 _setElem1

func (_setElem1) exec(vm *vm) {
	obj := vm.stack[vm.sp-3].ToObject(vm.r)
	propName := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]

	obj.setOwn(propName, val, true)

	vm.sp -= 2
	vm.pc++
}

type _setElem1Named struct{}

var setElem1Named _setElem1Named

func (_setElem1Named) exec(vm *vm) {
	receiver := vm.stack[vm.sp-3]
	base := receiver.ToObject(vm.r)
	propName := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	vm.r.toObject(val).self.defineOwnPropertyStr("name", PropertyDescriptor{
		Value:        funcName("", propName),
		Configurable: FLAG_TRUE,
	}, true)
	base.set(propName, val, receiver, true)

	vm.sp -= 2
	vm.pc++
}

type defineMethod struct {
	enumerable bool
}

func (d *defineMethod) exec(vm *vm) {
	obj := vm.r.toObject(vm.stack[vm.sp-3])
	propName := vm.stack[vm.sp-2]
	method := vm.r.toObject(vm.stack[vm.sp-1])
	method.self.defineOwnPropertyStr("name", PropertyDescriptor{
		Value:        funcName("", propName),
		Configurable: FLAG_TRUE,
	}, true)
	obj.defineOwnProperty(propName, PropertyDescriptor{
		Value:        method,
		Writable:     FLAG_TRUE,
		Configurable: FLAG_TRUE,
		Enumerable:   ToFlag(d.enumerable),
	}, true)

	vm.sp -= 2
	vm.pc++
}

type _setElemP struct{}

var setElemP _setElemP

func (_setElemP) exec(vm *vm) {
	obj := vm.stack[vm.sp-3].ToObject(vm.r)
	propName := toPropertyKey(vm.stack[vm.sp-2])
	val := vm.stack[vm.sp-1]

	obj.setOwn(propName, val, false)

	vm.sp -= 3
	vm.pc++
}

type _setElemStrict struct{}

var setElemStrict _setElemStrict

func (_setElemStrict) exec(vm *vm) {
	propName := toPropertyKey(vm.stack[vm.sp-2])
	receiver := vm.stack[vm.sp-3]
	val := vm.stack[vm.sp-1]
	if receiverObj, ok := receiver.(*Object); ok {
		receiverObj.setOwn(propName, val, true)
	} else {
		base := receiver.ToObject(vm.r)
		base.set(propName, val, receiver, true)
	}

	vm.sp -= 2
	vm.stack[vm.sp-1] = val
	vm.pc++
}

type _setElemRecv struct{}

var setElemRecv _setElemRecv

func (_setElemRecv) exec(vm *vm) {
	receiver := vm.stack[vm.sp-4]
	propName := toPropertyKey(vm.stack[vm.sp-3])
	o := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	if obj, ok := o.(*Object); ok {
		obj.set(propName, val, receiver, false)
	} else {
		base := o.ToObject(vm.r)
		base.set(propName, val, receiver, false)
	}

	vm.sp -= 3
	vm.stack[vm.sp-1] = val
	vm.pc++
}

type _setElemRecvStrict struct{}

var setElemRecvStrict _setElemRecvStrict

func (_setElemRecvStrict) exec(vm *vm) {
	receiver := vm.stack[vm.sp-4]
	propName := toPropertyKey(vm.stack[vm.sp-3])
	o := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	if obj, ok := o.(*Object); ok {
		obj.set(propName, val, receiver, true)
	} else {
		base := o.ToObject(vm.r)
		base.set(propName, val, receiver, true)
	}

	vm.sp -= 3
	vm.stack[vm.sp-1] = val
	vm.pc++
}

type _setElemStrictP struct{}

var setElemStrictP _setElemStrictP

func (_setElemStrictP) exec(vm *vm) {
	propName := toPropertyKey(vm.stack[vm.sp-2])
	receiver := vm.stack[vm.sp-3]
	val := vm.stack[vm.sp-1]
	if receiverObj, ok := receiver.(*Object); ok {
		receiverObj.setOwn(propName, val, true)
	} else {
		base := receiver.ToObject(vm.r)
		base.set(propName, val, receiver, true)
	}

	vm.sp -= 3
	vm.pc++
}

type _setElemRecvP struct{}

var setElemRecvP _setElemRecvP

func (_setElemRecvP) exec(vm *vm) {
	receiver := vm.stack[vm.sp-4]
	propName := toPropertyKey(vm.stack[vm.sp-3])
	o := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	if obj, ok := o.(*Object); ok {
		obj.set(propName, val, receiver, false)
	} else {
		base := o.ToObject(vm.r)
		base.set(propName, val, receiver, false)
	}

	vm.sp -= 4
	vm.pc++
}

type _setElemRecvStrictP struct{}

var setElemRecvStrictP _setElemRecvStrictP

func (_setElemRecvStrictP) exec(vm *vm) {
	receiver := vm.stack[vm.sp-4]
	propName := toPropertyKey(vm.stack[vm.sp-3])
	o := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	if obj, ok := o.(*Object); ok {
		obj.set(propName, val, receiver, true)
	} else {
		base := o.ToObject(vm.r)
		base.set(propName, val, receiver, true)
	}

	vm.sp -= 4
	vm.pc++
}

type _deleteElem struct{}

var deleteElem _deleteElem

func (_deleteElem) exec(vm *vm) {
	obj := vm.stack[vm.sp-2].ToObject(vm.r)
	propName := toPropertyKey(vm.stack[vm.sp-1])
	if obj.delete(propName, false) {
		vm.stack[vm.sp-2] = valueTrue
	} else {
		vm.stack[vm.sp-2] = valueFalse
	}
	vm.sp--
	vm.pc++
}

type _deleteElemStrict struct{}

var deleteElemStrict _deleteElemStrict

func (_deleteElemStrict) exec(vm *vm) {
	obj := vm.stack[vm.sp-2].ToObject(vm.r)
	propName := toPropertyKey(vm.stack[vm.sp-1])
	obj.delete(propName, true)
	vm.stack[vm.sp-2] = valueTrue
	vm.sp--
	vm.pc++
}

type deleteProp unistring.String

func (d deleteProp) exec(vm *vm) {
	obj := vm.stack[vm.sp-1].ToObject(vm.r)
	if obj.self.deleteStr(unistring.String(d), false) {
		vm.stack[vm.sp-1] = valueTrue
	} else {
		vm.stack[vm.sp-1] = valueFalse
	}
	vm.pc++
}

type deletePropStrict unistring.String

func (d deletePropStrict) exec(vm *vm) {
	obj := vm.stack[vm.sp-1].ToObject(vm.r)
	obj.self.deleteStr(unistring.String(d), true)
	vm.stack[vm.sp-1] = valueTrue
	vm.pc++
}

type getPropRef unistring.String

func (p getPropRef) exec(vm *vm) {
	vm.refStack = append(vm.refStack, &objStrRef{
		base: vm.stack[vm.sp-1].ToObject(vm.r),
		name: unistring.String(p),
	})
	vm.sp--
	vm.pc++
}

type getPropRefRecv unistring.String

func (p getPropRefRecv) exec(vm *vm) {
	vm.refStack = append(vm.refStack, &objStrRef{
		this: vm.stack[vm.sp-2],
		base: vm.stack[vm.sp-1].ToObject(vm.r),
		name: unistring.String(p),
	})
	vm.sp -= 2
	vm.pc++
}

type getPropRefStrict unistring.String

func (p getPropRefStrict) exec(vm *vm) {
	vm.refStack = append(vm.refStack, &objStrRef{
		base:   vm.stack[vm.sp-1].ToObject(vm.r),
		name:   unistring.String(p),
		strict: true,
	})
	vm.sp--
	vm.pc++
}

type getPropRefRecvStrict unistring.String

func (p getPropRefRecvStrict) exec(vm *vm) {
	vm.refStack = append(vm.refStack, &objStrRef{
		this:   vm.stack[vm.sp-2],
		base:   vm.stack[vm.sp-1].ToObject(vm.r),
		name:   unistring.String(p),
		strict: true,
	})
	vm.sp -= 2
	vm.pc++
}

type setProp unistring.String

func (p setProp) exec(vm *vm) {
	val := vm.stack[vm.sp-1]
	vm.stack[vm.sp-2].ToObject(vm.r).self.setOwnStr(unistring.String(p), val, false)
	vm.stack[vm.sp-2] = val
	vm.sp--
	vm.pc++
}

type setPropP unistring.String

func (p setPropP) exec(vm *vm) {
	val := vm.stack[vm.sp-1]
	vm.stack[vm.sp-2].ToObject(vm.r).self.setOwnStr(unistring.String(p), val, false)
	vm.sp -= 2
	vm.pc++
}

type setPropStrict unistring.String

func (p setPropStrict) exec(vm *vm) {
	receiver := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	propName := unistring.String(p)
	if receiverObj, ok := receiver.(*Object); ok {
		receiverObj.self.setOwnStr(propName, val, true)
	} else {
		base := receiver.ToObject(vm.r)
		base.setStr(propName, val, receiver, true)
	}

	vm.stack[vm.sp-2] = val
	vm.sp--
	vm.pc++
}

type setPropRecv unistring.String

func (p setPropRecv) exec(vm *vm) {
	receiver := vm.stack[vm.sp-3]
	o := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	propName := unistring.String(p)
	if obj, ok := o.(*Object); ok {
		obj.setStr(propName, val, receiver, false)
	} else {
		base := o.ToObject(vm.r)
		base.setStr(propName, val, receiver, false)
	}

	vm.stack[vm.sp-3] = val
	vm.sp -= 2
	vm.pc++
}

type setPropRecvStrict unistring.String

func (p setPropRecvStrict) exec(vm *vm) {
	receiver := vm.stack[vm.sp-3]
	o := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	propName := unistring.String(p)
	if obj, ok := o.(*Object); ok {
		obj.setStr(propName, val, receiver, true)
	} else {
		base := o.ToObject(vm.r)
		base.setStr(propName, val, receiver, true)
	}

	vm.stack[vm.sp-3] = val
	vm.sp -= 2
	vm.pc++
}

type setPropRecvP unistring.String

func (p setPropRecvP) exec(vm *vm) {
	receiver := vm.stack[vm.sp-3]
	o := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	propName := unistring.String(p)
	if obj, ok := o.(*Object); ok {
		obj.setStr(propName, val, receiver, false)
	} else {
		base := o.ToObject(vm.r)
		base.setStr(propName, val, receiver, false)
	}

	vm.sp -= 3
	vm.pc++
}

type setPropRecvStrictP unistring.String

func (p setPropRecvStrictP) exec(vm *vm) {
	receiver := vm.stack[vm.sp-3]
	o := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	propName := unistring.String(p)
	if obj, ok := o.(*Object); ok {
		obj.setStr(propName, val, receiver, true)
	} else {
		base := o.ToObject(vm.r)
		base.setStr(propName, val, receiver, true)
	}

	vm.sp -= 3
	vm.pc++
}

type setPropStrictP unistring.String

func (p setPropStrictP) exec(vm *vm) {
	receiver := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	propName := unistring.String(p)
	if receiverObj, ok := receiver.(*Object); ok {
		receiverObj.self.setOwnStr(propName, val, true)
	} else {
		base := receiver.ToObject(vm.r)
		base.setStr(propName, val, receiver, true)
	}

	vm.sp -= 2
	vm.pc++
}

type putProp unistring.String

func (p putProp) exec(vm *vm) {
	vm.r.toObject(vm.stack[vm.sp-2]).self._putProp(unistring.String(p), vm.stack[vm.sp-1], true, true, true)
	vm.sp--
	vm.pc++
}

// used in class declarations instead of putProp because DefineProperty must be observable by Proxy
type definePropKeyed unistring.String

func (p definePropKeyed) exec(vm *vm) {
	vm.r.toObject(vm.stack[vm.sp-2]).self.defineOwnPropertyStr(unistring.String(p), PropertyDescriptor{
		Value:        vm.stack[vm.sp-1],
		Writable:     FLAG_TRUE,
		Configurable: FLAG_TRUE,
		Enumerable:   FLAG_TRUE,
	}, true)

	vm.sp--
	vm.pc++
}

type defineProp struct{}

func (defineProp) exec(vm *vm) {
	vm.r.toObject(vm.stack[vm.sp-3]).defineOwnProperty(vm.stack[vm.sp-2], PropertyDescriptor{
		Value:        vm.stack[vm.sp-1],
		Writable:     FLAG_TRUE,
		Configurable: FLAG_TRUE,
		Enumerable:   FLAG_TRUE,
	}, true)

	vm.sp -= 2
	vm.pc++
}

type defineMethodKeyed struct {
	key        unistring.String
	enumerable bool
}

func (d *defineMethodKeyed) exec(vm *vm) {
	obj := vm.r.toObject(vm.stack[vm.sp-2])
	method := vm.r.toObject(vm.stack[vm.sp-1])

	obj.self.defineOwnPropertyStr(d.key, PropertyDescriptor{
		Value:        method,
		Writable:     FLAG_TRUE,
		Configurable: FLAG_TRUE,
		Enumerable:   ToFlag(d.enumerable),
	}, true)

	vm.sp--
	vm.pc++
}

type _setProto struct{}

var setProto _setProto

func (_setProto) exec(vm *vm) {
	vm.r.setObjectProto(vm.stack[vm.sp-2], vm.stack[vm.sp-1])

	vm.sp--
	vm.pc++
}

type defineGetterKeyed struct {
	key        unistring.String
	enumerable bool
}

func (s *defineGetterKeyed) exec(vm *vm) {
	obj := vm.r.toObject(vm.stack[vm.sp-2])
	val := vm.stack[vm.sp-1]
	method := vm.r.toObject(val)
	method.self.defineOwnPropertyStr("name", PropertyDescriptor{
		Value:        asciiString("get ").Concat(stringValueFromRaw(s.key)),
		Configurable: FLAG_TRUE,
	}, true)
	descr := PropertyDescriptor{
		Getter:       val,
		Configurable: FLAG_TRUE,
		Enumerable:   ToFlag(s.enumerable),
	}

	obj.self.defineOwnPropertyStr(s.key, descr, true)

	vm.sp--
	vm.pc++
}

type defineSetterKeyed struct {
	key        unistring.String
	enumerable bool
}

func (s *defineSetterKeyed) exec(vm *vm) {
	obj := vm.r.toObject(vm.stack[vm.sp-2])
	val := vm.stack[vm.sp-1]
	method := vm.r.toObject(val)
	method.self.defineOwnPropertyStr("name", PropertyDescriptor{
		Value:        asciiString("set ").Concat(stringValueFromRaw(s.key)),
		Configurable: FLAG_TRUE,
	}, true)

	descr := PropertyDescriptor{
		Setter:       val,
		Configurable: FLAG_TRUE,
		Enumerable:   ToFlag(s.enumerable),
	}

	obj.self.defineOwnPropertyStr(s.key, descr, true)

	vm.sp--
	vm.pc++
}

type defineGetter struct {
	enumerable bool
}

func (s *defineGetter) exec(vm *vm) {
	obj := vm.r.toObject(vm.stack[vm.sp-3])
	propName := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	method := vm.r.toObject(val)
	method.self.defineOwnPropertyStr("name", PropertyDescriptor{
		Value:        funcName("get ", propName),
		Configurable: FLAG_TRUE,
	}, true)

	descr := PropertyDescriptor{
		Getter:       val,
		Configurable: FLAG_TRUE,
		Enumerable:   ToFlag(s.enumerable),
	}

	obj.defineOwnProperty(propName, descr, true)

	vm.sp -= 2
	vm.pc++
}

type defineSetter struct {
	enumerable bool
}

func (s *defineSetter) exec(vm *vm) {
	obj := vm.r.toObject(vm.stack[vm.sp-3])
	propName := vm.stack[vm.sp-2]
	val := vm.stack[vm.sp-1]
	method := vm.r.toObject(val)

	method.self.defineOwnPropertyStr("name", PropertyDescriptor{
		Value:        funcName("set ", propName),
		Configurable: FLAG_TRUE,
	}, true)

	descr := PropertyDescriptor{
		Setter:       val,
		Configurable: FLAG_TRUE,
		Enumerable:   FLAG_TRUE,
	}

	obj.defineOwnProperty(propName, descr, true)

	vm.sp -= 2
	vm.pc++
}

type getProp unistring.String

func (g getProp) exec(vm *vm) {
	v := vm.stack[vm.sp-1]
	obj := v.baseObject(vm.r)
	if obj == nil {
		vm.throw(vm.r.NewTypeError("Cannot read property '%s' of undefined", g))
		return
	}
	vm.stack[vm.sp-1] = nilSafe(obj.self.getStr(unistring.String(g), v))

	vm.pc++
}

type getPropRecv unistring.String

func (g getPropRecv) exec(vm *vm) {
	recv := vm.stack[vm.sp-2]
	v := vm.stack[vm.sp-1]
	obj := v.baseObject(vm.r)
	if obj == nil {
		vm.throw(vm.r.NewTypeError("Cannot read property '%s' of undefined", g))
		return
	}
	vm.stack[vm.sp-2] = nilSafe(obj.self.getStr(unistring.String(g), recv))
	vm.sp--
	vm.pc++
}

type getPropRecvCallee unistring.String

func (g getPropRecvCallee) exec(vm *vm) {
	recv := vm.stack[vm.sp-2]
	v := vm.stack[vm.sp-1]
	obj := v.baseObject(vm.r)
	if obj == nil {
		vm.throw(vm.r.NewTypeError("Cannot read property '%s' of undefined", g))
		return
	}

	n := unistring.String(g)
	prop := obj.self.getStr(n, recv)
	if prop == nil {
		prop = memberUnresolved{valueUnresolved{r: vm.r, ref: n}}
	}

	vm.stack[vm.sp-1] = prop
	vm.pc++
}

type getPropCallee unistring.String

func (g getPropCallee) exec(vm *vm) {
	v := vm.stack[vm.sp-1]
	n := unistring.String(g)
	if v == nil {
		vm.throw(vm.r.NewTypeError("Cannot read property '%s' of undefined or null", n))
		return
	}
	obj := v.baseObject(vm.r)
	if obj == nil {
		vm.throw(vm.r.NewTypeError("Cannot read property '%s' of undefined or null", n))
		return
	}
	prop := obj.self.getStr(n, v)
	if prop == nil {
		prop = memberUnresolved{valueUnresolved{r: vm.r, ref: n}}
	}
	vm.push(prop)

	vm.pc++
}

type _getElem struct{}

var getElem _getElem

func (_getElem) exec(vm *vm) {
	v := vm.stack[vm.sp-2]
	obj := v.baseObject(vm.r)
	if obj == nil {
		vm.throw(vm.r.NewTypeError("Cannot read property '%s' of undefined", vm.stack[vm.sp-1]))
		return
	}
	propName := toPropertyKey(vm.stack[vm.sp-1])

	vm.stack[vm.sp-2] = nilSafe(obj.get(propName, v))

	vm.sp--
	vm.pc++
}

type _getElemRecv struct{}

var getElemRecv _getElemRecv

func (_getElemRecv) exec(vm *vm) {
	recv := vm.stack[vm.sp-3]
	v := vm.stack[vm.sp-1]
	obj := v.baseObject(vm.r)
	if obj == nil {
		vm.throw(vm.r.NewTypeError("Cannot read property '%s' of undefined", vm.stack[vm.sp-2]))
		return
	}
	propName := toPropertyKey(vm.stack[vm.sp-2])

	vm.stack[vm.sp-3] = nilSafe(obj.get(propName, recv))

	vm.sp -= 2
	vm.pc++
}

type _getKey struct{}

var getKey _getKey

func (_getKey) exec(vm *vm) {
	v := vm.stack[vm.sp-2]
	obj := v.baseObject(vm.r)
	propName := vm.stack[vm.sp-1]
	if obj == nil {
		vm.throw(vm.r.NewTypeError("Cannot read property '%s' of undefined", propName.String()))
		return
	}

	vm.stack[vm.sp-2] = nilSafe(obj.get(propName, v))

	vm.sp--
	vm.pc++
}

type _getElemCallee struct{}

var getElemCallee _getElemCallee

func (_getElemCallee) exec(vm *vm) {
	v := vm.stack[vm.sp-2]
	obj := v.baseObject(vm.r)
	if obj == nil {
		vm.throw(vm.r.NewTypeError("Cannot read property '%s' of undefined", vm.stack[vm.sp-1]))
		return
	}

	propName := toPropertyKey(vm.stack[vm.sp-1])
	prop := obj.get(propName, v)
	if prop == nil {
		prop = memberUnresolved{valueUnresolved{r: vm.r, ref: propName.string()}}
	}
	vm.stack[vm.sp-1] = prop

	vm.pc++
}

type _getElemRecvCallee struct{}

var getElemRecvCallee _getElemRecvCallee

func (_getElemRecvCallee) exec(vm *vm) {
	recv := vm.stack[vm.sp-3]
	v := vm.stack[vm.sp-2]
	obj := v.baseObject(vm.r)
	if obj == nil {
		vm.throw(vm.r.NewTypeError("Cannot read property '%s' of undefined", vm.stack[vm.sp-1]))
		return
	}

	propName := toPropertyKey(vm.stack[vm.sp-1])
	prop := obj.get(propName, recv)
	if prop == nil {
		prop = memberUnresolved{valueUnresolved{r: vm.r, ref: propName.string()}}
	}
	vm.stack[vm.sp-2] = prop
	vm.sp--

	vm.pc++
}

type _dup struct{}

var dup _dup

func (_dup) exec(vm *vm) {
	vm.push(vm.stack[vm.sp-1])
	vm.pc++
}

type dupN uint32

func (d dupN) exec(vm *vm) {
	vm.push(vm.stack[vm.sp-1-int(d)])
	vm.pc++
}

type rdupN uint32

func (d rdupN) exec(vm *vm) {
	vm.stack[vm.sp-1-int(d)] = vm.stack[vm.sp-1]
	vm.pc++
}

type dupLast uint32

func (d dupLast) exec(vm *vm) {
	e := vm.sp + int(d)
	vm.stack.expand(e)
	copy(vm.stack[vm.sp:e], vm.stack[vm.sp-int(d):])
	vm.sp = e
	vm.pc++
}

type _newObject struct{}

var newObject _newObject

func (_newObject) exec(vm *vm) {
	vm.push(vm.r.NewObject())
	vm.pc++
}

type newArray uint32

func (l newArray) exec(vm *vm) {
	values := make([]Value, 0, l)
	vm.push(vm.r.newArrayValues(values))
	vm.pc++
}

type _pushArrayItem struct{}

var pushArrayItem _pushArrayItem

func (_pushArrayItem) exec(vm *vm) {
	arr := vm.stack[vm.sp-2].(*Object).self.(*arrayObject)
	if arr.length < math.MaxUint32 {
		arr.length++
	} else {
		vm.throw(vm.r.newError(vm.r.getRangeError(), "Invalid array length"))
		return
	}
	val := vm.stack[vm.sp-1]
	arr.values = append(arr.values, val)
	if val != nil {
		arr.objCount++
	}
	vm.sp--
	vm.pc++
}

type _pushArraySpread struct{}

var pushArraySpread _pushArraySpread

func (_pushArraySpread) exec(vm *vm) {
	arr := vm.stack[vm.sp-2].(*Object).self.(*arrayObject)
	vm.r.getIterator(vm.stack[vm.sp-1], nil).iterate(func(val Value) {
		if arr.length < math.MaxUint32 {
			arr.length++
		} else {
			vm.throw(vm.r.newError(vm.r.getRangeError(), "Invalid array length"))
			return
		}
		arr.values = append(arr.values, val)
		arr.objCount++
	})
	vm.sp--
	vm.pc++
}

type _pushSpread struct{}

var pushSpread _pushSpread

func (_pushSpread) exec(vm *vm) {
	vm.sp--
	obj := vm.stack[vm.sp]
	vm.r.getIterator(obj, nil).iterate(func(val Value) {
		vm.push(val)
	})
	vm.pc++
}

type _newArrayFromIter struct{}

var newArrayFromIter _newArrayFromIter

func (_newArrayFromIter) exec(vm *vm) {
	var values []Value
	l := len(vm.iterStack) - 1
	iter := vm.iterStack[l].iter
	vm.iterStack[l] = iterStackItem{}
	vm.iterStack = vm.iterStack[:l]
	if iter.iterator != nil {
		iter.iterate(func(val Value) {
			values = append(values, val)
		})
	}
	vm.push(vm.r.newArrayValues(values))
	vm.pc++
}

type newRegexp struct {
	pattern *regexpPattern
	src     String
}

func (n *newRegexp) exec(vm *vm) {
	vm.push(vm.r.newRegExpp(n.pattern.clone(), n.src, vm.r.getRegExpPrototype()).val)
	vm.pc++
}

func (vm *vm) setLocalLex(s int) {
	v := vm.stack[vm.sp-1]
	level := s >> 24
	idx := uint32(s & 0x00FFFFFF)
	stash := vm.stash
	for i := 0; i < level; i++ {
		stash = stash.outer
	}
	p := &stash.values[idx]
	if *p == nil {
		panic(errAccessBeforeInit)
	}
	*p = v
	vm.pc++
}

func (vm *vm) initLocal(s int) {
	v := vm.stack[vm.sp-1]
	level := s >> 24
	idx := uint32(s & 0x00FFFFFF)
	stash := vm.stash
	for i := 0; i < level; i++ {
		stash = stash.outer
	}
	stash.initByIdx(idx, v)
	vm.pc++
}

type storeStash uint32

func (s storeStash) exec(vm *vm) {
	vm.initLocal(int(s))
}

type storeStashP uint32

func (s storeStashP) exec(vm *vm) {
	vm.initLocal(int(s))
	vm.sp--
}

type storeStashLex uint32

func (s storeStashLex) exec(vm *vm) {
	vm.setLocalLex(int(s))
}

type storeStashLexP uint32

func (s storeStashLexP) exec(vm *vm) {
	vm.setLocalLex(int(s))
	vm.sp--
}

type initStash uint32

func (s initStash) exec(vm *vm) {
	vm.initLocal(int(s))
}

type initIndirect struct {
	idx    uint32
	getter func(vm *vm) Value
}

func (s initIndirect) exec(vm *vm) {
	level := int(s.idx) >> 24
	idx := uint32(s.idx & 0x00FFFFFF)
	stash := vm.stash
	for i := 0; i < level; i++ {
		stash = stash.outer
	}
	stash.initByIdx(idx, vm.r.ToValue(s.getter))
	vm.pc++
}

type initStashP uint32

func (s initStashP) exec(vm *vm) {
	vm.initLocal(int(s))
	vm.sp--
}

type initGlobalP unistring.String

func (s initGlobalP) exec(vm *vm) {
	vm.sp--
	vm.r.global.stash.initByName(unistring.String(s), vm.stack[vm.sp])
	vm.pc++
}

type initGlobal unistring.String

func (s initGlobal) exec(vm *vm) {
	vm.r.global.stash.initByName(unistring.String(s), vm.stack[vm.sp])
	vm.pc++
}

type resolveVar1 unistring.String

func (s resolveVar1) exec(vm *vm) {
	name := unistring.String(s)
	var ref ref
	for stash := vm.stash; stash != nil; stash = stash.outer {
		ref = stash.getRefByName(name, false)
		if ref != nil {
			goto end
		}
	}

	ref = &objStrRef{
		base:    vm.r.globalObject,
		name:    name,
		binding: true,
	}

end:
	vm.refStack = append(vm.refStack, ref)
	vm.pc++
}

type deleteVar unistring.String

func (d deleteVar) exec(vm *vm) {
	name := unistring.String(d)
	ret := true
	for stash := vm.stash; stash != nil; stash = stash.outer {
		if stash.obj != nil {
			if stashObjHas(stash.obj, name) {
				ret = stash.obj.self.deleteStr(name, false)
				goto end
			}
		} else {
			if idx, exists := stash.names[name]; exists {
				if idx&(maskVar|maskDeletable) == maskVar|maskDeletable {
					stash.deleteBinding(name)
				} else {
					ret = false
				}
				goto end
			}
		}
	}

	if vm.r.globalObject.self.hasPropertyStr(name) {
		ret = vm.r.globalObject.self.deleteStr(name, false)
	}

end:
	if ret {
		vm.push(valueTrue)
	} else {
		vm.push(valueFalse)
	}
	vm.pc++
}

type deleteGlobal unistring.String

func (d deleteGlobal) exec(vm *vm) {
	name := unistring.String(d)
	var ret bool
	if vm.r.globalObject.self.hasPropertyStr(name) {
		ret = vm.r.globalObject.self.deleteStr(name, false)
	} else {
		ret = true
	}
	if ret {
		vm.push(valueTrue)
	} else {
		vm.push(valueFalse)
	}
	vm.pc++
}

type resolveVar1Strict unistring.String

func (s resolveVar1Strict) exec(vm *vm) {
	name := unistring.String(s)
	var ref ref
	for stash := vm.stash; stash != nil; stash = stash.outer {
		ref = stash.getRefByName(name, true)
		if ref != nil {
			goto end
		}
	}

	if vm.r.globalObject.self.hasPropertyStr(name) {
		ref = &objStrRef{
			base:    vm.r.globalObject,
			name:    name,
			binding: true,
			strict:  true,
		}
		goto end
	}

	ref = &unresolvedRef{
		runtime: vm.r,
		name:    name,
	}

end:
	vm.refStack = append(vm.refStack, ref)
	vm.pc++
}

type setGlobal unistring.String

func (s setGlobal) exec(vm *vm) {
	vm.r.setGlobal(unistring.String(s), vm.peek(), false)
	vm.pc++
}

type setGlobalStrict unistring.String

func (s setGlobalStrict) exec(vm *vm) {
	vm.r.setGlobal(unistring.String(s), vm.peek(), true)
	vm.pc++
}

// Load a var indirectly from another module
type loadIndirect func(vm *vm) Value

func (g loadIndirect) exec(vm *vm) {
	v := nilSafe(g(vm))
	vm.push(v)
	vm.pc++
}

// Load a var from stash
type loadStash uint32

func (g loadStash) exec(vm *vm) {
	level := int(g >> 24)
	idx := uint32(g & 0x00FFFFFF)
	stash := vm.stash
	for i := 0; i < level; i++ {
		stash = stash.outer
	}

	vm.push(nilSafe(stash.getByIdx(idx)))
	vm.pc++
}

// Load a lexical binding from stash
type loadStashLex uint32

func (g loadStashLex) exec(vm *vm) {
	level := int(g >> 24)
	idx := uint32(g & 0x00FFFFFF)
	stash := vm.stash
	for i := 0; i < level; i++ {
		stash = stash.outer
	}

	v := stash.getByIdx(idx)
	if v == nil {
		if debugCompiler {
			srcName := ""
			if vm.prg != nil && vm.prg.src != nil {
				srcName = vm.prg.src.Name()
			}
			if debugCompiler {
				fmt.Printf("[LOADSTASHLEX-TDZ] level=%d, idx=%d, stashLen=%d, pc=%d, src=%s\n",
				level, idx, len(stash.values), vm.pc, srcName)
			}
			if stash.names != nil {
				for name, sidx := range stash.names {
					if debugCompiler {
						fmt.Printf("[LOADSTASHLEX-TDZ]   stash name=%s idx=%d\n", name, sidx)
					}
				}
			}
		}
		vm.throw(errAccessBeforeInit)
		return
	}
	vm.push(v)
	vm.pc++
}

// scan dynamic stashes up to the given level (encoded as 8 most significant bits of idx), if not found
// return the indexed var binding value from stash
type loadMixed struct {
	name   unistring.String
	idx    uint32
	callee bool
}

func (g *loadMixed) exec(vm *vm) {
	level := int(g.idx >> 24)
	idx := g.idx & 0x00FFFFFF
	stash := vm.stash
	name := g.name
	for i := 0; i < level; i++ {
		if v, found := stash.getByName(name); found {
			if g.callee {
				if stash.obj != nil {
					vm.push(stash.obj)
				} else {
					vm.push(_undefined)
				}
			}
			vm.push(v)
			goto end
		}
		stash = stash.outer
	}
	if g.callee {
		vm.push(_undefined)
	}
	if stash != nil {
		vm.push(nilSafe(stash.getByIdx(idx)))
	}
end:
	vm.pc++
}

// scan dynamic stashes up to the given level (encoded as 8 most significant bits of idx), if not found
// return the indexed lexical binding value from stash
type loadMixedLex loadMixed

func (g *loadMixedLex) exec(vm *vm) {
	level := int(g.idx >> 24)
	idx := g.idx & 0x00FFFFFF
	stash := vm.stash
	name := g.name
	for i := 0; i < level; i++ {
		if v, found := stash.getByName(name); found {
			if g.callee {
				if stash.obj != nil {
					vm.push(stash.obj)
				} else {
					vm.push(_undefined)
				}
			}
			vm.push(v)
			goto end
		}
		stash = stash.outer
	}
	if g.callee {
		vm.push(_undefined)
	}
	if stash != nil {
		v := stash.getByIdx(idx)
		if v == nil {
			if vm != nil && vm.debugMode {
				// In debug mode, return undefined instead of throwing TDZ error
				// This handles function parameters and variables not yet initialized
				v = _undefined
			} else {
				vm.throw(errAccessBeforeInit)
				return
			}
		}
		vm.push(v)
	}
end:
	vm.pc++
}

// scan dynamic stashes up to the given level (encoded as 8 most significant bits of idx), if not found
// return the indexed var binding value from stack
type loadMixedStack struct {
	name   unistring.String
	idx    int
	level  uint8
	callee bool
}

// same as loadMixedStack, but the args have been moved to stash (therefore stack layout is different)
type loadMixedStack1 loadMixedStack

func (g *loadMixedStack) exec(vm *vm) {
	stash := vm.stash
	name := g.name
	level := int(g.level)
	for i := 0; i < level; i++ {
		if v, found := stash.getByName(name); found {
			if g.callee {
				if stash.obj != nil {
					vm.push(stash.obj)
				} else {
					vm.push(_undefined)
				}
			}
			vm.push(v)
			goto end
		}
		stash = stash.outer
	}
	if g.callee {
		vm.push(_undefined)
	}
	loadStack(g.idx).exec(vm)
	return
end:
	vm.pc++
}

func (g *loadMixedStack1) exec(vm *vm) {
	stash := vm.stash
	name := g.name
	level := int(g.level)
	for i := 0; i < level; i++ {
		if v, found := stash.getByName(name); found {
			if g.callee {
				if stash.obj != nil {
					vm.push(stash.obj)
				} else {
					vm.push(_undefined)
				}
			}
			vm.push(v)
			goto end
		}
		stash = stash.outer
	}
	if g.callee {
		vm.push(_undefined)
	}
	loadStack1(g.idx).exec(vm)
	return
end:
	vm.pc++
}

type loadMixedStackLex loadMixedStack

// same as loadMixedStackLex but when the arguments have been moved into stash
type loadMixedStack1Lex loadMixedStack

func (g *loadMixedStackLex) exec(vm *vm) {
	stash := vm.stash
	name := g.name
	level := int(g.level)
	for i := 0; i < level; i++ {
		if v, found := stash.getByName(name); found {
			if g.callee {
				if stash.obj != nil {
					vm.push(stash.obj)
				} else {
					vm.push(_undefined)
				}
			}
			vm.push(v)
			goto end
		}
		stash = stash.outer
	}
	if g.callee {
		vm.push(_undefined)
	}
	loadStackLex(g.idx).exec(vm)
	return
end:
	vm.pc++
}

func (g *loadMixedStack1Lex) exec(vm *vm) {
	stash := vm.stash
	name := g.name
	level := int(g.level)
	for i := 0; i < level; i++ {
		if v, found := stash.getByName(name); found {
			if g.callee {
				if stash.obj != nil {
					vm.push(stash.obj)
				} else {
					vm.push(_undefined)
				}
			}
			vm.push(v)
			goto end
		}
		stash = stash.outer
	}
	if g.callee {
		vm.push(_undefined)
	}
	loadStack1Lex(g.idx).exec(vm)
	return
end:
	vm.pc++
}

type resolveMixed struct {
	name   unistring.String
	idx    uint32
	typ    varType
	strict bool
}

func newStashRef(typ varType, name unistring.String, v *[]Value, idx int, vm *vm) ref {
	switch typ {
	case varTypeVar:
		return &stashRef{
			n:   name,
			v:   v,
			idx: idx,
			vm:  vm,
		}
	case varTypeLet:
		return &stashRefLex{
			stashRef: stashRef{
				n:   name,
				v:   v,
				idx: idx,
				vm:  vm,
			},
		}
	case varTypeConst, varTypeStrictConst:
		return &stashRefConst{
			stashRefLex: stashRefLex{
				stashRef: stashRef{
					n:   name,
					v:   v,
					idx: idx,
					vm:  vm,
				},
			},
			strictConst: typ == varTypeStrictConst,
		}
	}
	panic("unsupported var type")
}

func (r *resolveMixed) exec(vm *vm) {
	level := int(r.idx >> 24)
	idx := r.idx & 0x00FFFFFF
	stash := vm.stash
	var ref ref
	for i := 0; i < level; i++ {
		ref = stash.getRefByName(r.name, r.strict)
		if ref != nil {
			goto end
		}
		stash = stash.outer
	}

	if stash != nil {
		ref = newStashRef(r.typ, r.name, &stash.values, int(idx), vm)
		goto end
	}

	ref = &unresolvedRef{
		runtime: vm.r,
		name:    r.name,
	}

end:
	vm.refStack = append(vm.refStack, ref)
	vm.pc++
}

type resolveMixedStack struct {
	name   unistring.String
	idx    int
	typ    varType
	level  uint8
	strict bool
}

type resolveMixedStack1 resolveMixedStack

func (r *resolveMixedStack) exec(vm *vm) {
	level := int(r.level)
	stash := vm.stash
	var ref ref
	var idx int
	for i := 0; i < level; i++ {
		ref = stash.getRefByName(r.name, r.strict)
		if ref != nil {
			goto end
		}
		stash = stash.outer
	}

	if r.idx > 0 {
		idx = vm.sb + vm.args + r.idx
	} else {
		idx = vm.sb - r.idx
	}

	ref = newStashRef(r.typ, r.name, (*[]Value)(&vm.stack), idx, vm)

end:
	vm.refStack = append(vm.refStack, ref)
	vm.pc++
}

func (r *resolveMixedStack1) exec(vm *vm) {
	level := int(r.level)
	stash := vm.stash
	var ref ref
	for i := 0; i < level; i++ {
		ref = stash.getRefByName(r.name, r.strict)
		if ref != nil {
			goto end
		}
		stash = stash.outer
	}

	ref = newStashRef(r.typ, r.name, (*[]Value)(&vm.stack), vm.sb+r.idx, vm)

end:
	vm.refStack = append(vm.refStack, ref)
	vm.pc++
}

type _getValue struct{}

var getValue _getValue

func (_getValue) exec(vm *vm) {
	ref := vm.refStack[len(vm.refStack)-1]
	vm.push(nilSafe(ref.get()))
	vm.pc++
}

type _putValue struct{}

var putValue _putValue

func (_putValue) exec(vm *vm) {
	l := len(vm.refStack) - 1
	ref := vm.refStack[l]
	vm.refStack[l] = nil
	vm.refStack = vm.refStack[:l]
	ref.set(vm.stack[vm.sp-1])
	vm.pc++
}

type _popRef struct{}

var popRef _popRef

func (_popRef) exec(vm *vm) {
	l := len(vm.refStack) - 1
	vm.refStack[l] = nil
	vm.refStack = vm.refStack[:l]
	vm.pc++
}

type _putValueP struct{}

var putValueP _putValueP

func (_putValueP) exec(vm *vm) {
	l := len(vm.refStack) - 1
	ref := vm.refStack[l]
	vm.refStack[l] = nil
	vm.refStack = vm.refStack[:l]
	ref.set(vm.stack[vm.sp-1])
	vm.sp--
	vm.pc++
}

type _initValueP struct{}

var initValueP _initValueP

func (_initValueP) exec(vm *vm) {
	l := len(vm.refStack) - 1
	ref := vm.refStack[l]
	vm.refStack[l] = nil
	vm.refStack = vm.refStack[:l]
	ref.init(vm.stack[vm.sp-1])
	vm.sp--
	vm.pc++
}

type loadDynamic unistring.String

func (n loadDynamic) exec(vm *vm) {
	name := unistring.String(n)
	var val Value
	for stash := vm.stash; stash != nil; stash = stash.outer {
		if v, exists := stash.getByName(name); exists {
			val = v
			break
		}
	}
	if val == nil {
		val = vm.r.globalObject.self.getStr(name, nil)
		if val == nil {
			vm.throw(vm.r.newReferenceError(name))
			return
		}
	}
	vm.push(val)
	vm.pc++
}

type loadDynamicRef unistring.String

func (n loadDynamicRef) exec(vm *vm) {
	name := unistring.String(n)
	var val Value
	for stash := vm.stash; stash != nil; stash = stash.outer {
		if v, exists := stash.getByName(name); exists {
			val = v
			break
		}
	}
	if val == nil {
		val = vm.r.globalObject.self.getStr(name, nil)
		if val == nil {
			val = valueUnresolved{r: vm.r, ref: name}
		}
	}
	vm.push(val)
	vm.pc++
}

type loadDynamicCallee unistring.String

func (n loadDynamicCallee) exec(vm *vm) {
	name := unistring.String(n)
	var val Value
	var callee *Object
	for stash := vm.stash; stash != nil; stash = stash.outer {
		if v, exists := stash.getByName(name); exists {
			callee = stash.obj
			val = v
			break
		}
	}
	if val == nil {
		val = vm.r.globalObject.self.getStr(name, nil)
		if val == nil {
			val = valueUnresolved{r: vm.r, ref: name}
		}
	}
	if callee != nil {
		vm.push(callee)
	} else {
		vm.push(_undefined)
	}
	vm.push(val)
	vm.pc++
}

type _pop struct{}

var pop _pop

func (_pop) exec(vm *vm) {
	vm.sp--
	vm.pc++
}

func (vm *vm) callEval(n int, strict bool) {
	if vm.r.toObject(vm.stack[vm.sp-n-1]) == vm.r.global.Eval {
		if n > 0 {
			srcVal := vm.stack[vm.sp-n]
			if src, ok := srcVal.(String); ok {
				ret := vm.r.eval(src, true, strict)
				vm.stack[vm.sp-n-2] = ret
			} else {
				vm.stack[vm.sp-n-2] = srcVal
			}
		} else {
			vm.stack[vm.sp-n-2] = _undefined
		}

		vm.sp -= n + 1
		vm.pc++
	} else {
		call(n).exec(vm)
	}
}

type callEval uint32

func (numargs callEval) exec(vm *vm) {
	vm.callEval(int(numargs), false)
}

type callEvalStrict uint32

func (numargs callEvalStrict) exec(vm *vm) {
	vm.callEval(int(numargs), true)
}

type _callEvalVariadic struct{}

var callEvalVariadic _callEvalVariadic

func (_callEvalVariadic) exec(vm *vm) {
	vm.callEval(vm.countVariadicArgs()-2, false)
}

type _callEvalVariadicStrict struct{}

var callEvalVariadicStrict _callEvalVariadicStrict

func (_callEvalVariadicStrict) exec(vm *vm) {
	vm.callEval(vm.countVariadicArgs()-2, true)
}

type _boxThis struct{}

var boxThis _boxThis

func (_boxThis) exec(vm *vm) {
	v := vm.stack[vm.sb]
	if v == _undefined || v == _null {
		vm.stack[vm.sb] = vm.r.globalObject
	} else {
		vm.stack[vm.sb] = v.ToObject(vm.r)
	}
	vm.pc++
}

var variadicMarker Value = newSymbol(asciiString("[variadic marker]"))

type _startVariadic struct{}

var startVariadic _startVariadic

func (_startVariadic) exec(vm *vm) {
	vm.push(variadicMarker)
	vm.pc++
}

type _callVariadic struct{}

var callVariadic _callVariadic

func (vm *vm) countVariadicArgs() int {
	count := 0
	for i := vm.sp - 1; i >= 0; i-- {
		if vm.stack[i] == variadicMarker {
			return count
		}
		count++
	}
	panic("Variadic marker was not found. Compiler bug.")
}

func (_callVariadic) exec(vm *vm) {
	call(vm.countVariadicArgs() - 2).exec(vm)
}

type _endVariadic struct{}

var endVariadic _endVariadic

func (_endVariadic) exec(vm *vm) {
	vm.sp--
	vm.stack[vm.sp-1] = vm.stack[vm.sp]
	vm.pc++
}

type call uint32

func (numargs call) exec(vm *vm) {
	// this
	// callee
	// arg0
	// ...
	// arg<numargs-1>
	n := int(numargs)
	v := vm.stack[vm.sp-n-1] // callee
	obj := vm.toCallee(v)

	// DEBUG: Log when calling a non-function object in debug mode
	if vm.debugMode {
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
				obj.String(), obj.self, posFile, posLine, vm.pc, n)
			}
			// Print the bytecode around the call site
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
					marker := " "
					if i == vm.pc {
						marker = ">"
					}
					if debugVM {
						fmt.Printf("[CALL-DEBUG] %s [%d] %T\n", marker, i, vm.prg.code[i])
					}
				}
			}
		}
	}

	obj.self.vmCall(vm, n)
}

func (vm *vm) clearStack() {
	sp := vm.sp
	if sp > len(vm.stack) {
		// Clamp sp to prevent out-of-range panic - this indicates a VM bug
		if debugVM {
			fmt.Printf("[VM] ⚠️ clearStack: sp=%d > len(stack)=%d, clamping to stack length\n", sp, len(vm.stack))
		}
		sp = len(vm.stack)
	}
	stackTail := vm.stack[sp:]
	for i := range stackTail {
		stackTail[i] = nil
	}
	vm.stack = vm.stack[:sp]
}

type enterBlock struct {
	names     map[unistring.String]uint32
	stashSize uint32
	stackSize uint32
	needStash bool // set by compiler in debug mode for empty scopes
}

func (e *enterBlock) exec(vm *vm) {
	// Create stash if we have either stash size or names to track
	if e.stashSize > 0 || len(e.names) > 0 {
		if vm != nil && vm.debugMode {
			if e.stashSize > 0 || len(e.names) > 0 {
				vm.newStash()
				if e.stashSize > 0 {
					vm.stash.values = make([]Value, e.stashSize)
				}
				if len(e.names) > 0 {
					// Create a copy of the names map
					vm.stash.names = make(map[unistring.String]uint32, len(e.names))
					for k, v := range e.names {
						vm.stash.names[k] = v
					}
				}
			}
		} else {
			if e.stashSize > 0 {
				vm.newStash()
				vm.stash.values = make([]Value, e.stashSize)
				if len(e.names) > 0 {
					vm.stash.names = e.names
				}
			}
		}
	} else if e.needStash {
		// In debug mode, the compiler counts ALL scopes as stash
		// levels (via sc.c.debug in finaliseVarAlloc level loop). The runtime must
		// create a stash for every scope to match, even empty ones. Without this,
		// loadStashLex reads from the wrong stash level.
		// Only applies to code compiled in debug mode (needStash is set by compiler).
		vm.newStash()
	}
	ss := int(e.stackSize)
	vm.stack.expand(vm.sp + ss - 1)
	vv := vm.stack[vm.sp : vm.sp+ss]
	for i := range vv {
		vv[i] = nil
	}
	vm.sp += ss
	vm.pc++
}

type enterCatchBlock struct {
	names     map[unistring.String]uint32
	stashSize uint32
	stackSize uint32
}

func (e *enterCatchBlock) exec(vm *vm) {
	vm.newStash()
	vm.stash.values = make([]Value, e.stashSize)
	if len(e.names) > 0 {
		if vm != nil && vm.debugMode {
			// Create a copy of the names map instead of sharing it
			vm.stash.names = make(map[unistring.String]uint32, len(e.names))
			for k, v := range e.names {
				vm.stash.names[k] = v
			}
		} else {
			vm.stash.names = e.names
		}
	}
	vm.sp--
	vm.stash.values[0] = vm.stack[vm.sp]
	ss := int(e.stackSize)
	vm.stack.expand(vm.sp + ss - 1)
	vv := vm.stack[vm.sp : vm.sp+ss]
	for i := range vv {
		vv[i] = nil
	}
	vm.sp += ss
	vm.pc++
}

type leaveBlock struct {
	stackSize uint32
	popStash  bool
}

func (l *leaveBlock) exec(vm *vm) {
	if l.popStash {
		vm.stash = vm.stash.outer
	}
	if ss := l.stackSize; ss > 0 {
		vm.sp -= int(ss)
	}
	vm.pc++
}

type enterFunc struct {
	names       map[unistring.String]uint32
	stashSize   uint32
	stackSize   uint32
	numArgs     uint32
	funcType    funcType
	argsToStash bool
	extensible  bool
}

func (e *enterFunc) exec(vm *vm) {
	// Input stack:
	//
	// callee
	// this
	// arg0
	// ...
	// argN
	// <- sp

	// Output stack:
	//
	// this <- sb
	// <local stack vars...>
	// <- sp

	sp := vm.sp
	vm.sb = sp - vm.args - 1
	vm.newStash()
	stash := vm.stash
	stash.funcType = e.funcType
	stash.values = make([]Value, e.stashSize)
	if len(e.names) > 0 {
		if e.extensible {
			m := make(map[unistring.String]uint32, len(e.names))
			for name, idx := range e.names {
				m[name] = idx
			}
			stash.names = m
		} else {
			if vm != nil && vm.debugMode {
				// Create a copy of the names map instead of sharing it
				vm.stash.names = make(map[unistring.String]uint32, len(e.names))
				for k, v := range e.names {
					vm.stash.names[k] = v
				}
			} else {
				vm.stash.names = e.names
			}
		}
	}
	ss := int(e.stackSize)
	ea := 0
	if e.argsToStash {
		offset := vm.args - int(e.numArgs)
		copy(stash.values, vm.stack[sp-vm.args:sp])
		if offset > 0 {
			vm.stash.extraArgs = make([]Value, offset)
			copy(stash.extraArgs, vm.stack[sp-offset:])
		} else {
			vv := stash.values[vm.args:e.numArgs]
			for i := range vv {
				vv[i] = _undefined
			}
		}
		sp -= vm.args
	} else {
		d := int(e.numArgs) - vm.args
		if d > 0 {
			ss += d
			ea = d
			vm.args = int(e.numArgs)
		}
	}
	vm.stack.expand(sp + ss - 1)
	if ea > 0 {
		vv := vm.stack[sp : vm.sp+ea]
		for i := range vv {
			vv[i] = _undefined
		}
	}
	vv := vm.stack[sp+ea : sp+ss]
	for i := range vv {
		vv[i] = nil
	}
	vm.sp = sp + ss

	// DEBUG FIX: In debug mode, the compiler moves the " this" binding to stash
	// (allInStash=true rewrites loadStack→loadStash). But enterFunc only copies
	// args to stash (when argsToStash=true), NOT 'this' (which lives at vm.sb).
	// Without this, class methods see 'this' as undefined because the stash slot
	// is never initialized.
	if vm.debugMode && e.names != nil {
		if thisIdx, ok := e.names[unistring.String(thisBindingName)]; ok {
			idx := thisIdx & 0x00FFFFFF
			if int(idx) < len(stash.values) && stash.values[idx] == nil {
				stash.initByIdx(idx, vm.stack[vm.sb])
			}
		}
	}

	vm.pc++
}

// Similar to enterFunc, but for when arguments may be accessed before they are initialised,
// e.g. by an eval() code or from a closure, or from an earlier initialiser code.
// In this case the arguments remain on stack, first argsToCopy of them are copied to the stash.
type enterFunc1 struct {
	names      map[unistring.String]uint32
	stashSize  uint32
	numArgs    uint32
	argsToCopy uint32
	funcType   funcType
	extensible bool
}

func (e *enterFunc1) exec(vm *vm) {
	sp := vm.sp
	vm.sb = sp - vm.args - 1
	vm.newStash()
	stash := vm.stash
	stash.funcType = e.funcType
	stash.values = make([]Value, e.stashSize)
	if len(e.names) > 0 {
		if e.extensible {
			m := make(map[unistring.String]uint32, len(e.names))
			for name, idx := range e.names {
				m[name] = idx
			}
			stash.names = m
		} else {
			if vm != nil && vm.debugMode {
				// Create a copy of the names map instead of sharing it
				m := make(map[unistring.String]uint32, len(e.names))
				for name, idx := range e.names {
					m[name] = idx
				}
				stash.names = m
			} else {
				stash.names = e.names
			}
		}
	}
	offset := vm.args - int(e.argsToCopy)
	if offset > 0 {
		copy(stash.values, vm.stack[sp-vm.args:sp-offset])
		if offset := vm.args - int(e.numArgs); offset > 0 {
			vm.stash.extraArgs = make([]Value, offset)
			copy(stash.extraArgs, vm.stack[sp-offset:])
		}
	} else {
		copy(stash.values, vm.stack[sp-vm.args:sp])
		if int(e.argsToCopy) > vm.args {
			vv := stash.values[vm.args:e.argsToCopy]
			for i := range vv {
				vv[i] = _undefined
			}
		}
	}

	// DEBUG FIX: Same as enterFunc — copy 'this' from stack to stash in debug mode.
	if vm.debugMode && e.names != nil {
		if thisIdx, ok := e.names[unistring.String(thisBindingName)]; ok {
			idx := thisIdx & 0x00FFFFFF
			if int(idx) < len(stash.values) && stash.values[idx] == nil {
				stash.initByIdx(idx, vm.stack[vm.sb])
			}
		}
	}

	vm.pc++
}

// Finalises the initialisers section and starts the function body which has its own
// scope. When used in conjunction with enterFunc1 adjustStack is set to true which
// causes the arguments to be removed from the stack.
type enterFuncBody struct {
	names map[unistring.String]uint32
	enterBlock
	funcType    funcType
	extensible  bool
	adjustStack bool
}

func (e *enterFuncBody) exec(vm *vm) {
	if e.stashSize > 0 || e.extensible {
		vm.newStash()
		stash := vm.stash
		stash.funcType = e.funcType
		stash.values = make([]Value, e.stashSize)

		if len(e.names) > 0 {
			if e.extensible {
				m := make(map[unistring.String]uint32, len(e.names))
				for name, idx := range e.names {
					m[name] = idx
				}
				stash.names = m
			} else {
				if vm != nil && vm.debugMode {
					m := make(map[unistring.String]uint32, len(e.names))
					for name, idx := range e.names {
						m[name] = idx
					}
					stash.names = m
				} else {
					stash.names = e.names
				}
			}
		}
	}

	sp := vm.sp
	if e.adjustStack {
		sp -= vm.args
	}
	nsp := sp + int(e.stackSize)
	if e.stackSize > 0 {
		vm.stack.expand(nsp - 1)
		vv := vm.stack[sp:nsp]
		for i := range vv {
			vv[i] = nil
		}
	}
	vm.sp = nsp

	// DEBUG FIX: Same as enterFunc — copy 'this' from stack to stash in debug mode.
	if vm.debugMode && e.names != nil {
		stash := vm.stash
		if thisIdx, ok := e.names[unistring.String(thisBindingName)]; ok {
			idx := thisIdx & 0x00FFFFFF
			if int(idx) < len(stash.values) && stash.values[idx] == nil {
				stash.initByIdx(idx, vm.stack[vm.sb])
			}
		}
	}

	vm.pc++
}

type _ret struct{}

var ret _ret

func (_ret) exec(vm *vm) {
	// callee -3
	// this -2 <- sb
	// retval -1

	vm.stack[vm.sb-1] = vm.stack[vm.sp-1]
	vm.sp = vm.sb
	vm.popCtx()
	vm.pc++
}

type cret uint32

func (c cret) exec(vm *vm) {
	vm.stack[vm.sb] = *vm.getStashPtr(uint32(c))
	ret.exec(vm)
}

type enterFuncStashless struct {
	stackSize uint32
	args      uint32
}

func (e *enterFuncStashless) exec(vm *vm) {
	sp := vm.sp
	vm.sb = sp - vm.args - 1
	d := int(e.args) - vm.args
	if d > 0 {
		ss := sp + int(e.stackSize) + d
		vm.stack.expand(ss)
		vv := vm.stack[sp : sp+d]
		for i := range vv {
			vv[i] = _undefined
		}
		vv = vm.stack[sp+d : ss]
		for i := range vv {
			vv[i] = nil
		}
		vm.args = int(e.args)
		vm.sp = ss
	} else {
		if e.stackSize > 0 {
			ss := sp + int(e.stackSize)
			vm.stack.expand(ss)
			vv := vm.stack[sp:ss]
			for i := range vv {
				vv[i] = nil
			}
			vm.sp = ss
		}
	}
	vm.pc++
}

type newFuncInstruction interface {
	getPrg() *Program
}

type newFunc struct {
	prg    *Program
	name   unistring.String
	source string

	length int
	strict bool
}

func (n *newFunc) exec(vm *vm) {
	obj := vm.r.newFunc(n.name, n.length, n.strict)
	obj.prg = n.prg
	obj.stash = vm.stash
	obj.privEnv = vm.privEnv
	obj.src = n.source
	vm.push(obj.val)
	vm.pc++
}

func (n *newFunc) getPrg() *Program {
	return n.prg
}

type newAsyncFunc struct {
	newFunc
}

func (n *newAsyncFunc) exec(vm *vm) {
	obj := vm.r.newAsyncFunc(n.name, n.length, n.strict)
	obj.prg = n.prg
	obj.stash = vm.stash
	obj.privEnv = vm.privEnv
	obj.src = n.source
	vm.push(obj.val)
	vm.pc++
}

type loadModulePromise struct {
	moduleCore ModuleRecord
}

func (n *loadModulePromise) exec(vm *vm) {
	mi := vm.r.modules[n.moduleCore].(*SourceTextModuleInstance)
	vm.push(mi.pcap.promise)
	vm.pc++
}

type newModule struct {
	newAsyncFunc
	moduleCore ModuleRecord
}

func (n *newModule) exec(vm *vm) {
	obj := vm.r.newAsyncFunc(n.name, n.length, n.strict)
	obj.prg = n.prg
	obj.stash = vm.stash
	obj.privEnv = vm.privEnv
	obj.src = n.source
	vm.push(obj.val)
	vm.pc++
}

type setModulePromise struct {
	moduleCore ModuleRecord
}

func (n *setModulePromise) exec(vm *vm) {
	mi := vm.r.modules[n.moduleCore].(*SourceTextModuleInstance)
	mi.asyncPromise = vm.pop().Export().(*Promise)
	vm.pc++
}

type newGeneratorFunc struct {
	newFunc
}

func (n *newGeneratorFunc) exec(vm *vm) {
	obj := vm.r.newGeneratorFunc(n.name, n.length, n.strict)
	obj.prg = n.prg
	obj.stash = vm.stash
	obj.privEnv = vm.privEnv
	obj.src = n.source
	vm.push(obj.val)
	vm.pc++
}

type newMethod struct {
	newFunc
	homeObjOffset uint32
}

func (n *newMethod) _exec(vm *vm, obj *methodFuncObject) {
	obj.prg = n.prg
	obj.stash = vm.stash
	obj.privEnv = vm.privEnv
	obj.src = n.source
	if n.homeObjOffset > 0 {
		obj.homeObject = vm.r.toObject(vm.stack[vm.sp-int(n.homeObjOffset)])
	}
	vm.push(obj.val)
	vm.pc++
}

func (n *newMethod) exec(vm *vm) {
	n._exec(vm, vm.r.newMethod(n.name, n.length, n.strict))
}

type newAsyncMethod struct {
	newMethod
}

func (n *newAsyncMethod) exec(vm *vm) {
	obj := vm.r.newAsyncMethod(n.name, n.length, n.strict)
	n._exec(vm, &obj.methodFuncObject)
}

type newGeneratorMethod struct {
	newMethod
}

func (n *newGeneratorMethod) exec(vm *vm) {
	obj := vm.r.newGeneratorMethod(n.name, n.length, n.strict)
	n._exec(vm, &obj.methodFuncObject)
}

type newArrowFunc struct {
	newFunc
}

type newAsyncArrowFunc struct {
	newArrowFunc
}

func getFuncObject(v Value) *Object {
	if o, ok := v.(*Object); ok {
		if fn, ok := o.self.(*arrowFuncObject); ok {
			return fn.funcObj
		}
		return o
	}
	if v == _undefined || v == _null {
		return nil
	}
	panic(typeError("Value is not an Object"))
}

func getHomeObject(v Value) *Object {
	if o, ok := v.(*Object); ok {
		switch fn := o.self.(type) {
		case *methodFuncObject:
			return fn.homeObject
		case *generatorMethodFuncObject:
			return fn.homeObject
		case *asyncMethodFuncObject:
			return fn.homeObject
		case *classFuncObject:
			return o.runtime.toObject(fn.getStr("prototype", nil))
		case *arrowFuncObject:
			return getHomeObject(fn.funcObj)
		case *asyncArrowFuncObject:
			return getHomeObject(fn.funcObj)
		}
	}
	panic(newTypeError("Compiler bug: getHomeObject() on the wrong value: %T", v))
}

func (n *newArrowFunc) _exec(vm *vm, obj *arrowFuncObject) {
	obj.prg = n.prg
	obj.stash = vm.stash
	obj.privEnv = vm.privEnv
	obj.src = n.source
	if vm.sb > 0 {
		obj.funcObj = getFuncObject(vm.stack[vm.sb-1])
	}
	vm.push(obj.val)
	vm.pc++
}

type runtimeSyntaxError string

func (a runtimeSyntaxError) exec(vm *vm) {
	panic(vm.r.newError(vm.r.getSyntaxError(), (string)(a)))
}

func (n *newArrowFunc) exec(vm *vm) {
	n._exec(vm, vm.r.newArrowFunc(n.name, n.length, n.strict))
}

func (n *newAsyncArrowFunc) exec(vm *vm) {
	obj := vm.r.newAsyncArrowFunc(n.name, n.length, n.strict)
	n._exec(vm, &obj.arrowFuncObject)
}

func (vm *vm) alreadyDeclared(name unistring.String) Value {
	return vm.r.newError(vm.r.getSyntaxError(), "Identifier '%s' has already been declared", name)
}

func (vm *vm) checkBindVarsGlobal(names []unistring.String) {
	o := vm.r.globalObject.self
	sn := vm.r.global.stash.names
	if bo, ok := o.(*baseObject); ok {
		// shortcut
		if bo.extensible {
			for _, name := range names {
				if _, exists := sn[name]; exists {
					panic(vm.alreadyDeclared(name))
				}
			}
		} else {
			for _, name := range names {
				if !bo.hasOwnPropertyStr(name) {
					panic(vm.r.NewTypeError("Cannot define global variable '%s', global object is not extensible", name))
				}
				if _, exists := sn[name]; exists {
					panic(vm.alreadyDeclared(name))
				}
			}
		}
	} else {
		for _, name := range names {
			if !o.hasOwnPropertyStr(name) && !o.isExtensible() {
				panic(vm.r.NewTypeError("Cannot define global variable '%s', global object is not extensible", name))
			}
			if _, exists := sn[name]; exists {
				panic(vm.alreadyDeclared(name))
			}
		}
	}
}

func (vm *vm) createGlobalVarBindings(names []unistring.String, d bool) {
	o := vm.r.globalObject.self
	if bo, ok := o.(*templatedObject); ok {
		for _, name := range names {
			if !bo.hasOwnPropertyStr(name) && bo.extensible {
				bo._putProp(name, _undefined, true, true, d)
			}
		}
	} else {
		var cf Flag
		if d {
			cf = FLAG_TRUE
		} else {
			cf = FLAG_FALSE
		}
		for _, name := range names {
			if !o.hasOwnPropertyStr(name) && o.isExtensible() {
				o.defineOwnPropertyStr(name, PropertyDescriptor{
					Value:        _undefined,
					Writable:     FLAG_TRUE,
					Enumerable:   FLAG_TRUE,
					Configurable: cf,
				}, true)
				o.setOwnStr(name, _undefined, false)
			}
		}
	}
}

func (vm *vm) createGlobalFuncBindings(names []unistring.String, d bool) {
	o := vm.r.globalObject.self
	b := vm.sp - len(names)
	var shortcutObj *templatedObject
	if o, ok := o.(*templatedObject); ok {
		shortcutObj = o
	}
	for i, name := range names {
		var desc PropertyDescriptor
		prop := o.getOwnPropStr(name)
		desc.Value = vm.stack[b+i]
		if shortcutObj != nil && prop == nil && shortcutObj.extensible {
			shortcutObj._putProp(name, desc.Value, true, true, d)
		} else {
			if prop, ok := prop.(*valueProperty); ok && !prop.configurable {
				// no-op
			} else {
				desc.Writable = FLAG_TRUE
				desc.Enumerable = FLAG_TRUE
				if d {
					desc.Configurable = FLAG_TRUE
				} else {
					desc.Configurable = FLAG_FALSE
				}
			}
			if shortcutObj != nil {
				shortcutObj.defineOwnPropertyStr(name, desc, true)
			} else {
				o.defineOwnPropertyStr(name, desc, true)
				o.setOwnStr(name, desc.Value, false) // not a bug, see https://262.ecma-international.org/#sec-createglobalfunctionbinding
			}
		}
	}
	vm.sp = b
}

func (vm *vm) checkBindFuncsGlobal(names []unistring.String) {
	o := vm.r.globalObject.self
	sn := vm.r.global.stash.names
	for _, name := range names {
		if _, exists := sn[name]; exists {
			panic(vm.alreadyDeclared(name))
		}
		prop := o.getOwnPropStr(name)
		allowed := true
		switch prop := prop.(type) {
		case nil:
			allowed = o.isExtensible()
		case *valueProperty:
			allowed = prop.configurable || prop.getterFunc == nil && prop.setterFunc == nil && prop.writable && prop.enumerable
		}
		if !allowed {
			panic(vm.r.NewTypeError("Cannot redefine global function '%s'", name))
		}
	}
}

func (vm *vm) checkBindLexGlobal(names []unistring.String) {
	o := vm.r.globalObject.self
	s := &vm.r.global.stash
	for _, name := range names {
		if _, exists := s.names[name]; exists {
			goto fail
		}
		if prop, ok := o.getOwnPropStr(name).(*valueProperty); ok && !prop.configurable {
			goto fail
		}
		continue
	fail:
		panic(vm.alreadyDeclared(name))
	}
}

type bindVars struct {
	names     []unistring.String
	deletable bool
}

func (d *bindVars) exec(vm *vm) {
	var target *stash
	for _, name := range d.names {
		for s := vm.stash; s != nil; s = s.outer {
			if idx, exists := s.names[name]; exists && idx&maskVar == 0 {
				vm.throw(vm.alreadyDeclared(name))
				return
			}
			if s.isVariable() {
				target = s
				break
			}
		}
	}
	if target == nil {
		target = vm.stash
	}
	deletable := d.deletable
	for _, name := range d.names {
		target.createBinding(name, deletable)
	}
	vm.pc++
}

type bindGlobal struct {
	vars, funcs, lets, consts []unistring.String

	deletable bool
}

func (b *bindGlobal) exec(vm *vm) {
	vm.checkBindFuncsGlobal(b.funcs)
	vm.checkBindLexGlobal(b.lets)
	vm.checkBindLexGlobal(b.consts)
	vm.checkBindVarsGlobal(b.vars)

	s := &vm.r.global.stash
	for _, name := range b.lets {
		s.createLexBinding(name, false)
	}
	for _, name := range b.consts {
		s.createLexBinding(name, true)
	}
	vm.createGlobalFuncBindings(b.funcs, b.deletable)
	vm.createGlobalVarBindings(b.vars, b.deletable)
	vm.pc++
}

type jneP int32

func (j jneP) exec(vm *vm) {
	vm.sp--
	if !vm.stack[vm.sp].ToBoolean() {
		vm.pc += int(j)
	} else {
		vm.pc++
	}
}

type jeqP int32

func (j jeqP) exec(vm *vm) {
	vm.sp--
	if vm.stack[vm.sp].ToBoolean() {
		vm.pc += int(j)
	} else {
		vm.pc++
	}
}

type jeq int32

func (j jeq) exec(vm *vm) {
	if vm.stack[vm.sp-1].ToBoolean() {
		vm.pc += int(j)
	} else {
		vm.sp--
		vm.pc++
	}
}

type jne int32

func (j jne) exec(vm *vm) {
	if !vm.stack[vm.sp-1].ToBoolean() {
		vm.pc += int(j)
	} else {
		vm.sp--
		vm.pc++
	}
}

type jdef int32

func (j jdef) exec(vm *vm) {
	if vm.stack[vm.sp-1] != _undefined {
		vm.pc += int(j)
	} else {
		vm.sp--
		vm.pc++
	}
}

type jdefP int32

func (j jdefP) exec(vm *vm) {
	if vm.stack[vm.sp-1] != _undefined {
		vm.pc += int(j)
	} else {
		vm.pc++
	}
	vm.sp--
}

type jopt int32

func (j jopt) exec(vm *vm) {
	switch vm.stack[vm.sp-1] {
	case _null:
		vm.stack[vm.sp-1] = _undefined
		fallthrough
	case _undefined:
		vm.pc += int(j)
	default:
		vm.pc++
	}
}

type joptc int32

func (j joptc) exec(vm *vm) {
	switch vm.stack[vm.sp-1].(type) {
	case valueNull, valueUndefined, memberUnresolved:
		vm.sp--
		vm.stack[vm.sp-1] = _undefined
		vm.pc += int(j)
	default:
		vm.pc++
	}
}

type joptdel int32

func (j joptdel) exec(vm *vm) {
	switch vm.stack[vm.sp-1].(type) {
	case valueNull, valueUndefined:
		vm.stack[vm.sp-1] = valueTrue
		vm.pc += int(j)
	default:
		vm.pc++
	}
}

type joptdelc int32

func (j joptdelc) exec(vm *vm) {
	switch vm.stack[vm.sp-1].(type) {
	case valueNull, valueUndefined, memberUnresolved:
		vm.sp--
		vm.stack[vm.sp-1] = valueTrue
		vm.pc += int(j)
	default:
		vm.pc++
	}
}

type joptdelP int32

func (j joptdelP) exec(vm *vm) {
	switch vm.stack[vm.sp-1].(type) {
	case valueNull, valueUndefined:
		vm.sp--
		vm.pc += int(j)
	default:
		vm.pc++
	}
}

type joptdelcP int32

func (j joptdelcP) exec(vm *vm) {
	switch vm.stack[vm.sp-1].(type) {
	case valueNull, valueUndefined, memberUnresolved:
		vm.sp -= 2
		vm.pc += int(j)
	default:
		vm.pc++
	}
}

type jcoalesc int32

func (j jcoalesc) exec(vm *vm) {
	switch vm.stack[vm.sp-1] {
	case _undefined, _null:
		vm.sp--
		vm.pc++
	default:
		vm.pc += int(j)
	}
}

type jcoalescP int32

func (j jcoalescP) exec(vm *vm) {
	vm.sp--
	switch vm.stack[vm.sp] {
	case _undefined, _null:
		vm.pc++
	default:
		vm.pc += int(j)
	}
}

type _not struct{}

var not _not

func (_not) exec(vm *vm) {
	if vm.stack[vm.sp-1].ToBoolean() {
		vm.stack[vm.sp-1] = valueFalse
	} else {
		vm.stack[vm.sp-1] = valueTrue
	}
	vm.pc++
}

func toPrimitiveNumber(v Value) Value {
	if o, ok := v.(*Object); ok {
		return o.toPrimitiveNumber()
	}
	return v
}

func toPrimitive(v Value) Value {
	if o, ok := v.(*Object); ok {
		return o.toPrimitive()
	}
	return v
}

func cmp(px, py Value) Value {
	var ret bool
	xs, isPxString := px.(String)
	ys, isPyString := py.(String)

	if isPxString && isPyString {
		ret = xs.CompareTo(ys) < 0
		goto end
	} else {
		if px, ok := px.(*valueBigInt); ok && isPyString {
			ny, err := stringToBigInt(ys.toTrimmedUTF8())
			if err != nil {
				return _undefined
			}
			ret = (*big.Int)(px).Cmp(ny) < 0
			goto end
		}
		if py, ok := py.(*valueBigInt); ok && isPxString {
			nx, err := stringToBigInt(xs.toTrimmedUTF8())
			if err != nil {
				return _undefined
			}
			ret = nx.Cmp((*big.Int)(py)) < 0
			goto end
		}
	}

	px = toNumeric(px)
	py = toNumeric(py)

	switch nx := px.(type) {
	case valueInt:
		switch ny := py.(type) {
		case valueInt:
			ret = nx < ny
			goto end
		case *valueBigInt:
			ret = big.NewInt(int64(nx)).Cmp((*big.Int)(ny)) < 0
			goto end
		}
	case valueFloat:
		switch ny := py.(type) {
		case *valueBigInt:
			switch {
			case math.IsNaN(float64(nx)):
				return _undefined
			case nx == _negativeInf:
				ret = true
				goto end
			}
			if nx := big.NewFloat(float64(nx)); nx.IsInt() {
				nx, _ := nx.Int(nil)
				ret = nx.Cmp((*big.Int)(ny)) < 0
			} else {
				ret = nx.Cmp(new(big.Float).SetInt((*big.Int)(ny))) < 0
			}
			goto end
		}
	case *valueBigInt:
		switch ny := py.(type) {
		case valueInt:
			ret = (*big.Int)(nx).Cmp(big.NewInt(int64(ny))) < 0
			goto end
		case valueFloat:
			switch {
			case math.IsNaN(float64(ny)):
				return _undefined
			case ny == _positiveInf:
				ret = true
				goto end
			}
			if ny := big.NewFloat(float64(ny)); ny.IsInt() {
				ny, _ := ny.Int(nil)
				ret = (*big.Int)(nx).Cmp(ny) < 0
			} else {
				ret = new(big.Float).SetInt((*big.Int)(nx)).Cmp(ny) < 0
			}
			goto end
		case *valueBigInt:
			ret = (*big.Int)(nx).Cmp((*big.Int)(ny)) < 0
			goto end
		}
	}

	if nx, ny := px.ToFloat(), py.ToFloat(); math.IsNaN(nx) || math.IsNaN(ny) {
		return _undefined
	} else {
		ret = nx < ny
	}

end:
	if ret {
		return valueTrue
	}
	return valueFalse
}

type _op_lt struct{}

var op_lt _op_lt

func (_op_lt) exec(vm *vm) {
	left := toPrimitiveNumber(vm.stack[vm.sp-2])
	right := toPrimitiveNumber(vm.stack[vm.sp-1])

	r := cmp(left, right)
	if r == _undefined {
		vm.stack[vm.sp-2] = valueFalse
	} else {
		vm.stack[vm.sp-2] = r
	}
	vm.sp--
	vm.pc++
}

type _op_lte struct{}

var op_lte _op_lte

func (_op_lte) exec(vm *vm) {
	left := toPrimitiveNumber(vm.stack[vm.sp-2])
	right := toPrimitiveNumber(vm.stack[vm.sp-1])

	r := cmp(right, left)
	if r == _undefined || r == valueTrue {
		vm.stack[vm.sp-2] = valueFalse
	} else {
		vm.stack[vm.sp-2] = valueTrue
	}

	vm.sp--
	vm.pc++
}

type _op_gt struct{}

var op_gt _op_gt

func (_op_gt) exec(vm *vm) {
	left := toPrimitiveNumber(vm.stack[vm.sp-2])
	right := toPrimitiveNumber(vm.stack[vm.sp-1])

	r := cmp(right, left)
	if r == _undefined {
		vm.stack[vm.sp-2] = valueFalse
	} else {
		vm.stack[vm.sp-2] = r
	}
	vm.sp--
	vm.pc++
}

type _op_gte struct{}

var op_gte _op_gte

func (_op_gte) exec(vm *vm) {
	left := toPrimitiveNumber(vm.stack[vm.sp-2])
	right := toPrimitiveNumber(vm.stack[vm.sp-1])

	r := cmp(left, right)
	if r == _undefined || r == valueTrue {
		vm.stack[vm.sp-2] = valueFalse
	} else {
		vm.stack[vm.sp-2] = valueTrue
	}

	vm.sp--
	vm.pc++
}

type _op_eq struct{}

var op_eq _op_eq

func (_op_eq) exec(vm *vm) {
	if vm.stack[vm.sp-2].Equals(vm.stack[vm.sp-1]) {
		vm.stack[vm.sp-2] = valueTrue
	} else {
		vm.stack[vm.sp-2] = valueFalse
	}
	vm.sp--
	vm.pc++
}

type _op_neq struct{}

var op_neq _op_neq

func (_op_neq) exec(vm *vm) {
	if vm.stack[vm.sp-2].Equals(vm.stack[vm.sp-1]) {
		vm.stack[vm.sp-2] = valueFalse
	} else {
		vm.stack[vm.sp-2] = valueTrue
	}
	vm.sp--
	vm.pc++
}

type _op_strict_eq struct{}

var op_strict_eq _op_strict_eq

func (_op_strict_eq) exec(vm *vm) {
	if vm.stack[vm.sp-2].StrictEquals(vm.stack[vm.sp-1]) {
		vm.stack[vm.sp-2] = valueTrue
	} else {
		vm.stack[vm.sp-2] = valueFalse
	}
	vm.sp--
	vm.pc++
}

type _op_strict_neq struct{}

var op_strict_neq _op_strict_neq

func (_op_strict_neq) exec(vm *vm) {
	if vm.stack[vm.sp-2].StrictEquals(vm.stack[vm.sp-1]) {
		vm.stack[vm.sp-2] = valueFalse
	} else {
		vm.stack[vm.sp-2] = valueTrue
	}
	vm.sp--
	vm.pc++
}

type _op_instanceof struct{}

var op_instanceof _op_instanceof

func (_op_instanceof) exec(vm *vm) {
	left := vm.stack[vm.sp-2]
	right := vm.r.toObject(vm.stack[vm.sp-1])

	if instanceOfOperator(left, right) {
		vm.stack[vm.sp-2] = valueTrue
	} else {
		vm.stack[vm.sp-2] = valueFalse
	}

	vm.sp--
	vm.pc++
}

type _op_in struct{}

var op_in _op_in

func (_op_in) exec(vm *vm) {
	left := vm.stack[vm.sp-2]
	right := vm.r.toObject(vm.stack[vm.sp-1])

	if right.hasProperty(left) {
		vm.stack[vm.sp-2] = valueTrue
	} else {
		vm.stack[vm.sp-2] = valueFalse
	}

	vm.sp--
	vm.pc++
}

type try struct {
	catchOffset   int32
	finallyOffset int32
}

func (t try) exec(vm *vm) {
	var catchPos, finallyPos int32
	if t.catchOffset > 0 {
		catchPos = int32(vm.pc) + t.catchOffset
	} else {
		catchPos = -1
	}
	if t.finallyOffset > 0 {
		finallyPos = int32(vm.pc) + t.finallyOffset
	} else {
		finallyPos = -1
	}
	vm.pushTryFrame(catchPos, finallyPos)
	vm.pc++
}

type leaveTry struct{}

func (leaveTry) exec(vm *vm) {
	tf := &vm.tryStack[len(vm.tryStack)-1]
	if tf.finallyPos >= 0 {
		tf.finallyRet = int32(vm.pc + 1)
		vm.pc = int(tf.finallyPos)
		tf.finallyPos = -1
		tf.catchPos = -1
		vm.sp, vm.stash = int(tf.sp), tf.stash
	} else {
		vm.popTryFrame()
		vm.pc++
	}
}

type enterFinally struct{}

func (enterFinally) exec(vm *vm) {
	tf := &vm.tryStack[len(vm.tryStack)-1]
	tf.finallyPos = -1
	vm.pc++
}

type leaveFinally struct{}

func (leaveFinally) exec(vm *vm) {
	tf := &vm.tryStack[len(vm.tryStack)-1]
	ex, ret := tf.exception, tf.finallyRet
	tf.exception = nil
	vm.popTryFrame()
	if ex != nil {
		vm.throw(ex)
		return
	} else {
		if ret != -1 {
			vm.pc = int(ret)
		} else {
			vm.pc++
		}
	}
}

type _throw struct{}

var throw _throw

func (_throw) exec(vm *vm) {
	v := vm.stack[vm.sp-1]
	ex := &Exception{
		val: v,
	}

	if o, ok := v.(*Object); ok {
		if e, ok := o.self.(*errorObject); ok {
			if len(e.stack) > 0 {
				ex.stack = e.stack
			}
		}
	}

	if ex.stack == nil {
		ex.stack = vm.captureStack(make([]StackFrame, 0, len(vm.callStack)+1), 0)
	}

	if ex = vm.handleThrow(ex); ex != nil {
		panic(ex)
	}
}

type _newVariadic struct{}

var newVariadic _newVariadic

func (_newVariadic) exec(vm *vm) {
	_new(vm.countVariadicArgs() - 1).exec(vm)
}

type _new uint32

func (n _new) exec(vm *vm) {
	sp := vm.sp - int(n)
	obj := vm.stack[sp-1]
	ctor := vm.r.toConstructor(obj)
	vm.stack[sp-1] = ctor(vm.stack[sp:vm.sp], nil)
	vm.sp = sp
	vm.pc++
}

type superCall uint32

func (s superCall) exec(vm *vm) {
	l := len(vm.refStack) - 1
	thisRef := vm.refStack[l]
	vm.refStack[l] = nil
	vm.refStack = vm.refStack[:l]

	obj := vm.r.toObject(vm.stack[vm.sb-1])
	var cls *classFuncObject
	switch fn := obj.self.(type) {
	case *classFuncObject:
		cls = fn
	case *arrowFuncObject:
		cls, _ = fn.funcObj.self.(*classFuncObject)
	}
	if cls == nil {
		vm.throw(vm.r.NewTypeError("wrong callee type for super()"))
		return
	}
	sp := vm.sp - int(s)
	newTarget := vm.r.toObject(vm.newTarget)
	v := cls.createInstance(vm.stack[sp:vm.sp], newTarget)
	thisRef.set(v)
	vm.sp = sp
	cls._initFields(v)
	vm.push(v)
	vm.pc++
}

type _superCallVariadic struct{}

var superCallVariadic _superCallVariadic

func (_superCallVariadic) exec(vm *vm) {
	superCall(vm.countVariadicArgs()).exec(vm)
}

type _loadNewTarget struct{}

var loadNewTarget _loadNewTarget

func (_loadNewTarget) exec(vm *vm) {
	if t := vm.newTarget; t != nil {
		vm.push(t)
	} else {
		vm.push(_undefined)
	}
	vm.pc++
}

type _loadImportMeta struct{}

var loadImportMeta _loadImportMeta

func (_loadImportMeta) exec(vm *vm) {
	// https://262.ecma-international.org/13.0/#sec-meta-properties-runtime-semantics-evaluation
	t := vm.r.GetActiveScriptOrModule()
	m := t.(ModuleRecord) // There should be now way for this to have compiled
	vm.push(vm.r.getImportMetaFor(m))
	vm.pc++
}

type _loadDynamicImport struct{}

var dynamicImport _loadDynamicImport

func (_loadDynamicImport) exec(vm *vm) {
	// https://262.ecma-international.org/13.0/#sec-import-call-runtime-semantics-evaluation
	// NOTE(@mstoykov): it will be nice if we do not use vm.r.ToValue but write it directly
	vm.push(vm.r.ToValue(func(specifier Value) Value {
		t := vm.r.GetActiveScriptOrModule()

		pcap := vm.r.newPromiseCapability(vm.r.getPromise())
		var specifierStr String
		err := vm.r.try(func() {
			specifierStr = specifier.toString()
		})
		if err != nil {
			if ex, ok := err.(*Exception); ok {
				pcap.reject(vm.r.ToValue(ex.val))
			} else {
				pcap.reject(vm.r.ToValue(err))
			}
			return pcap.promise
		}
		if vm.r.importModuleDynamically == nil {
			pcap.reject(asciiString("dynamic modules not enabled in the host program"))
		} else {
			pcapInput := vm.r.newPromiseCapability(vm.r.getPromise())
			onFullfill := vm.r.ToValue(func(call FunctionCall) Value {
				pcap.resolve(call.Argument(0))
				return nil
			})
			rejectionClosure := vm.r.ToValue(func(call FunctionCall) Value {
				v := call.Argument(0)
				if v.ExportType() == reflect.TypeOf(&Exception{}) {
					v = v.Export().(*Exception).Value()
				}

				pcap.reject(v)
				return nil
			})
			vm.r.performPromiseThen(pcapInput.promise.Export().(*Promise), onFullfill, rejectionClosure, nil)
			vm.r.importModuleDynamically(t, specifierStr, pcapInput)
		}
		return pcap.promise
	}))
	vm.pc++
}

type _typeof struct{}

var typeof _typeof

func (_typeof) exec(vm *vm) {
	var r Value
	switch v := vm.stack[vm.sp-1].(type) {
	case valueUndefined, valueUnresolved:
		r = stringUndefined
	case valueNull:
		r = stringObjectC
	case *Object:
		r = v.self.typeOf()
	case valueBool:
		r = stringBoolean
	case String:
		r = stringString
	case valueInt, valueFloat:
		r = stringNumber
	case *valueBigInt:
		r = stringBigInt
	case *Symbol:
		r = stringSymbol
	default:
		panic(newTypeError("Compiler bug: unknown type: %T", v))
	}
	vm.stack[vm.sp-1] = r
	vm.pc++
}

type createArgsMapped uint32

func (formalArgs createArgsMapped) exec(vm *vm) {
	v := &Object{runtime: vm.r}
	args := &argumentsObject{}
	args.extensible = true
	args.prototype = vm.r.global.ObjectPrototype
	args.class = "Arguments"
	v.self = args
	args.val = v
	args.length = vm.args
	args.init()
	i := 0
	c := int(formalArgs)
	if vm.args < c {
		c = vm.args
	}
	for ; i < c; i++ {
		args._put(unistring.String(strconv.Itoa(i)), &mappedProperty{
			valueProperty: valueProperty{
				writable:     true,
				configurable: true,
				enumerable:   true,
			},
			v: &vm.stash.values[i],
		})
	}

	for _, v := range vm.stash.extraArgs {
		args._put(unistring.String(strconv.Itoa(i)), v)
		i++
	}

	args._putProp("callee", vm.stack[vm.sb-1], true, false, true)
	args._putSym(SymIterator, valueProp(vm.r.getArrayValues(), true, false, true))
	vm.push(v)
	vm.pc++
}

type createArgsUnmapped uint32

func (formalArgs createArgsUnmapped) exec(vm *vm) {
	args := vm.r.newBaseObject(vm.r.global.ObjectPrototype, "Arguments")
	i := 0
	c := int(formalArgs)
	if vm.args < c {
		c = vm.args
	}
	for _, v := range vm.stash.values[:c] {
		args._put(unistring.String(strconv.Itoa(i)), v)
		i++
	}

	for _, v := range vm.stash.extraArgs {
		args._put(unistring.String(strconv.Itoa(i)), v)
		i++
	}

	args._putProp("length", intToValue(int64(vm.args)), true, false, true)
	args._put("callee", vm.r.newThrowerProperty(false))
	args._putSym(SymIterator, valueProp(vm.r.getArrayValues(), true, false, true))
	vm.push(args.val)
	vm.pc++
}

type _enterWith struct{}

var enterWith _enterWith

func (_enterWith) exec(vm *vm) {
	vm.newStash()
	vm.stash.obj = vm.stack[vm.sp-1].ToObject(vm.r)
	vm.sp--
	vm.pc++
}

type _leaveWith struct{}

var leaveWith _leaveWith

func (_leaveWith) exec(vm *vm) {
	vm.stash = vm.stash.outer
	vm.pc++
}

func emptyIter() (propIterItem, iterNextFunc) {
	return propIterItem{}, nil
}

type _enumerate struct{}

var enumerate _enumerate

func (_enumerate) exec(vm *vm) {
	v := vm.stack[vm.sp-1]
	if v == _undefined || v == _null {
		vm.iterStack = append(vm.iterStack, iterStackItem{f: emptyIter})
	} else {
		vm.iterStack = append(vm.iterStack, iterStackItem{f: enumerateRecursive(v.ToObject(vm.r))})
	}
	vm.sp--
	vm.pc++
}

type enumNext int32

func (jmp enumNext) exec(vm *vm) {
	l := len(vm.iterStack) - 1
	item, n := vm.iterStack[l].f()
	if n != nil {
		vm.iterStack[l].val = item.name
		vm.iterStack[l].f = n
		vm.pc++
	} else {
		vm.pc += int(jmp)
	}
}

type _enumGet struct{}

var enumGet _enumGet

func (_enumGet) exec(vm *vm) {
	l := len(vm.iterStack) - 1
	vm.push(vm.iterStack[l].val)
	vm.pc++
}

type _enumPop struct{}

var enumPop _enumPop

func (_enumPop) exec(vm *vm) {
	l := len(vm.iterStack) - 1
	vm.iterStack[l] = iterStackItem{}
	vm.iterStack = vm.iterStack[:l]
	vm.pc++
}

type _enumPopClose struct{}

var enumPopClose _enumPopClose

func (_enumPopClose) exec(vm *vm) {
	l := len(vm.iterStack) - 1
	item := vm.iterStack[l]
	vm.iterStack[l] = iterStackItem{}
	vm.iterStack = vm.iterStack[:l]
	if iter := item.iter; iter != nil {
		iter.returnIter()
	}
	vm.pc++
}

type _iterateP struct{}

var iterateP _iterateP

func (_iterateP) exec(vm *vm) {
	iter := vm.r.getIterator(vm.stack[vm.sp-1], nil)
	vm.iterStack = append(vm.iterStack, iterStackItem{iter: iter})
	vm.sp--
	vm.pc++
}

type _iterate struct{}

var iterate _iterate

func (_iterate) exec(vm *vm) {
	iter := vm.r.getIterator(vm.stack[vm.sp-1], nil)
	vm.iterStack = append(vm.iterStack, iterStackItem{iter: iter})
	vm.pc++
}

type iterNext int32

func (jmp iterNext) exec(vm *vm) {
	l := len(vm.iterStack) - 1
	iter := vm.iterStack[l].iter
	value, ex := iter.step()
	if ex == nil {
		if value == nil {
			vm.pc += int(jmp)
		} else {
			vm.iterStack[l].val = value
			vm.pc++
		}
	} else {
		l := len(vm.iterStack) - 1
		vm.iterStack[l] = iterStackItem{}
		vm.iterStack = vm.iterStack[:l]
		vm.throw(ex.val)
		return
	}
}

type iterGetNextOrUndef struct{}

func (iterGetNextOrUndef) exec(vm *vm) {
	l := len(vm.iterStack) - 1
	iter := vm.iterStack[l].iter
	var value Value
	if iter.iterator != nil {
		var ex *Exception
		value, ex = iter.step()
		if ex != nil {
			l := len(vm.iterStack) - 1
			vm.iterStack[l] = iterStackItem{}
			vm.iterStack = vm.iterStack[:l]
			vm.throw(ex.val)
			return
		}
	}
	vm.push(nilSafe(value))
	vm.pc++
}

type copyStash struct{}

func (copyStash) exec(vm *vm) {
	oldStash := vm.stash
	newStash := &stash{
		outer: oldStash.outer,
	}
	vm.stashAllocs++
	newStash.values = append([]Value(nil), oldStash.values...)
	newStash.names = oldStash.names
	vm.stash = newStash
	vm.pc++
}

type _throwAssignToConst struct{}

var throwAssignToConst _throwAssignToConst

func (_throwAssignToConst) exec(vm *vm) {
	vm.throw(errAssignToConst)
}

func (r *Runtime) copyDataProperties(target, source Value) {
	targetObj := r.toObject(target)
	if source == _null || source == _undefined {
		return
	}
	sourceObj := source.ToObject(r)
	for item, next := iterateEnumerableProperties(sourceObj)(); next != nil; item, next = next() {
		createDataPropertyOrThrow(targetObj, item.name, item.value)
	}
}

type _copySpread struct{}

var copySpread _copySpread

func (_copySpread) exec(vm *vm) {
	vm.r.copyDataProperties(vm.stack[vm.sp-2], vm.stack[vm.sp-1])
	vm.sp--
	vm.pc++
}

type _copyRest struct{}

var copyRest _copyRest

func (_copyRest) exec(vm *vm) {
	vm.push(vm.r.NewObject())
	vm.r.copyDataProperties(vm.stack[vm.sp-1], vm.stack[vm.sp-2])
	vm.pc++
}

type _createDestructSrc struct{}

var createDestructSrc _createDestructSrc

func (_createDestructSrc) exec(vm *vm) {
	v := vm.stack[vm.sp-1]
	vm.r.checkObjectCoercible(v)
	vm.push(vm.r.newDestructKeyedSource(v))
	vm.pc++
}

type _checkObjectCoercible struct{}

var checkObjectCoercible _checkObjectCoercible

func (_checkObjectCoercible) exec(vm *vm) {
	vm.r.checkObjectCoercible(vm.stack[vm.sp-1])
	vm.pc++
}

type createArgsRestStack int

func (n createArgsRestStack) exec(vm *vm) {
	var values []Value
	delta := vm.args - int(n)
	if delta > 0 {
		values = make([]Value, delta)
		copy(values, vm.stack[vm.sb+int(n)+1:])
	}
	vm.push(vm.r.newArrayValues(values))
	vm.pc++
}

type _createArgsRestStash struct{}

var createArgsRestStash _createArgsRestStash

func (_createArgsRestStash) exec(vm *vm) {
	vm.push(vm.r.newArrayValues(vm.stash.extraArgs))
	vm.stash.extraArgs = nil
	vm.pc++
}

type concatStrings int

func (n concatStrings) exec(vm *vm) {
	low := vm.sp - int(n)
	if low < 0 || low > vm.sp || vm.sp > len(vm.stack) {
		panic(referenceError(fmt.Sprintf("internal: concatStrings stack underflow (sp=%d, n=%d, stackLen=%d)", vm.sp, int(n), len(vm.stack))))
	}
	strs := vm.stack[low:vm.sp]
	length := 0
	allAscii := true
	for i, s := range strs {
		switch s := s.(type) {
		case asciiString:
			length += s.Length()
		case unicodeString:
			length += s.Length()
			allAscii = false
		case *importedString:
			s.ensureScanned()
			if s.u != nil {
				strs[i] = s.u
				length += s.u.Length()
				allAscii = false
			} else {
				strs[i] = asciiString(s.s)
				length += len(s.s)
			}
		default:
			panic(unknownStringTypeErr(s))
		}
	}

	vm.sp -= int(n) - 1
	if allAscii {
		var buf strings.Builder
		buf.Grow(length)
		for _, s := range strs {
			buf.WriteString(string(s.(asciiString)))
		}
		vm.stack[vm.sp-1] = asciiString(buf.String())
	} else {
		var buf unicodeStringBuilder
		buf.Grow(length)
		for _, s := range strs {
			buf.writeString(s.(String))
		}
		vm.stack[vm.sp-1] = buf.String()
	}
	vm.pc++
}

type getTaggedTmplObject struct {
	raw, cooked []Value
}

// As tagged template objects are not cached (because it's hard to ensure the cache is cleaned without using
// finalizers) this wrapper is needed to override the equality method so that two objects for the same template
// literal appeared to be equal from the code's point of view.
type taggedTemplateArray struct {
	*arrayObject
	idPtr *[]Value
}

func (a *taggedTemplateArray) equal(other objectImpl) bool {
	if o, ok := other.(*taggedTemplateArray); ok {
		return a.idPtr == o.idPtr
	}
	return false
}

func (c *getTaggedTmplObject) exec(vm *vm) {
	cooked := vm.r.newArrayObject()
	setArrayValues(cooked, c.cooked)
	raw := vm.r.newArrayObject()
	setArrayValues(raw, c.raw)

	cooked.propValueCount = len(c.cooked)
	cooked.lengthProp.writable = false

	raw.propValueCount = len(c.raw)
	raw.lengthProp.writable = false

	raw.preventExtensions(true)
	raw.val.self = &taggedTemplateArray{
		arrayObject: raw,
		idPtr:       &c.raw,
	}

	cooked._putProp("raw", raw.val, false, false, false)
	cooked.preventExtensions(true)
	cooked.val.self = &taggedTemplateArray{
		arrayObject: cooked,
		idPtr:       &c.cooked,
	}

	vm.push(cooked.val)
	vm.pc++
}

type _loadSuper struct{}

var loadSuper _loadSuper

func (_loadSuper) exec(vm *vm) {
	homeObject := getHomeObject(vm.stack[vm.sb-1])
	if proto := homeObject.Prototype(); proto != nil {
		vm.push(proto)
	} else {
		vm.push(_undefined)
	}
	vm.pc++
}

type newClass struct {
	ctor       *Program
	name       unistring.String
	source     string
	initFields *Program

	privateFields, privateMethods       []unistring.String // only set when dynamic resolution is needed
	numPrivateFields, numPrivateMethods uint32

	length        int
	hasPrivateEnv bool
}

type newDerivedClass struct {
	newClass
}

func (vm *vm) createPrivateType(f *classFuncObject, numFields, numMethods uint32) {
	typ := &privateEnvType{}
	typ.numFields = numFields
	typ.numMethods = numMethods
	f.privateEnvType = typ
	f.privateMethods = make([]Value, numMethods)
}

func (vm *vm) fillPrivateNamesMap(typ *privateEnvType, privateFields, privateMethods []unistring.String) {
	if len(privateFields) > 0 || len(privateMethods) > 0 {
		penv := vm.privEnv.names
		if penv == nil {
			penv = make(privateNames)
			vm.privEnv.names = penv
		}
		for idx, field := range privateFields {
			penv[field] = &privateId{
				typ: typ,
				idx: uint32(idx),
			}
		}
		for idx, method := range privateMethods {
			penv[method] = &privateId{
				typ:      typ,
				idx:      uint32(idx),
				isMethod: true,
			}
		}
	}
}

func (c *newClass) create(protoParent, ctorParent *Object, vm *vm, derived bool) (prototype, cls *Object) {
	proto := vm.r.newBaseObject(protoParent, classObject)
	f := vm.r.newClassFunc(c.name, c.length, ctorParent, derived)
	f._putProp("prototype", proto.val, false, false, false)
	proto._putProp("constructor", f.val, true, false, true)
	f.prg = c.ctor
	f.stash = vm.stash
	f.src = c.source
	f.initFields = c.initFields
	if c.hasPrivateEnv {
		vm.privEnv = &privateEnv{
			outer: vm.privEnv,
		}
		vm.createPrivateType(f, c.numPrivateFields, c.numPrivateMethods)
		vm.fillPrivateNamesMap(f.privateEnvType, c.privateFields, c.privateMethods)
		vm.privEnv.instanceType = f.privateEnvType
	}
	f.privEnv = vm.privEnv
	return proto.val, f.val
}

func (c *newClass) exec(vm *vm) {
	proto, cls := c.create(vm.r.global.ObjectPrototype, vm.r.getFunctionPrototype(), vm, false)
	sp := vm.sp
	vm.stack.expand(sp + 1)
	vm.stack[sp] = proto
	vm.stack[sp+1] = cls
	vm.sp = sp + 2
	vm.pc++
}

func (c *newDerivedClass) exec(vm *vm) {
	var protoParent *Object
	var superClass *Object
	if o := vm.stack[vm.sp-1]; o != _null {
		if sc, ok := o.(*Object); !ok || sc.self.assertConstructor() == nil {
			vm.throw(vm.r.NewTypeError("Class extends value is not a constructor or null"))
			return
		} else {
			v := sc.self.getStr("prototype", nil)
			if v != _null {
				if o, ok := v.(*Object); ok {
					protoParent = o
				} else {
					vm.throw(vm.r.NewTypeError("Class extends value does not have valid prototype property"))
					return
				}
			}
			superClass = sc
		}
	} else {
		superClass = vm.r.getFunctionPrototype()
	}

	proto, cls := c.create(protoParent, superClass, vm, true)
	vm.stack[vm.sp-1] = proto
	vm.push(cls)
	vm.pc++
}

// Creates a special instance of *classFuncObject which is only used during evaluation of a class declaration
// to initialise static fields and instance private methods of another class.
type newStaticFieldInit struct {
	initFields                          *Program
	numPrivateFields, numPrivateMethods uint32
}

func (c *newStaticFieldInit) exec(vm *vm) {
	f := vm.r.newClassFunc("", 0, vm.r.getFunctionPrototype(), false)
	if c.numPrivateFields > 0 || c.numPrivateMethods > 0 {
		vm.createPrivateType(f, c.numPrivateFields, c.numPrivateMethods)
	}
	f.initFields = c.initFields
	f.stash = vm.stash
	vm.push(f.val)
	vm.pc++
}

func (vm *vm) loadThis(v Value) {
	if v != nil {
		vm.push(v)
	} else {
		vm.throw(vm.r.newError(vm.r.getReferenceError(), "Must call super constructor in derived class before accessing 'this'"))
		return
	}
	vm.pc++
}

type loadThisStash uint32

func (l loadThisStash) exec(vm *vm) {
	vm.loadThis(*vm.getStashPtr(uint32(l)))
}

type loadThisStack struct{}

func (loadThisStack) exec(vm *vm) {
	vm.loadThis(vm.stack[vm.sb])
}

func (vm *vm) getStashPtr(s uint32) *Value {
	level := int(s) >> 24
	idx := s & 0x00FFFFFF
	stash := vm.stash
	for i := 0; i < level; i++ {
		stash = stash.outer
	}

	return &stash.values[idx]
}

type getThisDynamic struct{}

func (getThisDynamic) exec(vm *vm) {
	for stash := vm.stash; stash != nil; stash = stash.outer {
		if stash.obj == nil {
			if v, exists := stash.getByName(thisBindingName); exists {
				vm.push(v)
				vm.pc++
				return
			}
		}
	}
	vm.push(vm.r.globalObject)
	vm.pc++
}

type throwConst struct {
	v interface{}
}

func (t throwConst) exec(vm *vm) {
	vm.throw(t.v)
}

type resolveThisStack struct{}

func (r resolveThisStack) exec(vm *vm) {
	vm.refStack = append(vm.refStack, &thisRef{v: (*[]Value)(&vm.stack), idx: vm.sb})
	vm.pc++
}

type resolveThisStash uint32

func (r resolveThisStash) exec(vm *vm) {
	level := int(r) >> 24
	idx := r & 0x00FFFFFF
	stash := vm.stash
	for i := 0; i < level; i++ {
		stash = stash.outer
	}
	vm.refStack = append(vm.refStack, &thisRef{v: &stash.values, idx: int(idx)})
	vm.pc++
}

type resolveThisDynamic struct{}

func (resolveThisDynamic) exec(vm *vm) {
	for stash := vm.stash; stash != nil; stash = stash.outer {
		if stash.obj == nil {
			if idx, exists := stash.names[thisBindingName]; exists {
				vm.refStack = append(vm.refStack, &thisRef{v: &stash.values, idx: int(idx &^ maskTyp)})
				vm.pc++
				return
			}
		}
	}
	panic(vm.r.newError(vm.r.getReferenceError(), "Compiler bug: 'this' reference is not found in resolveThisDynamic"))
}

type defineComputedKey int

func (offset defineComputedKey) exec(vm *vm) {
	obj := vm.r.toObject(vm.stack[vm.sp-int(offset)])
	if h, ok := obj.self.(*classFuncObject); ok {
		key := toPropertyKey(vm.stack[vm.sp-1])
		h.computedKeys = append(h.computedKeys, key)
		vm.sp--
		vm.pc++
		return
	}
	panic(vm.r.NewTypeError("Compiler bug: unexpected target for defineComputedKey: %v", obj))
}

type loadComputedKey int

func (idx loadComputedKey) exec(vm *vm) {
	obj := vm.r.toObject(vm.stack[vm.sb-1])
	if h, ok := obj.self.(*classFuncObject); ok {
		vm.push(h.computedKeys[idx])
		vm.pc++
		return
	}
	panic(vm.r.NewTypeError("Compiler bug: unexpected target for loadComputedKey: %v", obj))
}

type initStaticElements struct {
	privateFields, privateMethods []unistring.String
}

func (i *initStaticElements) exec(vm *vm) {
	cls := vm.stack[vm.sp-1]
	staticInit := vm.r.toObject(vm.stack[vm.sp-3])
	vm.sp -= 2
	if h, ok := staticInit.self.(*classFuncObject); ok {
		h._putProp("prototype", cls, true, true, true) // so that 'super' resolution work
		h.privEnv = vm.privEnv
		if h.privateEnvType != nil {
			vm.privEnv.staticType = h.privateEnvType
			vm.fillPrivateNamesMap(h.privateEnvType, i.privateFields, i.privateMethods)
		}
		h._initFields(vm.r.toObject(cls))
		vm.stack[vm.sp-1] = cls

		vm.pc++
		return
	}
	panic(vm.r.NewTypeError("Compiler bug: unexpected target for initStaticElements: %v", staticInit))
}

type definePrivateMethod struct {
	idx          int
	targetOffset int
}

func (d *definePrivateMethod) getPrivateMethods(vm *vm) []Value {
	obj := vm.r.toObject(vm.stack[vm.sp-d.targetOffset])
	if cls, ok := obj.self.(*classFuncObject); ok {
		return cls.privateMethods
	} else {
		panic(vm.r.NewTypeError("Compiler bug: wrong target type for definePrivateMethod: %T", obj.self))
	}
}

func (d *definePrivateMethod) exec(vm *vm) {
	methods := d.getPrivateMethods(vm)
	methods[d.idx] = vm.stack[vm.sp-1]
	vm.sp--
	vm.pc++
}

type definePrivateGetter struct {
	definePrivateMethod
}

func (d *definePrivateGetter) exec(vm *vm) {
	methods := d.getPrivateMethods(vm)
	val := vm.stack[vm.sp-1]
	method := vm.r.toObject(val)
	p, _ := methods[d.idx].(*valueProperty)
	if p == nil {
		p = &valueProperty{
			accessor: true,
		}
		methods[d.idx] = p
	}
	if p.getterFunc != nil {
		vm.throw(vm.r.NewTypeError("Private getter has already been declared"))
		return
	}
	p.getterFunc = method
	vm.sp--
	vm.pc++
}

type definePrivateSetter struct {
	definePrivateMethod
}

func (d *definePrivateSetter) exec(vm *vm) {
	methods := d.getPrivateMethods(vm)
	val := vm.stack[vm.sp-1]
	method := vm.r.toObject(val)
	p, _ := methods[d.idx].(*valueProperty)
	if p == nil {
		p = &valueProperty{
			accessor: true,
		}
		methods[d.idx] = p
	}
	if p.setterFunc != nil {
		vm.throw(vm.r.NewTypeError("Private setter has already been declared"))
		return
	}
	p.setterFunc = method
	vm.sp--
	vm.pc++
}

type definePrivateProp struct {
	idx int
}

func (d *definePrivateProp) exec(vm *vm) {
	f := vm.r.toObject(vm.stack[vm.sb-1]).self.(*classFuncObject)
	obj := vm.r.toObject(vm.stack[vm.sp-2])
	penv := obj.self.getPrivateEnv(f.privateEnvType, false)
	penv.fields[d.idx] = vm.stack[vm.sp-1]
	vm.sp--
	vm.pc++
}

type getPrivatePropRes resolvedPrivateName

func (vm *vm) getPrivateType(level uint8, isStatic bool) *privateEnvType {
	e := vm.privEnv
	for i := uint8(0); i < level; i++ {
		e = e.outer
	}
	if isStatic {
		return e.staticType
	}
	return e.instanceType
}

func (g *getPrivatePropRes) _get(base Value, vm *vm) Value {
	return vm.getPrivateProp(base, g.name, vm.getPrivateType(g.level, g.isStatic), g.idx, g.isMethod)
}

func (g *getPrivatePropRes) exec(vm *vm) {
	vm.stack[vm.sp-1] = g._get(vm.stack[vm.sp-1], vm)
	vm.pc++
}

type getPrivatePropId privateId

func (g *getPrivatePropId) exec(vm *vm) {
	vm.stack[vm.sp-1] = vm.getPrivateProp(vm.stack[vm.sp-1], g.name, g.typ, g.idx, g.isMethod)
	vm.pc++
}

type getPrivatePropIdCallee privateId

func (g *getPrivatePropIdCallee) exec(vm *vm) {
	prop := vm.getPrivateProp(vm.stack[vm.sp-1], g.name, g.typ, g.idx, g.isMethod)
	if prop == nil {
		prop = memberUnresolved{valueUnresolved{r: vm.r, ref: (*privateId)(g).string()}}
	}
	vm.push(prop)

	vm.pc++
}

func (vm *vm) getPrivateProp(base Value, name unistring.String, typ *privateEnvType, idx uint32, isMethod bool) Value {
	obj := vm.r.toObject(base)
	penv := obj.self.getPrivateEnv(typ, false)
	var v Value
	if penv != nil {
		if isMethod {
			v = penv.methods[idx]
		} else {
			v = penv.fields[idx]
			if v == nil {
				panic(vm.r.NewTypeError("Private member #%s is accessed before it is initialized", name))
			}
		}
	} else {
		panic(vm.r.NewTypeError("Cannot read private member #%s from an object whose class did not declare it", name))
	}
	if prop, ok := v.(*valueProperty); ok {
		if prop.getterFunc == nil {
			panic(vm.r.NewTypeError("'#%s' was defined without a getter", name))
		}
		v = prop.get(obj)
	}
	return v
}

type getPrivatePropResCallee getPrivatePropRes

func (g *getPrivatePropResCallee) exec(vm *vm) {
	prop := (*getPrivatePropRes)(g)._get(vm.stack[vm.sp-1], vm)
	if prop == nil {
		prop = memberUnresolved{valueUnresolved{r: vm.r, ref: (*resolvedPrivateName)(g).string()}}
	}
	vm.push(prop)

	vm.pc++
}

func (vm *vm) setPrivateProp(base Value, name unistring.String, typ *privateEnvType, idx uint32, isMethod bool, val Value) {
	obj := vm.r.toObject(base)
	penv := obj.self.getPrivateEnv(typ, false)
	if penv != nil {
		if isMethod {
			v := penv.methods[idx]
			if prop, ok := v.(*valueProperty); ok {
				if prop.setterFunc != nil {
					prop.set(base, val)
				} else {
					panic(vm.r.NewTypeError("Cannot assign to read only property '#%s'", name))
				}
			} else {
				panic(vm.r.NewTypeError("Private method '#%s' is not writable", name))
			}
		} else {
			ptr := &penv.fields[idx]
			if *ptr == nil {
				panic(vm.r.NewTypeError("Private member #%s is accessed before it is initialized", name))
			}
			*ptr = val
		}
	} else {
		panic(vm.r.NewTypeError("Cannot write private member #%s from an object whose class did not declare it", name))
	}
}

func (vm *vm) exceptionFromValue(x interface{}) *Exception {
	var ex *Exception
	switch x1 := x.(type) {
	case *Object:
		ex = &Exception{
			val: x1,
		}
		if er, ok := x1.self.(*errorObject); ok {
			ex.stack = er.stack
		}
	case Value:
		ex = &Exception{
			val: x1,
		}
	case *Exception:
		ex = x1
	case typeError:
		ex = &Exception{
			val: vm.r.NewTypeError(string(x1)),
		}
	case referenceError:
		ex = &Exception{
			val: vm.r.newError(vm.r.getReferenceError(), string(x1)),
		}
	case rangeError:
		ex = &Exception{
			val: vm.r.newError(vm.r.getRangeError(), string(x1)),
		}
	case syntaxError:
		ex = &Exception{
			val: vm.r.newError(vm.r.getSyntaxError(), string(x1)),
		}
	default:
		/*
			if vm.prg != nil {
				vm.prg.dumpCode(log.Printf)
			}
			log.Print("Stack: ", string(debug.Stack()))
			panic(fmt.Errorf("Panic at %d: %v", vm.pc, x))
		*/
		return nil
	}
	if ex.stack == nil {
		ex.stack = vm.captureStack(make([]StackFrame, 0, len(vm.callStack)+1), 0)
	}
	return ex
}

type setPrivatePropRes resolvedPrivateName

func (p *setPrivatePropRes) _set(base Value, val Value, vm *vm) {
	vm.setPrivateProp(base, p.name, vm.getPrivateType(p.level, p.isStatic), p.idx, p.isMethod, val)
}

func (p *setPrivatePropRes) exec(vm *vm) {
	v := vm.stack[vm.sp-1]
	p._set(vm.stack[vm.sp-2], v, vm)
	vm.stack[vm.sp-2] = v
	vm.sp--
	vm.pc++
}

type setPrivatePropResP setPrivatePropRes

func (p *setPrivatePropResP) exec(vm *vm) {
	v := vm.stack[vm.sp-1]
	(*setPrivatePropRes)(p)._set(vm.stack[vm.sp-2], v, vm)
	vm.sp -= 2
	vm.pc++
}

type setPrivatePropId privateId

func (p *setPrivatePropId) exec(vm *vm) {
	v := vm.stack[vm.sp-1]
	vm.setPrivateProp(vm.stack[vm.sp-2], p.name, p.typ, p.idx, p.isMethod, v)
	vm.stack[vm.sp-2] = v
	vm.sp--
	vm.pc++
}

type setPrivatePropIdP privateId

func (p *setPrivatePropIdP) exec(vm *vm) {
	v := vm.stack[vm.sp-1]
	vm.setPrivateProp(vm.stack[vm.sp-2], p.name, p.typ, p.idx, p.isMethod, v)
	vm.sp -= 2
	vm.pc++
}

type popPrivateEnv struct{}

func (popPrivateEnv) exec(vm *vm) {
	vm.privEnv = vm.privEnv.outer
	vm.pc++
}

type privateInRes resolvedPrivateName

func (i *privateInRes) exec(vm *vm) {
	obj := vm.r.toObject(vm.stack[vm.sp-1])
	pe := obj.self.getPrivateEnv(vm.getPrivateType(i.level, i.isStatic), false)
	if pe != nil && (i.isMethod && pe.methods[i.idx] != nil || !i.isMethod && pe.fields[i.idx] != nil) {
		vm.stack[vm.sp-1] = valueTrue
	} else {
		vm.stack[vm.sp-1] = valueFalse
	}
	vm.pc++
}

type privateInId privateId

func (i *privateInId) exec(vm *vm) {
	obj := vm.r.toObject(vm.stack[vm.sp-1])
	pe := obj.self.getPrivateEnv(i.typ, false)
	if pe != nil && (i.isMethod && pe.methods[i.idx] != nil || !i.isMethod && pe.fields[i.idx] != nil) {
		vm.stack[vm.sp-1] = valueTrue
	} else {
		vm.stack[vm.sp-1] = valueFalse
	}
	vm.pc++
}

type getPrivateRefRes resolvedPrivateName

func (r *getPrivateRefRes) exec(vm *vm) {
	vm.refStack = append(vm.refStack, &privateRefRes{
		base: vm.stack[vm.sp-1].ToObject(vm.r),
		name: (*resolvedPrivateName)(r),
	})
	vm.sp--
	vm.pc++
}

type getPrivateRefId privateId

func (r *getPrivateRefId) exec(vm *vm) {
	vm.refStack = append(vm.refStack, &privateRefId{
		base: vm.stack[vm.sp-1].ToObject(vm.r),
		id:   (*privateId)(r),
	})
	vm.sp--
	vm.pc++
}

func (y *yieldMarker) exec(vm *vm) {
	vm.pc = -vm.pc // this will terminate the run loop
	vm.push(y)     // marker so the caller knows it's a yield, not a return
}

func (y *yieldMarker) String() string {
	if y == yieldEmpty {
		return "empty"
	}
	switch y.resultType {
	case resultYield:
		return "yield"
	case resultYieldRes:
		return "yieldRes"
	case resultYieldDelegate:
		return "yield*"
	case resultYieldDelegateRes:
		return "yield*Res"
	case resultAwait:
		return "await"
	default:
		return "unknown"
	}
}
