package sobek

import (
	"bufio"
	"errors"
	"fmt"
	"os"
	"regexp"
	"runtime"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"time"
	"unicode"

	"github.com/go-sourcemap/sourcemap"
	"github.com/grafana/sobek/unistring"
)

// DebuggerVersion identifies the current debugger build.
// Bump this on every meaningful change so log output confirms the running version.
const DebuggerVersion = "0.5.0-20260427"

// Debug logging flags controlled by environment variables
// Set these env vars to "1" or "true" to enable verbose logging for specific areas
var (
	// SOBEK_DEBUG_ACTIVATE - logs activate() flow, continue signals, lifecycle transitions
	debugActivate = os.Getenv("SOBEK_DEBUG_ACTIVATE") == "1" || os.Getenv("SOBEK_DEBUG_ACTIVATE") == "true"
	// SOBEK_DEBUG_GLOBAL_STEP - logs global step state changes across VMs
	debugGlobalStep = os.Getenv("SOBEK_DEBUG_GLOBAL_STEP") == "1" || os.Getenv("SOBEK_DEBUG_GLOBAL_STEP") == "true"
	// SOBEK_DEBUG_INIT - logs init phase tracking and breakpoint skipping during init
	debugInit = os.Getenv("SOBEK_DEBUG_INIT") == "1" || os.Getenv("SOBEK_DEBUG_INIT") == "true"
	// SOBEK_DEBUG_BREAKPOINT - logs breakpoint checking and hitting
	debugBreakpoint = os.Getenv("SOBEK_DEBUG_BREAKPOINT") == "1" || os.Getenv("SOBEK_DEBUG_BREAKPOINT") == "true"
	// SOBEK_DEBUG_BP - alias for SOBEK_DEBUG_BREAKPOINT (for global breakpoint registry)
	debugBP = os.Getenv("SOBEK_DEBUG_BP") == "1" || os.Getenv("SOBEK_DEBUG_BP") == "true"
	// SOBEK_DEBUG_CONTINUE - logs Continue() signal flow and channel coordination
	debugContinue = os.Getenv("SOBEK_DEBUG_CONTINUE") == "1" || os.Getenv("SOBEK_DEBUG_CONTINUE") == "true"
	// SOBEK_DEBUG_VM - logs VM execution stepping details
	debugVM = os.Getenv("SOBEK_DEBUG_VM") == "1" || os.Getenv("SOBEK_DEBUG_VM") == "true"
	// SOBEK_DEBUG_COMPILER - logs compiler debug symbol collection (very verbose)
	debugCompiler = os.Getenv("SOBEK_DEBUG_COMPILER") == "1" || os.Getenv("SOBEK_DEBUG_COMPILER") == "true"
	// SOBEK_DEBUG_ALL - enables all debug logging
	debugAll = os.Getenv("SOBEK_DEBUG_ALL") == "1" || os.Getenv("SOBEK_DEBUG_ALL") == "true"
)

// tsSatisfiesRegex matches the TypeScript 'satisfies' operator: "expr satisfies Type" → "expr"
var tsSatisfiesRegex = regexp.MustCompile(`\s+satisfies\s+[A-Za-z_$][\w$.<>, ]*`)

func init() {
	if debugAll {
		debugActivate = true
		debugGlobalStep = true
		debugInit = true
		debugBreakpoint = true
		debugBP = true
		debugContinue = true
		debugVM = true
		// NOTE: debugCompiler is NOT enabled by SOBEK_DEBUG_ALL because it
		// generates massive output (1000+ lines per run). Use
		// SOBEK_DEBUG_COMPILER=1 separately when debugging scope/binding issues.
	}
}

// GlobalDebugCoordinator manages debug coordination across all VMs/VUs.
type GlobalDebugCoordinator struct {
	mu            sync.RWMutex
	activationCh  chan chan DebuggerActivation
	activeDbg     *Debugger
	isInitialized bool
	hasConnection bool

	globalStepNext        bool
	globalStepIn          bool
	globalSteppingFile    string
	globalStepTargetDepth int

	// PERF: Atomic fast-path flags for the hot instruction loop.
	// The vm.debug() loop checks for inherited step state on EVERY instruction
	// when !next && !stepIn. Using atomic flags lets us skip the RLock entirely
	// when no step state exists (99.9% of the time between breakpoints).
	// These are set/cleared by Set/Clear{Global,VU}StepState under mu.Lock,
	// and read lock-free by the instruction loop via atomic.LoadUint32.
	hasAnyStepState uint32 // 1 if any global or per-VU step state is set

	// PERF: multiVUDebug is set once at startup and never changes during a run.
	// Cache it as an atomic to avoid RLock on every instruction.
	multiVUDebugAtomic uint32 // 1 if multiVUDebug is true

	pendingLifecycleStepIn bool
	waitForFunctionEntry   bool
	globalActivationEpoch  uint64

	// suppressDefaultEntry: when set, sobek suppresses the debugger the moment
	// the "default" exported function is entered. Gherkin sets this after
	// LoadFeature so breakpoints in step-definition bodies don't fire during
	// the default() setup phase. runPickleStep clears it before each step call.
	suppressDefaultEntry bool

	// onPause/onResume are global callbacks invoked by every Debugger instance
	// when the VM pauses/resumes in activate(). k6 registers
	// ExecutionState.Pause/Resume here so debug-pause time is excluded from
	// iteration-duration metrics. Protected by mu.
	onPause  func()
	onResume func()

	// ── Multi-VU debug support ──────────────────────────────────────────
	// When multiVUDebug is true, each VU operates independently:
	//  - Step operations (Next/StepIn/StepOut) are scoped to the target VU
	//    and do NOT propagate via global step state.
	//  - activate() does NOT inherit global step state from other VUs.
	//  - Each debugger carries a vuID that is included in DebuggerActivation
	//    so the DAP handler can map VUs to DAP thread IDs.
	//  - Per-VU activation channels are used instead of the single global
	//    activationCh, eliminating the bottleneck when multiple VUs hit
	//    breakpoints simultaneously.
	// Enabled by default when debug mode is active. Set K6_DEBUG_MULTI_VU=0
	// in the environment to disable and enforce single-VU debugging.
	multiVUDebug    bool
	activeDebuggers map[uint64]*Debugger // vuID → debugger (all currently registered debuggers)

	// perVUActivationCh provides per-VU activation channels in multi-VU mode.
	// Each VU gets its own channel so simultaneous breakpoint hits don't
	// contend on a single global channel. Only used when multiVUDebug=true.
	perVUActivationCh map[uint64]chan chan DebuggerActivation

	// perVUStepState holds per-VU step state in multi-VU mode. In single-VU
	// mode, the global fields (globalStepNext, etc.) are used instead.
	perVUStepState map[uint64]*vuStepState

	// globalStoppedCh is notified by activate() whenever ANY debugger pauses.
	// doContinue() in the DAP layer listens on this as a cross-VU fallback
	// to detect breakpoints on VUs other than the one Continue() was called on.
	globalStoppedCh chan DebuggerActivation
}

// vuStepState holds step operation state scoped to a single VU.
// Only used in multi-VU debug mode.
type vuStepState struct {
	next             bool
	stepIn           bool
	steppingFile     string
	targetDepth      int
}

var globalDebugCoordinator = &GlobalDebugCoordinator{
	activationCh:  make(chan chan DebuggerActivation, 1),
	isInitialized: false,
	hasConnection: false,
}

func InitGlobalCoordinator() {
	globalDebugCoordinator.mu.Lock()
	defer globalDebugCoordinator.mu.Unlock()

	// Drain the old channel before replacing it.
	select {
	case <-globalDebugCoordinator.activationCh:
	default:
	}

	// Full reset — wipe ALL state so a second run starts clean.
	globalDebugCoordinator.resetLocked()
}

// resetLocked performs the actual coordinator reset. Must be called with mu held.
func (gdc *GlobalDebugCoordinator) resetLocked() {
	gdc.activationCh = make(chan chan DebuggerActivation, 1)
	gdc.isInitialized = true
	gdc.hasConnection = false
	gdc.activeDbg = nil
	gdc.globalStepNext = false
	gdc.globalStepIn = false
	gdc.globalSteppingFile = ""
	gdc.globalStepTargetDepth = 0
	gdc.pendingLifecycleStepIn = false
	gdc.waitForFunctionEntry = false
	gdc.globalActivationEpoch = 0
	gdc.activeDebuggers = make(map[uint64]*Debugger)
	gdc.perVUActivationCh = make(map[uint64]chan chan DebuggerActivation)
	gdc.perVUStepState = make(map[uint64]*vuStepState)
	gdc.globalStoppedCh = make(chan DebuggerActivation, 1)
	atomic.StoreUint32(&gdc.hasAnyStepState, 0)
	// NOTE: multiVUDebug/multiVUDebugAtomic are NOT reset here — they're set
	// once at startup and must survive across lifecycle phase resets.
}

// ── Multi-VU debug API ──────────────────────────────────────────────────────

// SetMultiVUDebug enables or disables multi-VU debug mode.
// When enabled, step operations are scoped per-VU and global step state is not
// inherited across VUs. Call this once during debugger initialization.
func (gdc *GlobalDebugCoordinator) SetMultiVUDebug(enabled bool) {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	gdc.multiVUDebug = enabled
	if enabled {
		atomic.StoreUint32(&gdc.multiVUDebugAtomic, 1)
	} else {
		atomic.StoreUint32(&gdc.multiVUDebugAtomic, 0)
	}
}

// IsMultiVUDebug returns true if multi-VU debug mode is active.
// PERF: Lock-free via atomic — safe to call on every instruction.
func (gdc *GlobalDebugCoordinator) IsMultiVUDebug() bool {
	return atomic.LoadUint32(&gdc.multiVUDebugAtomic) != 0
}

// RegisterDebugger adds a debugger to the active set keyed by its VU ID.
// Called when a VU is created in debug mode. Safe to call multiple times for
// the same vuID (idempotent — overwrites the previous entry).
func (gdc *GlobalDebugCoordinator) RegisterDebugger(vuID uint64, dbg *Debugger) {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	if gdc.activeDebuggers == nil {
		gdc.activeDebuggers = make(map[uint64]*Debugger)
	}
	gdc.activeDebuggers[vuID] = dbg
}

// UnregisterDebugger removes a debugger from the active set.
func (gdc *GlobalDebugCoordinator) UnregisterDebugger(vuID uint64) {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	delete(gdc.activeDebuggers, vuID)
}

// GetDebuggerForVU returns the debugger for a specific VU, or nil.
func (gdc *GlobalDebugCoordinator) GetDebuggerForVU(vuID uint64) *Debugger {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	return gdc.activeDebuggers[vuID]
}

// GetAllDebuggers returns a snapshot of all registered debugger instances.
// The returned map is safe to iterate — it's a copy.
func (gdc *GlobalDebugCoordinator) GetAllDebuggers() map[uint64]*Debugger {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	result := make(map[uint64]*Debugger, len(gdc.activeDebuggers))
	for k, v := range gdc.activeDebuggers {
		result[k] = v
	}
	return result
}

// ── Per-VU activation channels (multi-VU mode) ─────────────────────────────

// GetVUActivationChannel returns the per-VU activation channel for the given vuID.
// In multi-VU mode, each VU has its own channel to avoid contention.
// In single-VU mode, returns the global activationCh.
func (gdc *GlobalDebugCoordinator) GetVUActivationChannel(vuID uint64) chan chan DebuggerActivation {
	if !gdc.multiVUDebug {
		return gdc.activationCh
	}
	gdc.mu.Lock()
	ch, ok := gdc.perVUActivationCh[vuID]
	if !ok {
		ch = make(chan chan DebuggerActivation, 1)
		gdc.perVUActivationCh[vuID] = ch
	}
	gdc.mu.Unlock()
	return ch
}

// DrainVUActivationChannel removes any stale entries from a VU-specific
// activation channel. In single-VU mode, drains the global channel.
func (gdc *GlobalDebugCoordinator) DrainVUActivationChannel(vuID uint64) {
	ch := gdc.GetVUActivationChannel(vuID)
	for {
		select {
		case <-ch:
		default:
			return
		}
	}
}

// ── Per-VU step state (multi-VU mode) ───────────────────────────────────────

// SetVUStepState sets step state for a specific VU. Only used in multi-VU mode.
func (gdc *GlobalDebugCoordinator) SetVUStepState(vuID uint64, next, stepIn bool, filename string, targetDepth int) {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	if gdc.perVUStepState == nil {
		gdc.perVUStepState = make(map[uint64]*vuStepState)
	}
	gdc.perVUStepState[vuID] = &vuStepState{
		next:         next,
		stepIn:       stepIn,
		steppingFile: filename,
		targetDepth:  targetDepth,
	}
	if next || stepIn {
		atomic.StoreUint32(&gdc.hasAnyStepState, 1)
	}
	if debugGlobalStep {
		fmt.Printf("[GLOBAL-STEP] SetVUStepState(vuID=%d): next=%v, stepIn=%v, file=%s, depth=%d\n",
			vuID, next, stepIn, filename, targetDepth)
	}
}

// GetVUStepState reads step state for a specific VU. Returns zero values if no
// state is set. Only used in multi-VU mode.
func (gdc *GlobalDebugCoordinator) GetVUStepState(vuID uint64) (next, stepIn bool, filename string, targetDepth int) {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	if gdc.perVUStepState == nil {
		return
	}
	s := gdc.perVUStepState[vuID]
	if s == nil {
		return
	}
	return s.next, s.stepIn, s.steppingFile, s.targetDepth
}

// ClearVUStepState clears step state for a specific VU. Only used in multi-VU mode.
func (gdc *GlobalDebugCoordinator) ClearVUStepState(vuID uint64) {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	if gdc.perVUStepState != nil {
		delete(gdc.perVUStepState, vuID)
	}
	// Recompute atomic flag: check if any step state remains
	gdc.recomputeHasAnyStepStateLocked()
	if debugGlobalStep {
		fmt.Printf("[GLOBAL-STEP] ClearVUStepState(vuID=%d)\n", vuID)
	}
}

// HasVUStepState returns true if the given VU has pending step state.
func (gdc *GlobalDebugCoordinator) HasVUStepState(vuID uint64) bool {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	if gdc.perVUStepState == nil {
		return false
	}
	s := gdc.perVUStepState[vuID]
	if s == nil {
		return false
	}
	return s.next || s.stepIn
}

// MaybeInitGlobalCoordinator initializes the coordinator only if it hasn't been
// initialized yet. This is TOCTOU-safe: the check and init happen under a single
// Lock, preventing a concurrent Instantiate() from wiping state set by another VU.
func MaybeInitGlobalCoordinator() {
	globalDebugCoordinator.mu.Lock()
	defer globalDebugCoordinator.mu.Unlock()
	if globalDebugCoordinator.isInitialized {
		return
	}
	globalDebugCoordinator.resetLocked()
}

func GetGlobalCoordinator() *GlobalDebugCoordinator {
	return globalDebugCoordinator
}

func (gdc *GlobalDebugCoordinator) SetActiveDebugger(dbg *Debugger) {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	gdc.activeDbg = dbg
}

func (gdc *GlobalDebugCoordinator) GetActiveDebugger() *Debugger {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	return gdc.activeDbg
}

func (gdc *GlobalDebugCoordinator) ActivationChannel() chan chan DebuggerActivation {
	return gdc.activationCh
}

// GlobalStoppedChannel returns the channel that is notified whenever any
// debugger's activate() fires (breakpoint/step hit). The DAP layer listens
// on this as a cross-VU fallback so it always detects stops regardless of
// which VU's debugger Continue() was called on.
func (gdc *GlobalDebugCoordinator) GlobalStoppedChannel() <-chan DebuggerActivation {
	return gdc.globalStoppedCh
}

// NotifyGlobalStopped sends an activation to the global stopped channel.
// Called by activate() after the debugger has paused. Non-blocking — if the
// channel is full (previous notification not consumed), the old entry is
// drained first.
func (gdc *GlobalDebugCoordinator) NotifyGlobalStopped(activation DebuggerActivation) {
	select {
	case <-gdc.globalStoppedCh:
	default:
	}
	select {
	case gdc.globalStoppedCh <- activation:
	default:
	}
}

// DrainGlobalStopped removes any stale entry from the global stopped channel.
// Called after the handshake Continue() to prevent the stale activation from
// winning the select race against the real step result.
func (gdc *GlobalDebugCoordinator) DrainGlobalStopped() {
	select {
	case <-gdc.globalStoppedCh:
		// drained stale entry
	default:
	}
}

// DrainActivationChannel removes any stale entries from the global activation
// channel. Call this before setting stepIn for a new gherkin step to prevent
// activate() from picking up a stale Continue() signal (0ms handshake).
func (gdc *GlobalDebugCoordinator) DrainActivationChannel() {
	for {
		select {
		case <-gdc.activationCh:
			// drained one stale entry
		default:
			return
		}
	}
}

func (gdc *GlobalDebugCoordinator) NextGlobalEpoch() uint64 {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	gdc.globalActivationEpoch++
	return gdc.globalActivationEpoch
}

func (gdc *GlobalDebugCoordinator) GetGlobalEpoch() uint64 {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	return gdc.globalActivationEpoch
}

func (gdc *GlobalDebugCoordinator) IsInitialized() bool {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	return gdc.isInitialized
}

func (gdc *GlobalDebugCoordinator) SetGlobalConnection(connected bool) {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	gdc.hasConnection = connected
	if debugActivate {
		fmt.Printf("[DEBUGGER] Global connection status set to: %v\n", connected)
	}
}

type WatchResult struct {
	ID    int
	Value Value
	Err   error
}

func (gdc *GlobalDebugCoordinator) HasGlobalConnection() bool {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	return gdc.hasConnection
}

func (gdc *GlobalDebugCoordinator) SetGlobalStepState(next, stepIn bool, filename string, targetDepth int) {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	if debugGlobalStep {
		fmt.Printf("[GLOBAL-STEP] SetGlobalStepState: next=%v, stepIn=%v, file=%s, targetDepth=%d (was: next=%v, stepIn=%v, file=%s, targetDepth=%d)\n",
			next, stepIn, filename, targetDepth, gdc.globalStepNext, gdc.globalStepIn, gdc.globalSteppingFile, gdc.globalStepTargetDepth)
	}
	gdc.globalStepNext = next
	gdc.globalStepIn = stepIn
	gdc.globalSteppingFile = filename
	gdc.globalStepTargetDepth = targetDepth
	if next || stepIn {
		atomic.StoreUint32(&gdc.hasAnyStepState, 1)
	} else {
		gdc.recomputeHasAnyStepStateLocked()
	}
}

func (gdc *GlobalDebugCoordinator) GetGlobalStepState() (next, stepIn bool, filename string, targetDepth int) {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	if debugGlobalStep {
		fmt.Printf("[GLOBAL-STEP] GetGlobalStepState: next=%v, stepIn=%v, file=%s, targetDepth=%d\n",
			gdc.globalStepNext, gdc.globalStepIn, gdc.globalSteppingFile, gdc.globalStepTargetDepth)
	}
	return gdc.globalStepNext, gdc.globalStepIn, gdc.globalSteppingFile, gdc.globalStepTargetDepth
}

func (gdc *GlobalDebugCoordinator) ClearGlobalStepState() {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	if debugGlobalStep {
		fmt.Printf("[GLOBAL-STEP] ClearGlobalStepState: was next=%v, stepIn=%v, file=%s, targetDepth=%d\n",
			gdc.globalStepNext, gdc.globalStepIn, gdc.globalSteppingFile, gdc.globalStepTargetDepth)
	}
	gdc.globalStepNext = false
	gdc.globalStepIn = false
	gdc.globalSteppingFile = ""
	gdc.globalStepTargetDepth = 0
	gdc.recomputeHasAnyStepStateLocked()
}

func (gdc *GlobalDebugCoordinator) HasGlobalStepState() bool {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	return gdc.globalStepNext || gdc.globalStepIn
}

// HasAnyStepStateFast returns true if any global or per-VU step state is set.
// PERF: Lock-free via atomic — safe to call on every instruction in vm.debug().
// This is the fast-path gate: when false (99.9% of instructions), the caller
// can skip the RLock-protected GetGlobalStepState/GetVUStepState entirely.
func (gdc *GlobalDebugCoordinator) HasAnyStepStateFast() bool {
	return atomic.LoadUint32(&gdc.hasAnyStepState) != 0
}

// recomputeHasAnyStepStateLocked recalculates the hasAnyStepState atomic flag.
// Must be called with mu held (Lock, not RLock).
func (gdc *GlobalDebugCoordinator) recomputeHasAnyStepStateLocked() {
	if gdc.globalStepNext || gdc.globalStepIn {
		atomic.StoreUint32(&gdc.hasAnyStepState, 1)
		return
	}
	for _, s := range gdc.perVUStepState {
		if s != nil && (s.next || s.stepIn) {
			atomic.StoreUint32(&gdc.hasAnyStepState, 1)
			return
		}
	}
	atomic.StoreUint32(&gdc.hasAnyStepState, 0)
}

// SetPendingLifecycleStepIn marks that a lifecycle transition is pending and the
// VM should break at the first line of the new lifecycle function (setup, default,
// teardown, handleSummary).
//
// WARNING: This should ONLY be used for real lifecycle transitions (phase changes
// where a new exported function is entered). Do NOT use this for sub-step
// callbacks within the same phase (e.g., gherkin step functions within default()).
// Setting pendingLifecycleStepIn + SetGlobalStepState(stepIn=true) for sub-step
// callbacks causes the VM to break at every callback entry — even when the user
// pressed Continue (not Step Into). For sub-step callbacks, just unsuppress
// breakpoints and let them fire naturally.
func (gdc *GlobalDebugCoordinator) SetPendingLifecycleStepIn(pending bool) {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	if debugGlobalStep {
		fmt.Printf("[GLOBAL-STEP] SetPendingLifecycleStepIn: %v (was: %v)\n", pending, gdc.pendingLifecycleStepIn)
	}
	gdc.pendingLifecycleStepIn = pending
}

func (gdc *GlobalDebugCoordinator) HasPendingLifecycleStepIn() bool {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	return gdc.pendingLifecycleStepIn
}

func (gdc *GlobalDebugCoordinator) ConsumeLifecycleStepIn() bool {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	hadPending := gdc.pendingLifecycleStepIn
	if hadPending {
		if debugGlobalStep {
			fmt.Printf("[GLOBAL-STEP] ConsumeLifecycleStepIn: consumed pending step-in\n")
		}
		gdc.pendingLifecycleStepIn = false
	}
	return hadPending
}

func (gdc *GlobalDebugCoordinator) SetWaitForFunctionEntry(wait bool) {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	if debugGlobalStep {
		fmt.Printf("[GLOBAL-STEP] SetWaitForFunctionEntry: %v (was: %v)\n", wait, gdc.waitForFunctionEntry)
	}
	gdc.waitForFunctionEntry = wait
}

func (gdc *GlobalDebugCoordinator) ConsumeWaitForFunctionEntry() bool {
	gdc.mu.Lock()
	defer gdc.mu.Unlock()
	had := gdc.waitForFunctionEntry
	if had {
		if debugGlobalStep {
			fmt.Printf("[GLOBAL-STEP] ConsumeWaitForFunctionEntry: consumed (was waiting for function entry)\n")
		}
		gdc.waitForFunctionEntry = false
	}
	return had
}

func (gdc *GlobalDebugCoordinator) HasWaitForFunctionEntry() bool {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	return gdc.waitForFunctionEntry
}

// SetPauseResumeCallbacks registers global callbacks for debugger pause/resume.
// k6 calls this with ExecutionState.Pause / ExecutionState.Resume so that
// debug-pause time is excluded from iteration-duration metrics.
// Both callbacks must be goroutine-safe. Pass nil to clear.
func (gdc *GlobalDebugCoordinator) SetPauseResumeCallbacks(onPause, onResume func()) {
	gdc.mu.Lock()
	gdc.onPause = onPause
	gdc.onResume = onResume
	gdc.mu.Unlock()
}

// callPause invokes the registered onPause callback (if any).
// Called from Debugger.activateWithStepState before blocking.
func (gdc *GlobalDebugCoordinator) callPause() {
	gdc.mu.RLock()
	fn := gdc.onPause
	gdc.mu.RUnlock()
	if fn != nil {
		fn()
	}
}

// callResume invokes the registered onResume callback (if any).
// Called from Debugger.activateWithStepState after unblocking.
func (gdc *GlobalDebugCoordinator) callResume() {
	gdc.mu.RLock()
	fn := gdc.onResume
	gdc.mu.RUnlock()
	if fn != nil {
		fn()
	}
}

type VMRegistry interface {
	MultiScopeEval(rt *Runtime, expr string) (Value, error)
	RegisterVM(phase string, vuID uint64, rt *Runtime)
	SetSetupData(data Value)
	RefreshInitStash()
}

// conditionalBreakpoints maps normalizedFilename:line -> condition expression
// A breakpoint only fires if the condition evaluates to truthy.
// An empty/missing condition means "always fire" (normal breakpoint).
type conditionalBreakpoint struct {
	condition  string // JS expression; empty = unconditional
	logMessage string // if non-empty, this is a logpoint (don't pause, just log)
	hitCount   int    // current hit count
	hitTarget  int    // if > 0, only fire when hitCount % hitTarget == 0
}

const (
	PhaseInit = "init"
	PhaseVU   = "vu"
)

var (
	globalVMRegistry   VMRegistry
	globalVMRegistryMu sync.RWMutex
	watchExprCounter   int64 // atomic — AddWatch may be called from DAP goroutine
)

func SetGlobalRegistry(registry VMRegistry) {
	globalVMRegistryMu.Lock()
	defer globalVMRegistryMu.Unlock()
	globalVMRegistry = registry
}

func GetGlobalRegistry() VMRegistry {
	globalVMRegistryMu.RLock()
	defer globalVMRegistryMu.RUnlock()
	return globalVMRegistry
}

// bpSnapshot is an immutable, atomically-swapped snapshot of all breakpoints.
// Read-path methods (HasBreakpoint, FileHasBreakpoints, Count) load this via
// atomic.Pointer with zero lock acquisitions. Write-path methods (Set/Clear/ClearFile)
// rebuild and Store a new snapshot under the write lock.
type bpSnapshot struct {
	breakpoints map[string][]int // normalized filename -> sorted line numbers
	totalFiles  int              // cached len(breakpoints) for Count()
}

// GlobalBreakpointRegistry holds breakpoints shared across all debugger instances.
type GlobalBreakpointRegistry struct {
	mu            sync.RWMutex
	breakpoints   map[string][]int // normalized filename -> sorted line numbers
	breakpointIDs map[bpKey]int    // PERF: struct key avoids string alloc on lookup
	nextID        int

	// PERF: Lock-free read path — atomic pointer to immutable snapshot.
	// Reads (HasBreakpoint, FileHasBreakpoints, Count) load this pointer
	// with zero lock acquisitions. Writes (Set/Clear/ClearFile) take the
	// mutex and atomically swap a new snapshot. This eliminates the RLock
	// that was acquired on every instruction in the vm.debug() hot path.
	snapshot atomic.Pointer[bpSnapshot]
}

// bpKey is used as a map key for breakpointIDs to avoid string concatenation allocations.
type bpKey struct {
	filename string
	line     int
}

var globalBreakpoints = &GlobalBreakpointRegistry{
	breakpoints:   make(map[string][]int),
	breakpointIDs: make(map[bpKey]int),
	nextID:        0,
}

// rebuildSnapshotLocked creates a new immutable bpSnapshot from the current
// breakpoints map and stores it atomically. Must be called with mu held (write lock).
// The snapshot is a deep copy — reads are safe without any lock.
func (gbr *GlobalBreakpointRegistry) rebuildSnapshotLocked() {
	snap := &bpSnapshot{
		breakpoints: make(map[string][]int, len(gbr.breakpoints)),
		totalFiles:  len(gbr.breakpoints),
	}
	for k, v := range gbr.breakpoints {
		cp := make([]int, len(v))
		copy(cp, v)
		snap.breakpoints[k] = cp
	}
	gbr.snapshot.Store(snap)
}

// use composite key to avoid cross-file false positives
type initBPKey struct {
	file string
	line int
}

// GlobalInitTracker tracks which files have completed their init phase.
type GlobalInitTracker struct {
	mu            sync.RWMutex
	initCompleted map[string]bool

	// FIXED: composite key prevents line-number collisions across files
	initBreakpointSet map[initBPKey]bool

	// Per-file set kept for WasBreakpointHitDuringInit (file-specific check).
	initBreakpointsByFile map[string]map[int]bool
}

// globalInitCompletedFlag is a monotonic atomic: 0 → 1 when the first file's init
// completes, never reverts (except on full Reset). Allows HasAnyInitCompleted() to
// return without acquiring any lock — eliminates one RLock per instruction on the hot path.
var globalInitCompletedFlag uint32

var globalInitTracker = &GlobalInitTracker{
	initCompleted:         make(map[string]bool),
	initBreakpointSet:     make(map[initBPKey]bool),
	initBreakpointsByFile: make(map[string]map[int]bool),
}

func (git *GlobalInitTracker) MarkInitCompleted(filename string) {
	git.mu.Lock()
	defer git.mu.Unlock()
	normalizedFilename := normalizeFilename(filename)
	git.initCompleted[normalizedFilename] = true
	// PERF: Set monotonic atomic so HasAnyInitCompleted() is lock-free.
	atomic.StoreUint32(&globalInitCompletedFlag, 1)
	if debugInit {
		fmt.Printf("[INIT-TRACKER] Init completed for: %s\n", normalizedFilename)
	}
}

func (git *GlobalInitTracker) IsInitCompleted(filename string) bool {
	git.mu.RLock()
	defer git.mu.RUnlock()
	normalizedFilename := normalizeFilename(filename)
	return git.initCompleted[normalizedFilename]
}

func getMapKeys(m map[string]bool) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	return keys
}

func (git *GlobalInitTracker) RecordInitBreakpoint(filename string, line int) {
	normalizedFilename := normalizeFilename(filename)

	// PERF: Check under RLock first — the common case is that the breakpoint
	// was already recorded (multiple bytecodes per source line).
	git.mu.RLock()
	already := git.initBreakpointSet[initBPKey{normalizedFilename, line}]
	git.mu.RUnlock()
	if already {
		return
	}

	git.mu.Lock()
	defer git.mu.Unlock()

	// Double-check under exclusive lock.
	if git.initBreakpointSet[initBPKey{normalizedFilename, line}] {
		return
	}

	// FIXED: composite key — no cross-file false positives
	git.initBreakpointSet[initBPKey{normalizedFilename, line}] = true

	if git.initBreakpointsByFile[normalizedFilename] == nil {
		git.initBreakpointsByFile[normalizedFilename] = make(map[int]bool)
	}
	git.initBreakpointsByFile[normalizedFilename][line] = true

	if debugInit {
		fmt.Printf("[INIT-TRACKER] Recorded init breakpoint: file='%s', line=%d\n", normalizedFilename, line)
	}
}

// WasBreakpointHitDuringInit checks if a specific file+line was hit during init.
func (git *GlobalInitTracker) WasBreakpointHitDuringInit(filename string, line int) bool {
	git.mu.RLock()
	defer git.mu.RUnlock()
	normalizedFilename := normalizeFilename(filename)
	fileSet := git.initBreakpointsByFile[normalizedFilename]
	if fileSet == nil {
		return false
	}
	return fileSet[line]
}

// WasAnyBreakpointHitDuringInit checks if this line was hit during init in ANY file.
// PERF: O(1) map lookup — was O(files * lines) linear scan under RLock.
// Callers must pass the normalized filename.
func (git *GlobalInitTracker) WasAnyBreakpointHitDuringInit(normalizedFilename string, line int) bool {
	git.mu.RLock()
	found := git.initBreakpointSet[initBPKey{normalizedFilename, line}]
	git.mu.RUnlock()
	return found
}

// HasAnyInitCompleted returns true once any file's init phase has completed.
// PERF: Lock-free — uses a monotonic atomic flag instead of acquiring RLock.
// The flag is set in MarkInitCompleted and only ever goes from 0→1.
func (git *GlobalInitTracker) HasAnyInitCompleted() bool {
	return atomic.LoadUint32(&globalInitCompletedFlag) != 0
}

func (git *GlobalInitTracker) Reset() {
	git.mu.Lock()
	defer git.mu.Unlock()
	git.initCompleted = make(map[string]bool)
	git.initBreakpointSet = make(map[initBPKey]bool)
	git.initBreakpointsByFile = make(map[string]map[int]bool)
	// PERF: Reset the monotonic atomic flag.
	atomic.StoreUint32(&globalInitCompletedFlag, 0)
}

func GetGlobalInitTracker() *GlobalInitTracker {
	return globalInitTracker
}

// SetBreakpoint adds a breakpoint. Filenames are normalized at write time so
// HasBreakpoint never needs to allocate or normalize at read time.
func (gbr *GlobalBreakpointRegistry) SetBreakpoint(filename string, line int) (id int, err error) {
	// PERF: normalize once here so all lookups use the canonical form.
	filename = normalizeFilename(filename)

	gbr.mu.Lock()
	defer gbr.mu.Unlock()

	idx := sort.SearchInts(gbr.breakpoints[filename], line)
	if idx < len(gbr.breakpoints[filename]) && gbr.breakpoints[filename][idx] == line {
		return 0, errors.New("breakpoint exists")
	}

	gbr.breakpoints[filename] = append(gbr.breakpoints[filename], line)
	if len(gbr.breakpoints[filename]) > 1 {
		sort.Ints(gbr.breakpoints[filename])
	}

	id = gbr.nextID
	gbr.nextID++
	gbr.breakpointIDs[bpKey{filename, line}] = id

	if debugBP {
		fmt.Printf("[GLOBAL-BP] ✅ Breakpoint added: id=%d, filename='%s', line=%d, total=%d\n",
			id, filename, line, len(gbr.breakpoints[filename]))
	}

	// PERF: Rebuild lock-free snapshot for read-path methods.
	gbr.rebuildSnapshotLocked()

	return id, nil
}

func (gbr *GlobalBreakpointRegistry) ClearBreakpoint(filename string, line int) error {
	filename = normalizeFilename(filename)

	gbr.mu.Lock()
	defer gbr.mu.Unlock()

	if len(gbr.breakpoints[filename]) == 0 {
		return errors.New("no breakpoints")
	}

	idx := sort.SearchInts(gbr.breakpoints[filename], line)
	if idx < len(gbr.breakpoints[filename]) && gbr.breakpoints[filename][idx] == line {
		gbr.breakpoints[filename] = append(gbr.breakpoints[filename][:idx], gbr.breakpoints[filename][idx+1:]...)
		if len(gbr.breakpoints[filename]) == 0 {
			delete(gbr.breakpoints, filename)
		}
		delete(gbr.breakpointIDs, bpKey{filename, line})
		if debugBP {
			fmt.Printf("[GLOBAL-BP] Breakpoint cleared: filename='%s', line=%d\n", filename, line)
		}
		// PERF: Rebuild lock-free snapshot for read-path methods.
		gbr.rebuildSnapshotLocked()
		return nil
	}

	return errors.New("breakpoint doesn't exist")
}

// ClearFileBreakpoints removes ALL breakpoints for a given file from the global registry.
// This is used by the DAP setBreakpoints handler which is a replacement operation:
// the client sends the complete list of desired breakpoints and the server must
// remove any breakpoints that are no longer in the list.
func (gbr *GlobalBreakpointRegistry) ClearFileBreakpoints(filename string) {
	filename = normalizeFilename(filename)

	gbr.mu.Lock()
	defer gbr.mu.Unlock()

	lines := gbr.breakpoints[filename]
	if len(lines) == 0 {
		return
	}

	// Remove all breakpoint IDs for this file.
	for _, line := range lines {
		delete(gbr.breakpointIDs, bpKey{filename, line})
	}
	delete(gbr.breakpoints, filename)

	if debugBP {
		fmt.Printf("[GLOBAL-BP] Cleared all breakpoints for file '%s' (was %d)\n", filename, len(lines))
	}

	// PERF: Rebuild lock-free snapshot for read-path methods.
	gbr.rebuildSnapshotLocked()
}

// HasBreakpoint checks for a breakpoint. Caller must pass a normalized filename.
// PERF: Fully lock-free — loads an immutable snapshot via atomic.Pointer.
// No RLock, no defer, no allocation. One atomic load + map lookup + binary search.
func (gbr *GlobalBreakpointRegistry) HasBreakpoint(normalizedFilename string, line int) bool {
	snap := gbr.snapshot.Load()
	if snap == nil {
		return false
	}
	lines := snap.breakpoints[normalizedFilename]
	idx := sort.SearchInts(lines, line)
	return idx < len(lines) && lines[idx] == line
}

func (gbr *GlobalBreakpointRegistry) GetBreakpointID(filename string, line int) int {
	filename = normalizeFilename(filename)
	gbr.mu.RLock()
	id := gbr.breakpointIDs[bpKey{filename, line}]
	gbr.mu.RUnlock()
	return id
}

func (gbr *GlobalBreakpointRegistry) GetAllBreakpoints() map[string][]int {
	gbr.mu.RLock()
	defer gbr.mu.RUnlock()

	result := make(map[string][]int)
	for k, v := range gbr.breakpoints {
		result[k] = append([]int(nil), v...)
	}
	return result
}

// Count returns the number of files that have breakpoints.
// PERF: Lock-free — loads immutable snapshot via atomic.Pointer.
func (gbr *GlobalBreakpointRegistry) Count() int {
	snap := gbr.snapshot.Load()
	if snap == nil {
		return 0
	}
	return snap.totalFiles
}

// FileHasBreakpoints returns true if the file has any breakpoints registered.
// PERF: Lock-free — loads immutable snapshot via atomic.Pointer. O(1) map lookup.
func (gbr *GlobalBreakpointRegistry) FileHasBreakpoints(normalizedFilename string) bool {
	snap := gbr.snapshot.Load()
	if snap == nil {
		return false
	}
	return len(snap.breakpoints[normalizedFilename]) > 0
}

// HasBreakpointOnLine checks if ANY file has a breakpoint on the given line.
// PERF: Lock-free — loads immutable snapshot via atomic.Pointer.
func (gbr *GlobalBreakpointRegistry) HasBreakpointOnLine(line int) bool {
	snap := gbr.snapshot.Load()
	if snap == nil {
		return false
	}
	for _, lines := range snap.breakpoints {
		idx := sort.SearchInts(lines, line)
		if idx < len(lines) && lines[idx] == line {
			return true
		}
	}
	return false
}

// HasBreakpointOnLineExcluding checks if any file OTHER than the excluded ones
// has a breakpoint on the given line. Used for bundled TS where the bundle filename
// has already been checked and we only want to match original source filenames.
// PERF: Lock-free — loads immutable snapshot via atomic.Pointer.
func (gbr *GlobalBreakpointRegistry) HasBreakpointOnLineExcluding(line int, excludeFiles ...string) bool {
	snap := gbr.snapshot.Load()
	if snap == nil {
		return false
	}
	for file, lines := range snap.breakpoints {
		excluded := false
		for _, ef := range excludeFiles {
			if file == ef {
				excluded = true
				break
			}
		}
		if excluded {
			continue
		}
		idx := sort.SearchInts(lines, line)
		if idx < len(lines) && lines[idx] == line {
			return true
		}
	}
	return false
}

func GetGlobalBreakpoints() *GlobalBreakpointRegistry {
	return globalBreakpoints
}

// HttpCallRecord stores data about a completed HTTP request/response.
// Populated by the k6 HTTP module during execution (not just at pause time).
type HttpCallRecord struct {
	Method          string             `json:"method"`
	URL             string             `json:"url"`
	Name            string             `json:"name,omitempty"`
	Status          int                `json:"status"`
	StatusText      string             `json:"statusText"`
	Duration        float64            `json:"duration"`
	Proto           string             `json:"proto"`
	RequestHeaders  map[string]string  `json:"requestHeaders,omitempty"`
	RequestBody     string             `json:"requestBody,omitempty"`
	ResponseHeaders map[string]string  `json:"responseHeaders,omitempty"`
	ResponseBody    string             `json:"responseBody,omitempty"`
	ContentType     string             `json:"contentType,omitempty"`
	Size            int                `json:"size"`
	Timings         map[string]float64 `json:"timings,omitempty"`
	SourceFile      string             `json:"sourceFile,omitempty"`
	SourceLine      int                `json:"sourceLine,omitempty"`
	CallerFile      string             `json:"callerFile,omitempty"`  // outermost user-level frame (e.g. test script)
	CallerLine      int                `json:"callerLine,omitempty"`
}

type Debugger struct {
	vm   *vm
	vuID uint64 // VU identifier — maps to DAP thread ID in multi-VU debug

	// debugLoopDepth tracks nested vm.debug() invocations. Incremented on entry,
	// decremented on exit. Only when it reaches 0 is the VM truly finished
	// (not just a nested runTry/initFields completion). Used by the VM exit
	// handler to avoid prematurely setting vmExited=true during nested calls.
	debugLoopDepth int

	currentLine     int
	lastLine        int
	lastDebugLine   int
	lastDebugDepth  int
	breakpoints     map[string][]int // normalized filename -> sorted lines
	breakpointMutex sync.RWMutex
	breakpointIDs   map[bpKey]int // PERF: struct key, no string alloc on lookup
	conditionalBPs  map[bpKey]*conditionalBreakpoint
	breakPointCount int
	activationCh    chan chan DebuggerActivation
	currentCh       chan DebuggerActivation
	active          bool
	lastBreakpoint  struct {
		filename   string
		line       int
		pc         int
		stackDepth int
	}
	next                        bool
	stepIn                      bool
	continuing                  bool
	stepOverTargetDepth         int
	stepOverOriginalTargetDepth int // the depth at which Next() was originally called — never overwritten by re-activation
	stepOverStartLine           int
	stepOverLastPC              int      // last PC whose source-mapped line == stepOverStartLine; step-over won't break until currentPC > this
	stepOverLastPCPrg           *Program // the program stepOverLastPC was computed for; guard is invalid in any other program
	stepInLastPC                int      // last PC whose source-mapped line == stepInStartLine; stepIn skips sub-expressions across depth changes
	stepInLastPCPrg             *Program // the program stepInLastPC was computed for; guard is invalid in any other program
	stepInStartLine             int // the line where the current stepIn operation began
	stepInSkipEntryLine         int // when entering a new function via stepIn, skip all PCs on this line (the function declaration line)
	stepInSkipEntryPrg          *Program // the program the entry line skip is for
	stepOverMissCount           int // safety counter: instructions with startLine=0 and no valid currentLine
	suppressedInheritedLine     int // line to suppress after detecting inherited position from skipped if-body
	suppressedInheritedFile     string // file for the suppressed line (to avoid cross-file suppression)
	steppingFilename            string
	enableDebugLogging          bool
	breakpointCheckCount        int // TEMP: counter for unique line transitions logged
	bpCallLogCount              int // TEMP: counter for BP-ENTRY logs
	bpCallLogLastLine           int // TEMP: last line logged for BP-ENTRY dedup
	lastBPTraceLine             int    // last line logged in BP-TRACE (dedup)
	lastBPTraceFile             string // last file logged in BP-TRACE (dedup)
	skipPhaseEntryBreak         bool
	suppressStepInheritance     bool // true during _initFields to prevent global step state from re-enabling step flags
	lifecycleTransition         bool
	userCommandIssued           bool
	configuredCh                chan struct{}
	waitingForConfig            bool
	evalMutex                   sync.Mutex   // serializes evaluateComplexExpression calls only
	evalWG                      sync.WaitGroup // tracks in-progress eval/getter operations; activate() waits on this
	vmResuming                  atomic.Bool    // set when VM is about to resume; prevents new evals from starting
	hasConnection               bool

	// EventLoopDrainer is an optional hook set by the host (k6) to drain the
	// event loop queue during debug-console await evaluation. When set, the
	// debugger calls this function in a polling loop while waiting for a
	// Promise to settle. The function should process any pending callbacks
	// in the event loop queue (without blocking) and return true if any
	// callbacks were processed.
	EventLoopDrainer func() bool

	initPhase    bool
	initFilename string

	watchExpressions []watchExpr

	// httpCallLog records HTTP responses as they happen (even without pausing).
	// The k6 HTTP module pushes entries here; the DAP server drains them on each pause.
	httpCallLog   []HttpCallRecord
	httpCallLogMu sync.Mutex

	// --- PERF: hot-path caches ---

	// cachedPrg is the last vm.prg pointer we computed filename/normFilename for.
	// When vm.prg == cachedPrg we skip all string work in breakpoint().
	// NOTE: This is ONLY for the filename cache. The Line() cache uses cachedLinePrg.
	cachedPrg      *Program
	cachedFilename string // raw src.Name()
	cachedNormFile string // normalizeFilename(cachedFilename), slice of cachedFilename or equal

	// PERF: Line() cache — avoids expensive src.Position(sourceOffset(pc)) on every instruction.
	// Uses separate cachedLinePrg (not cachedPrg) to prevent Line() and refreshFilenameCache()
	// from interfering with each other's cache validity checks.
	cachedLinePrg    *Program
	cachedPC         int
	cachedLine       int
	cachedSrcMapFile string // source-mapped filename from Position(), normalized

	// PERF: cached source line split — avoids allocating a []string slice on every
	// getSourceVarInfo cache miss. Keyed by prg pointer since source is stable per-Program.
	cachedSourceLines    []string
	cachedSourceLinesPrg *Program

	// PERF: cached isUserFile result — avoids 3 lock acquisitions + string ops per instruction.
	// Two-level cache: first check the fast *Program pointer, then fall back to the
	// filename-keyed map. The map survives function calls within the same bundled file
	// (where *Program changes but the filename stays the same).
	// Invalidated when breakpoints change or on phase/run reset.
	cachedIsUserFile       bool
	cachedIsUserFilePrg    *Program
	cachedIsUserFileByName map[string]bool // normalized filename → isUserFile

	// PERF: cached normalizeFilenameForMatch result — avoids extension stripping per instruction.
	cachedBaseFile    string
	cachedBaseFilePrg *Program

	// initComplete is a local monotonic copy of globalInitTracker.HasAnyInitCompleted().
	// It is only ever flipped from false→true, never backwards, so once true we stop
	// asking the global tracker entirely (eliminating an RLock per instruction).
	initComplete bool

	// initBPSnapshot is a read-only copy of globalInitTracker.initBreakpointSet,
	// taken once when initComplete flips true. After that, all init-breakpoint
	// lookups use this local map with zero lock acquisitions.
	initBPSnapshot     map[initBPKey]bool
	initBPSnapshotDone bool

	// hasLocalBPs / hasGlobalBPs are set/cleared by SetBreakpoint/ClearBreakpoint.
	// When both are false, breakpoint() returns immediately with no lock acquisitions.
	hasLocalBPs  bool
	hasGlobalBPs bool

	// pausedVarSnapshot is built lazily on the first eval call per pause and reused
	// for all subsequent evals during the same pause (e.g. multiple variable hovers).
	// Cleared by Continue()/Next()/StepIn() before resuming.
	pausedVarSnapshot     map[string]Value
	pausedVarSnapshotLine int
	pausedVarSnapshotPC   int

	// PERF: Reusable map pool — avoids allocating make(map[string]Value, 64) on every
	// pause. On cache miss we clear() this map and rebuild it. On cache hit we return
	// pausedVarSnapshot directly (which points to the same map). Allocated once in
	// newDebugger(), never set to nil — only cleared between pauses.
	pausedVarPool map[string]Value

	// pausedVarSnapshotFrozen is set true during evaluateComplexExpression.
	// When frozen, buildPausedVarSnapshot returns the existing snapshot without
	// rebuilding — preventing corruption if the eval expression triggers a getter
	// that would otherwise overwrite the snapshot with stale data.
	pausedVarSnapshotFrozen bool

	// PERF: Source map name mapping cache — maps generated variable names (from
	// the bundler output) to original names (from the user's TypeScript source)
	// and vice versa. Built lazily per-program when the debugger is paused.
	// This is how Node.js / Chrome DevTools handle bundler variable renaming:
	// the source map's "names" array encodes original→generated name mappings
	// that the debugger uses to present original names and resolve lookups.
	//
	// genToOrig: generated name (stash key) → original name (user source)
	//   e.g., "test2" → "test" (bundler renamed due to import collision)
	// origToGen: original name (user hover/eval) → generated name (stash key)
	//   e.g., "test" → "test2"
	cachedNameMapPrg  *Program
	cachedGenToOrig   map[string]string // generated name → original name
	cachedOrigToGen   map[string]string // original name → generated name

	// ---

	varDeclLines     map[string]int
	sourceVarCache   map[sourceVarCacheKey]*sourceVarInfo // PERF: composite key fixes correctness + re-enables cache
	globalVarCache   map[string]bool
	sourceCacheValid bool

	varValueCache     map[string]Value
	varValueCacheLine int

	// PERF: Cache for GetAllStashVariables — avoids rescanning 25 modules + stash
	// chain on every call during the same pause. Invalidated when VM resumes.
	allStashVarsCache    map[string]Value
	allStashVarsCachePC  int // PC at time of capture — if unchanged, cache is valid
	allStashVarsCachePrg *Program

	functionCallStack   []FunctionCall
	pendingReturnValues map[int]Value
	returnValueCache    map[string]Value

	currentScopeDepth int
	scopeVariables    map[int]map[string]Value

	initRuntime *Runtime
	setupData   Value

	cachedGlobalNames map[string]bool
	globalsCaptured   bool

	vmExited bool
	vmDoneCh chan struct{}

	// uncaughtExceptionExit is set true when the VM exits due to an uncaught
	// exception (TypeError, ReferenceError, etc.) in runTryInner. This allows
	// Continue() and ResetVMExited() to distinguish between an uncaught-exception
	// exit and a lifecycle transition (init→setup→default). When true, stale
	// coordinator channels are drained in ResetVMExited() to prevent the next
	// iteration's activate() from picking up a channel that was intended for
	// the old (crashed) iteration — which manifests as the debugger "looping back"
	// to the same breakpoint instead of showing the exception.
	uncaughtExceptionExit bool

	// pendingUncaughtException is set by BreakOnException when the VM is
	// stepping (next/stepIn) and an uncaught exception occurs.  Instead of
	// calling activate() — which races with Continue()'s channel cleanup
	// (stale channel → immediate unblock → no pause) — we store the
	// activation here and let Continue() return it directly when vmDoneCh
	// closes.  This avoids the channel coordination race entirely.
	pendingUncaughtException *DebuggerActivation

	// exceptionWaitCh is created when an uncaught exception stores a
	// pendingUncaughtException. The VM goroutine blocks on this channel
	// (in runTryInner's defer) so that the k6 process doesn't exit before
	// the user has seen and dismissed the exception popup in the IDE.
	// The DAP layer closes this channel after the user clicks Continue.
	exceptionWaitCh chan struct{}

	pendingCh chan DebuggerActivation

	suppressDebugger   bool
	suppressDebugDepth int  // nesting depth of suppress calls; debugger active only when 0
	inEvalContext      bool // true while evaluateComplexExpression is running

	// asyncResumeActive is set true by onAsyncResume and cleared after the
	// first instruction in the debug loop. It tells the file-change check
	// to update steppingFilename instead of clearing step flags, because
	// the generator resumed in a different execution context (promise
	// reaction job) where the filename may not match.
	asyncResumeActive bool

	// inTestExecution is set true only while a Gherkin step function is being
	// called by runPickleStep. When false, ALL breakpoint/stepping logic is
	// skipped in vm.debug() so the debugger never fires during init, default()
	// setup, or gherkin orchestration — only inside actual step functions.
	inTestExecution bool

	// mu protects fields that may be written from external goroutines (e.g. RequestPause)
	mu sync.Mutex

	// lastException stores the most recent uncaught exception for exceptionInfo requests
	lastException Value
	// lastExceptionStack stores the call stack at the throw site for uncaught exceptions.
	// After handleThrow unwinds vm.callStack, CaptureCallStack returns empty. This saved
	// stack lets the DAP layer return a meaningful stackTrace when paused on an exception.
	lastExceptionStack []StackFrame

	// breakOnCaughtExceptions: pause on exceptions caught by try/catch ("All Exceptions" in IDE)
	breakOnCaughtExceptions bool
	// breakOnUncaughtExceptions: pause on uncaught exceptions ("Uncaught Exceptions" in IDE)
	breakOnUncaughtExceptions bool
	// exceptionBreakActive: true when debugger is paused due to an exception
	exceptionBreakActive bool

	// exceptionStash holds the stash chain captured at the throw site BEFORE
	// handleThrow unwinds vm.stash to the catch handler. This lets
	// buildPausedVarSnapshot show the local variables that were in scope when
	// the exception was thrown — matching Chrome DevTools / Node.js behaviour.
	// Cleared when the exception break ends (Continue/Step).
	exceptionStash *stash

	// exceptionSB holds the stack base (vm.sb) at the throw site.
	exceptionSB int

	// exceptionPrg holds the program at the throw site (for scope resolution).
	exceptionPrg *Program

	// onPause is called when the debugger pauses the VM (entering activate()).
	// k6 registers ExecutionState.Pause here so debug-pause time is excluded
	// from iteration duration metrics. May be nil.
	onPause func()
	// onResume is called when the debugger resumes the VM (leaving activate()).
	// k6 registers ExecutionState.Resume here. May be nil.
	onResume func()
}

// sourceVarCacheKey includes currentLine so variables declared after the current
// position are correctly excluded. Previously the cache was keyed only by
// functionStartLine which caused stale entries to miss newly-declared vars.
type sourceVarCacheKey struct {
	functionStartLine int
	currentLine       int
}

type sourceVarInfo struct {
	params    map[string]int
	locals    map[string]int
	declLines map[string]int
	numParams int
}

type watchExpr struct {
	id         int
	expression string
}

func newDebugger(vm *vm) *Debugger {
	if debugActivate || debugAll {
		fmt.Printf("[DEBUGGER] Creating new debugger (version=%s)\n", DebuggerVersion)
	}
	inheritConnection := false
	globalInitialized := globalDebugCoordinator.IsInitialized()
	if globalInitialized {
		inheritConnection = globalDebugCoordinator.HasGlobalConnection()
	}

	dbg := &Debugger{
		vm:                 vm,
		activationCh:       make(chan chan DebuggerActivation, 1),
		active:             false,
		breakpoints:        make(map[string][]int),
		breakpointIDs:      make(map[bpKey]int),
		lastLine:           0,
		lastDebugLine:      -1,
		lastDebugDepth:     -1,
		configuredCh:       make(chan struct{}),
		waitingForConfig:   true,
		varDeclLines:       make(map[string]int),
		sourceVarCache:     make(map[sourceVarCacheKey]*sourceVarInfo),
		globalVarCache:     make(map[string]bool),
		sourceCacheValid:   false,
		continuing:         false,
		enableDebugLogging: debugAll || os.Getenv("SOBEK_DEBUG_LOGGING") == "1",
		varValueCache:      make(map[string]Value),
		varValueCacheLine:  -1,
		hasConnection:      inheritConnection,
		vmDoneCh:           make(chan struct{}),
		pausedVarPool:      make(map[string]Value, 64), // PERF: pre-allocated, reused across pauses
	}
	// FIX: Initialize lastBreakpoint.pc to -1 so that pcAdvanced (currentPC != prevPC)
	// is true at PC=0 (the first instruction of any function). Without this, step-in
	// at function entry evaluates 0 != 0 = false and skips the first line.
	// ResetForPhaseTransition already does this correctly; newDebugger must match.
	dbg.lastBreakpoint.pc = -1
	if debugActivate {
		if inheritConnection {
			if debugActivate {
				fmt.Printf("[DEBUGGER] New debugger inherited global connection status: %v\n", inheritConnection)
			}
		} else {
			if debugActivate {
				fmt.Printf("[DEBUGGER] New debugger NOT inheriting connection (globalInitialized=%v, inheritConnection=%v)\n",
				globalInitialized, inheritConnection)
			}
		}
	}
	return dbg
}

type ActivationReason string

const (
	ProgramStartActivation      ActivationReason = "start"
	DebuggerStatementActivation ActivationReason = "debugger"
	BreakpointActivation        ActivationReason = "breakpoint"
	StepActivation              ActivationReason = "step"
	ExceptionActivation         ActivationReason = "exception"
	TerminatedActivation        ActivationReason = "terminated"
)

type DebuggerActivation struct {
	Reason        ActivationReason
	Filename      string
	Line          int
	Column        int    // 1-based column from source map — enables VS Code token highlighting
	ID            int
	Epoch         uint64
	VUID          uint64 // VU that triggered this activation (0 = VU0/lifecycle, >0 = VU N)
	ExceptionText string // non-empty when Reason == ExceptionActivation; shown in IDE popup
}

var globalBuiltinKeys = map[string]bool{
	"Object": true, "Function": true, "Array": true, "String": true, "globalThis": true,
	"NaN": true, "undefined": true, "Infinity": true, "isNaN": true, "parseInt": true,
	"parseFloat": true, "isFinite": true, "decodeURI": true, "decodeURIComponent": true,
	"encodeURI": true, "encodeURIComponent": true, "escape": true, "unescape": true,
	"Number": true, "RegExp": true, "Date": true, "Boolean": true, "Proxy": true,
	"Reflect": true, "Error": true, "AggregateError": true, "TypeError": true,
	"ReferenceError": true, "SyntaxError": true, "RangeError": true, "EvalError": true,
	"URIError": true, "GoError": true, "eval": true, "Math": true, "JSON": true,
	"ArrayBuffer": true, "DataView": true, "Uint8Array": true, "Uint8ClampedArray": true,
	"Int8Array": true, "Uint16Array": true, "Int16Array": true, "Uint32Array": true,
	"Int32Array": true, "Float32Array": true, "Float64Array": true, "Symbol": true,
	"WeakSet": true, "WeakMap": true, "Map": true, "Set": true, "Promise": true,
}

var globalUnsafeKeys = map[string]bool{
	"module":  true,
	"exports": true,
	"require": true,
}

var lifecycleFunctionKeys = map[string]bool{
	"setup":         true,
	"teardown":      true,
	"handleSummary": true,
	"default":       true,
}

func safeGetGlobalProperty(obj *Object, key unistring.String) (v Value) {
	defer func() {
		if r := recover(); r != nil {
			v = nil
		}
	}()
	return obj.self.getStr(key, nil)
}

func safeStringKeys(obj *Object) (names []string) {
	defer func() {
		if r := recover(); r != nil {
			names = nil
		}
	}()
	vals := obj.self.stringKeys(true, nil)
	names = make([]string, 0, len(vals))
	for _, v := range vals {
		if s, ok := v.(String); ok {
			names = append(names, s.String())
		}
	}
	return
}

func isIdentifierLike(name string) bool {
	if name == "" {
		return false
	}
	for i, r := range name {
		if i == 0 {
			if r != '$' && r != '_' && !unicode.IsLetter(r) {
				return false
			}
			continue
		}
		if r != '$' && r != '_' && !unicode.IsLetter(r) && !unicode.IsDigit(r) {
			return false
		}
	}
	return true
}

// normalizeFilename strips the file:// prefix. It returns a slice of the input
// string when possible (zero allocation) — only allocates when TrimPrefix would.
func normalizeFilename(filename string) string {
	const prefix = "file://"
	if strings.HasPrefix(filename, prefix) {
		return filename[len(prefix):] // slice, no allocation
	}
	return filename
}

// ensureInitBPSnapshot takes a one-time snapshot of the global init breakpoint set
// into a local map on the Debugger. After this, all init-breakpoint lookups use the
// local snapshot with zero lock acquisitions. Called from both vm.debug() and
// breakpoint() — previously the snapshot logic was duplicated in both places.
//
// PERF: The snapshot is taken exactly once per Debugger lifecycle (when initComplete
// flips true and initPhase is false). Subsequent calls are a no-op.
func (dbg *Debugger) ensureInitBPSnapshot() {
	if dbg.initBPSnapshotDone || dbg.initPhase {
		return
	}
	globalInitTracker.mu.RLock()
	dbg.initBPSnapshot = make(map[initBPKey]bool, len(globalInitTracker.initBreakpointSet))
	for k, v := range globalInitTracker.initBreakpointSet {
		dbg.initBPSnapshot[k] = v
	}
	globalInitTracker.mu.RUnlock()
	dbg.initBPSnapshotDone = true
}

// wasHitDuringInit checks if a breakpoint at normalizedFilename:line was already hit
// during the init phase. Uses the local snapshot if available, falling back to the
// global tracker. This is the single source of truth for init-BP dedup — called from
// both vm.debug() and breakpoint().
func (dbg *Debugger) wasHitDuringInit(normalizedFilename string, line int) bool {
	if dbg.initBPSnapshotDone {
		return dbg.initBPSnapshot[initBPKey{normalizedFilename, line}]
	}
	return GetGlobalInitTracker().WasAnyBreakpointHitDuringInit(normalizedFilename, line)
}

// refreshFilenameCache updates the per-debugger filename caches when vm.prg changes.
// Called at the top of breakpoint() and Filename(). Cheap when prg hasn't changed.
func (dbg *Debugger) refreshFilenameCache() {
	if dbg.vm.prg == dbg.cachedPrg {
		return
	}
	dbg.cachedPrg = dbg.vm.prg
	// NOTE: cachedLinePrg/cachedPC/cachedLine are separate — no need to invalidate them here.
	// Line() has its own prg check via cachedLinePrg.
	if dbg.vm.prg == nil || dbg.vm.prg.src == nil {
		dbg.cachedFilename = ""
		dbg.cachedNormFile = ""
		return
	}
	dbg.cachedFilename = dbg.vm.prg.src.Name()
	dbg.cachedNormFile = normalizeFilename(dbg.cachedFilename)
}

// IsUserSourceFilePath returns true if the given normalized filename looks like
// a user source file (local path with a JS/TS extension, not in node_modules).
// This is the single source of truth for the heuristic that decides whether
// a file is user code vs. internal k6 code — previously duplicated in multiple
// places within vm.debug().
func IsUserSourceFilePath(normalizedFilename string) bool {
	// External jslib URLs (tempo, httpx, etc.) loaded from https:// are
	// never user source — they must never trigger breakpoints or stepping.
	if strings.HasPrefix(normalizedFilename, "https://") ||
		strings.HasPrefix(normalizedFilename, "http://") {
		return false
	}

	return (strings.HasSuffix(normalizedFilename, ".ts") ||
		strings.HasSuffix(normalizedFilename, ".js") ||
		strings.HasSuffix(normalizedFilename, ".mjs") ||
		strings.HasSuffix(normalizedFilename, ".tsx")) &&
		strings.HasPrefix(normalizedFilename, "/") &&
		!strings.Contains(normalizedFilename, "node_modules")
}

func (dbg *Debugger) activate(reason ActivationReason, filename string, line int) {
	dbg.activateWithStepState(reason, filename, line, dbg.stepIn, dbg.next)
}

func (dbg *Debugger) activateWithStepState(reason ActivationReason, filename string, line int, wasStepIn bool, wasNext bool) {
	// PERF: only call time.Now() when debug logging is enabled.
	var activateStart time.Time
	if debugActivate {
		activateStart = time.Now()
	}

	savedStepIn := wasStepIn
	savedNext := wasNext
	savedLifecycleTransition := dbg.lifecycleTransition

	if debugActivate {
		fmt.Printf("[DEBUGGER-ACTIVATE-ENTRY] VU=%d At %s:%d - savedStepIn=%v, savedNext=%v, savedLifecycleTransition=%v, reason=%v\n",
			dbg.vuID,
			filename, line, savedStepIn, savedNext, savedLifecycleTransition, reason)
	}

	if globalDebugCoordinator.IsInitialized() {
		globalDebugCoordinator.SetActiveDebugger(dbg)
	}

	dbg.active = true
	// Allow DAP eval/getter operations now that the VM is paused.
	dbg.vmResuming.Store(false)

	savedCallDepth := dbg.callStackDepth()

	epoch := globalDebugCoordinator.NextGlobalEpoch()

	// CRITICAL: Notify the global stopped channel so that doContinue() in the
	// DAP layer can detect this stop even when Continue() was called on a
	// different VU's debugger. This is the cross-VU notification path.
	if globalDebugCoordinator.IsInitialized() {
		globalDebugCoordinator.NotifyGlobalStopped(DebuggerActivation{
			Filename: filename,
			Line:     line,
			Reason:   reason,
			Epoch:    epoch,
			VUID:     dbg.vuID,
		})
	}

	var ch chan DebuggerActivation

	if debugActivate {
		fmt.Printf("[DEBUGGER-ACTIVATE] Waiting for Continue() at %s:%d (hasConnection=%v, lifecycleTransition=%v)\n",
			filename, line, dbg.HasConnection(), savedLifecycleTransition)
	}

	if savedLifecycleTransition {
		if debugActivate {
			fmt.Printf("[DEBUGGER-ACTIVATE] Lifecycle transition: waiting on both channels (preferring global coordinator)\n")
		}
		// FIX: Use time.NewTimer instead of time.After to prevent goroutine leaks.
		// time.After creates a new timer+goroutine each iteration — if the select
		// resolves before 5s, the goroutine leaks until the timer fires.
		lifecycleTimer := time.NewTimer(5 * time.Second)
		defer lifecycleTimer.Stop()
	lifecycleWaitLoop:
		for {
			select {
			case ch = <-globalDebugCoordinator.ActivationChannel():
				if debugActivate {
					fmt.Printf("[DEBUGGER-ACTIVATE] Received from global coordinator (lifecycle transition)\n")
				}
				// PERF: read global step state once, reuse below.
				globalNext, globalStepIn, globalSteppingFile, globalTargetDepth := globalDebugCoordinator.GetGlobalStepState()
				userIssuedCommand := globalNext || globalStepIn

				if userIssuedCommand {
					globalDebugCoordinator.ConsumeLifecycleStepIn()
					localDepth := savedCallDepth
					if debugActivate {
						fmt.Printf("[DEBUGGER-ACTIVATE] Lifecycle transition: user issued command, applying global step state: next=%v, stepIn=%v, file=%s, globalDepth=%d, localDepth=%d, line=%d\n",
							globalNext, globalStepIn, globalSteppingFile, globalTargetDepth, localDepth, line)
					}
					dbg.next = globalNext
					dbg.stepIn = globalStepIn
					dbg.steppingFilename = globalSteppingFile
					if globalTargetDepth > 0 && globalTargetDepth < localDepth {
						dbg.stepOverTargetDepth = globalTargetDepth
					} else {
						dbg.stepOverTargetDepth = localDepth
					}
					dbg.stepOverStartLine = line
					dbg.userCommandIssued = true
					globalDebugCoordinator.ClearGlobalStepState()
				} else if globalDebugCoordinator.ConsumeLifecycleStepIn() {
					if debugActivate {
						fmt.Printf("[DEBUGGER-ACTIVATE] Lifecycle transition: using pendingLifecycleStepIn (no user command yet)\n")
					}
					dbg.stepIn = true
					dbg.next = false
					dbg.steppingFilename = filename
					dbg.stepOverTargetDepth = savedCallDepth
					globalDebugCoordinator.ClearGlobalStepState()
				}
				break lifecycleWaitLoop
			case ch = <-dbg.activationCh:
				if debugActivate {
					fmt.Printf("[DEBUGGER-ACTIVATE] Received from local channel (lifecycle transition - avoided global coordinator race)\n")
				}
				globalNext, globalStepIn, globalSteppingFile, globalTargetDepth := globalDebugCoordinator.GetGlobalStepState()
				userIssuedCommand := globalNext || globalStepIn

				if userIssuedCommand {
					globalDebugCoordinator.ConsumeLifecycleStepIn()
					localDepth := savedCallDepth
					if debugActivate {
						fmt.Printf("[DEBUGGER-ACTIVATE] Lifecycle transition (local): user issued command, applying global step state: next=%v, stepIn=%v, file=%s, globalDepth=%d, localDepth=%d, line=%d\n",
							globalNext, globalStepIn, globalSteppingFile, globalTargetDepth, localDepth, line)
					}
					dbg.next = globalNext
					dbg.stepIn = globalStepIn
					dbg.steppingFilename = globalSteppingFile
					if globalTargetDepth > 0 && globalTargetDepth < localDepth {
						dbg.stepOverTargetDepth = globalTargetDepth
					} else {
						dbg.stepOverTargetDepth = localDepth
					}
					dbg.stepOverStartLine = line
					dbg.userCommandIssued = true
					globalDebugCoordinator.ClearGlobalStepState()
				} else if globalDebugCoordinator.ConsumeLifecycleStepIn() {
					if debugActivate {
						fmt.Printf("[DEBUGGER-ACTIVATE] Lifecycle transition (local): using pendingLifecycleStepIn (no user command yet)\n")
					}
					dbg.stepIn = true
					dbg.next = false
					dbg.steppingFilename = filename
					dbg.stepOverTargetDepth = savedCallDepth
					globalDebugCoordinator.ClearGlobalStepState()
				}
				break lifecycleWaitLoop
			case <-lifecycleTimer.C:
				if debugActivate {
					fmt.Printf("[DEBUGGER-ACTIVATE] ⚠️ Lifecycle transition: timeout waiting for Continue() (5s). Still waiting...\n")
				}
				if globalDebugCoordinator.HasPendingLifecycleStepIn() {
					if debugActivate {
						fmt.Printf("[DEBUGGER-ACTIVATE] Lifecycle transition: has pending step-in, continuing to wait...\n")
					}
				} else {
					if debugActivate {
						fmt.Printf("[DEBUGGER-ACTIVATE] Lifecycle transition: no pending step-in, still waiting for user...\n")
					}
				}
				// Reset timer for next iteration
				lifecycleTimer.Reset(5 * time.Second)
			}
		}
	} else {
		// In multi-VU mode, use per-VU activation channel; in single-VU, use global.
		vuActivationCh := globalDebugCoordinator.GetVUActivationChannel(dbg.vuID)
		if debugActivate {
			fmt.Printf("[DEBUGGER-ACTIVATE] Non-lifecycle: waiting on both channels (multiVU=%v, vuID=%d, localCh=%p, vuCh=%p, vmExited=%v)\n",
				globalDebugCoordinator.IsMultiVUDebug(), dbg.vuID, dbg.activationCh, vuActivationCh, dbg.vmExited)
		}
		// readStepState reads step state from per-VU or global source as appropriate.
		readStepState := func() (bool, bool, string, int) {
			if globalDebugCoordinator.IsMultiVUDebug() {
				return globalDebugCoordinator.GetVUStepState(dbg.vuID)
			}
			return globalDebugCoordinator.GetGlobalStepState()
		}
		clearStepState := func() {
			if globalDebugCoordinator.IsMultiVUDebug() {
				globalDebugCoordinator.ClearVUStepState(dbg.vuID)
			} else {
				globalDebugCoordinator.ClearGlobalStepState()
			}
		}
		// applyStepState applies step state from the coordinator if available.
		applyStepState := func(source string) {
			if savedStepIn {
				if debugActivate {
					fmt.Printf("[DEBUGGER-ACTIVATE] Skipping step state check (lifecycle stepIn entry, stale state from previous phase)\n")
				}
				return
			}
			globalNext, globalStepIn, globalSteppingFile, globalTargetDepth := readStepState()
			if globalNext || globalStepIn {
				if debugActivate {
					fmt.Printf("[DEBUGGER-ACTIVATE] Non-lifecycle %s: applying step state: next=%v, stepIn=%v, file=%s, targetDepth=%d\n",
						source, globalNext, globalStepIn, globalSteppingFile, globalTargetDepth)
				}
				dbg.next = globalNext
				dbg.stepIn = globalStepIn
				dbg.steppingFilename = globalSteppingFile
				localDepth := savedCallDepth
				if globalTargetDepth > 0 && globalTargetDepth < localDepth {
					dbg.stepOverTargetDepth = globalTargetDepth
				} else {
					dbg.stepOverTargetDepth = localDepth
				}
				if debugActivate {
					fmt.Printf("[DEBUGGER-ACTIVATE] ✅ Using depth=%d (local=%d, global=%d, line=%d)\n",
						dbg.stepOverTargetDepth, localDepth, globalTargetDepth, line)
				}
				dbg.stepOverStartLine = line
				dbg.userCommandIssued = true
				clearStepState()
			}
		}
		for {
			select {
			case ch = <-dbg.activationCh:
				if debugActivate {
					fmt.Printf("[DEBUGGER-ACTIVATE] Received from local channel (non-lifecycle, ch=%p)\n", ch)
				}
				applyStepState("local")
			case ch = <-vuActivationCh:
				if debugActivate {
					fmt.Printf("[DEBUGGER-ACTIVATE] Received from coordinator (non-lifecycle, multiVU=%v, vuID=%d, ch=%p)\n", globalDebugCoordinator.IsMultiVUDebug(), dbg.vuID, ch)
				}
				applyStepState("coordinator")
			case ch = <-globalDebugCoordinator.ActivationChannel():
				// CROSS-VU FIX: After a lifecycle transition (init→default),
				// Continue() runs on the old VU's debugger and can't reach the
				// new VU's per-VU channel. It falls back to the global channel.
				// By listening here, ANY VU's activate() can pick it up and
				// respond, breaking the deadlock.
				if debugActivate {
					fmt.Printf("[DEBUGGER-ACTIVATE] Received from global channel (cross-VU lifecycle transition, vuID=%d, ch=%p)\n", dbg.vuID, ch)
				}
				applyStepState("global-crossVU")
			}
			// Guard: if ch is nil (a stale Continue() sent dbg.currentCh after
			// ResetForPhaseTransition nil'd it), retry — sending on a nil channel
			// blocks forever and is unrecoverable.
			if ch != nil {
				break
			}
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] ⚠️ Received nil channel — retrying select\n")
			}
		}
	}

	id := 0
	if debugActivate {
		channelWait := time.Since(activateStart)
		if debugActivate {
			fmt.Printf("[DEBUGGER-ACTIVATE] Channel handshake completed in %dms at %s:%d\n",
			channelWait.Milliseconds(), filename, line)
		}
	}
	if reason != DebuggerStatementActivation {
		id = globalBreakpoints.GetBreakpointID(filename, line)
		if id == 0 {
			dbg.breakpointMutex.RLock()
			id = dbg.breakpointIDs[bpKey{filename, line}]
			dbg.breakpointMutex.RUnlock()
		}
	}

	dbg.pendingCh = ch

	// Notify k6 that the VM is now paused so iteration-duration timers
	// stop counting while the user inspects variables / steps.
	if globalDebugCoordinator.IsInitialized() {
		globalDebugCoordinator.callPause()
	} else if dbg.onPause != nil {
		dbg.onPause()
	}

	// CRITICAL FIX: Protect the send from panicking when the channel was
	// closed by a concurrent Continue()/Next()/StepIn() call on another
	// goroutine. If the channel is stale (closed), go back and wait for a
	// fresh channel instead of skipping the pause.
	//
	// FIX: Use time.NewTimer instead of time.After to prevent goroutine leaks.
	// time.After creates a timer+goroutine that is never collected if the select
	// resolves before the timeout fires.
	retryTimer := time.NewTimer(5 * time.Second)
	defer retryTimer.Stop()
	for retries := 0; retries < 5; retries++ {
		act := DebuggerActivation{
			Reason:   reason,
			Filename: filename,
			Line:     line,
			Column:   dbg.Column(),
			ID:       id,
			Epoch:    epoch,
			VUID:     dbg.vuID,
		}
		if reason == ExceptionActivation && dbg.lastException != nil {
			act.ExceptionText = dbg.lastException.String()
		}
		sendOK := safeSendActivation(ch, act)
		if sendOK {
			break
		}
		if debugActivate {
			fmt.Printf("[DEBUGGER-ACTIVATE] ⚠️ Channel was closed (stale) at %s:%d — retrying (attempt %d/5)\n",
				filename, line, retries+1)
		}
		// Wait for a fresh channel from Continue()
		if !retryTimer.Stop() {
			select {
			case <-retryTimer.C:
			default:
			}
		}
		retryTimer.Reset(5 * time.Second)
		select {
		case ch = <-dbg.activationCh:
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Got fresh channel from local (retry)\n")
			}
			dbg.pendingCh = ch
		case ch = <-globalDebugCoordinator.ActivationChannel():
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Got fresh channel from global (retry)\n")
			}
			dbg.pendingCh = ch
		case <-retryTimer.C:
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] ⚠️ Timeout waiting for fresh channel at %s:%d — resuming VM\n",
					filename, line)
			}
			if globalDebugCoordinator.IsInitialized() {
				globalDebugCoordinator.callResume()
			} else if dbg.onResume != nil {
				dbg.onResume()
			}
			dbg.pendingCh = nil
			dbg.active = false
			return
		}
		// Check global step state on the fresh channel
		globalNext, globalStepIn, globalSteppingFile, globalTargetDepth := globalDebugCoordinator.GetGlobalStepState()
		if globalNext || globalStepIn {
			dbg.next = globalNext
			dbg.stepIn = globalStepIn
			dbg.steppingFilename = globalSteppingFile
			if globalTargetDepth > 0 {
				dbg.stepOverTargetDepth = globalTargetDepth
			}
			dbg.stepOverStartLine = line
			dbg.userCommandIssued = true
			globalDebugCoordinator.ClearGlobalStepState()
		}
	}

	// Wait for Continue signal (close of ch).
	<-ch

	// Signal that the VM is about to resume. In-progress eval/getter operations
	// will see this flag and skip restoring stale VM state. New operations will
	// be rejected immediately.
	dbg.vmResuming.Store(true)

	// CRITICAL: Wait for in-progress eval/getter operations to finish before
	// resuming the VM. Without this, evaluateComplexExpression (running on the
	// DAP goroutine) and the VM goroutine (resuming here) race on vm.tryStack,
	// vm.callStack, vm.sp, etc. — causing "slice bounds out of range" panics
	// that crash the entire k6 process.
	//
	// The timeout prevents indefinite stalls if the IDE keeps sending evaluate
	// requests. 100ms is enough for any in-flight eval to see vmResuming and
	// bail out, but short enough to not noticeably delay VM resume.
	evalDone := make(chan struct{})
	go func() {
		dbg.evalWG.Wait()
		close(evalDone)
	}()
	select {
	case <-evalDone:
		// All evals finished cleanly
	case <-time.After(100 * time.Millisecond):
		if debugActivate {
			fmt.Printf("[DEBUGGER-ACTIVATE] ⚠️ Timeout waiting for eval operations to finish (100ms) — resuming anyway\n")
		}
	}

	// Notify k6 that the VM is about to resume — restart iteration-duration timers.
	if globalDebugCoordinator.IsInitialized() {
		globalDebugCoordinator.callResume()
	} else if dbg.onResume != nil {
		dbg.onResume()
	}

	dbg.pendingCh = nil

	// PERF: read global step state once after Continue signal, reuse for all checks below.
	globalNext, globalStepIn, globalSteppingFile, globalTargetDepth := globalDebugCoordinator.GetGlobalStepState()
	userCommand := false

	if savedStepIn && !dbg.userCommandIssued {
		if globalNext || globalStepIn {
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Post-Continue: IGNORING stale global state (lifecycle stepIn entry): next=%v, stepIn=%v, file=%s, depth=%d\n",
					globalNext, globalStepIn, globalSteppingFile, globalTargetDepth)
			}
			globalDebugCoordinator.ClearGlobalStepState()
		}
	} else {
		userCommand = globalNext || globalStepIn
		if userCommand {
			dbg.next = globalNext
			dbg.stepIn = globalStepIn
			if globalSteppingFile != "" {
				dbg.steppingFilename = globalSteppingFile
			}
			localDepth := savedCallDepth
			// For step-out, globalTargetDepth < localDepth. Use it so we
			// break when depth drops to the caller's level.
			if globalTargetDepth > 0 && globalTargetDepth < localDepth {
				dbg.stepOverTargetDepth = globalTargetDepth
			} else {
				dbg.stepOverTargetDepth = localDepth
			}
			dbg.stepOverStartLine = line
			globalDebugCoordinator.ClearGlobalStepState()
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Applied user command from global state: next=%v, stepIn=%v, file=%s, globalDepth=%d, localDepth=%d, appliedDepth=%d, startLine=%d\n",
					globalNext, globalStepIn, globalSteppingFile, globalTargetDepth, localDepth, dbg.stepOverTargetDepth, line)
			}
		}
	}

	if dbg.userCommandIssued {
		userCommand = true
	}
	dbg.userCommandIssued = false

	if debugActivate {
		fmt.Printf("[DEBUGGER-ACTIVATE-POST] After Continue signal: stepIn=%v (saved=%v), next=%v (saved=%v), userCommandIssued=%v, lifecycleTransition=%v\n",
			dbg.stepIn, savedStepIn, dbg.next, savedNext, userCommand, savedLifecycleTransition)
	}

	if savedLifecycleTransition {
		dbg.lifecycleTransition = false
		dbg.lastBreakpoint.line = line
		dbg.lastBreakpoint.filename = filename
		dbg.lastBreakpoint.pc = dbg.vm.pc
		dbg.lastBreakpoint.stackDepth = savedCallDepth
		// For lifecycle transitions, reset target depth to the new phase's depth
		// and also reset the original target since this is a new stepping context
		dbg.stepOverTargetDepth = savedCallDepth
		dbg.stepOverOriginalTargetDepth = savedCallDepth

		if userCommand {
			dbg.steppingFilename = filename
			if dbg.next {
				dbg.stepOverStartLine = line
			}
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Lifecycle transition complete, honoring user's command: stepIn=%v, next=%v, steppingFilename=%s\n",
					dbg.stepIn, dbg.next, filename)
			}
		} else {
			dbg.stepIn = false
			dbg.next = false
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Lifecycle transition complete, no user command, cleared step flags\n")
			}
		}
	} else if userCommand {
		if debugActivate {
			fmt.Printf("[DEBUGGER-ACTIVATE] Normal breakpoint, user issued command: stepIn=%v, next=%v\n",
				dbg.stepIn, dbg.next)
		}
		dbg.lastBreakpoint.line = line
		dbg.lastBreakpoint.filename = filename
		dbg.lastBreakpoint.pc = dbg.vm.pc
		dbg.lastBreakpoint.stackDepth = savedCallDepth
		if dbg.next {
			dbg.stepOverStartLine = line
			// Only reset targetDepth to current depth for normal step-over.
			// For step-out, stepOverTargetDepth was already set to a shallower
			// depth by the post-Continue code — don't overwrite it.
			if dbg.stepOverTargetDepth == 0 || dbg.stepOverTargetDepth >= savedCallDepth {
				dbg.stepOverTargetDepth = savedCallDepth
				dbg.stepOverOriginalTargetDepth = savedCallDepth
			}
			if dbg.steppingFilename == "" {
				dbg.steppingFilename = filename
			}
		}
		if dbg.stepIn {
			if dbg.steppingFilename == "" {
				dbg.steppingFilename = filename
			}
		}
	} else {
		dbg.stepIn = savedStepIn
		dbg.next = savedNext
		if dbg.next {
			// FIX #1: NEVER let a re-activation during a step change the target depth.
			// stepOverOriginalTargetDepth was set authoritively by Next().
			// savedCallDepth may be deeper (inside a called function that hit a
			// breakpoint mid-step-over), so using it would make step-over stop
			// prematurely inside functions it should be stepping over.
			if dbg.stepOverOriginalTargetDepth > 0 {
				dbg.stepOverTargetDepth = dbg.stepOverOriginalTargetDepth
			}
			// FIX #2: Do NOT reset stepOverStartLine here.
			// stepOverStartLine is set by Next() and represents the line where
			// the user pressed step-over. Resetting it on every re-activation
			// (e.g., when a breakpoint fires mid-step) shifts the "don't stop
			// on the line we started from" guard, causing phantom stops or
			// skipped lines. Only Next() should set stepOverStartLine.
			dbg.steppingFilename = filename
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Restored next=true, preserved stepOverStartLine=%d, targetDepth=%d (original=%d, saved=%d)\n",
					dbg.stepOverStartLine, dbg.stepOverTargetDepth, dbg.stepOverOriginalTargetDepth, savedCallDepth)
			}
		}
		if debugActivate {
			fmt.Printf("[DEBUGGER-ACTIVATE] Normal breakpoint, no user command detected, restored saved: stepIn=%v, next=%v, stepOverStartLine=%d\n",
				savedStepIn, savedNext, dbg.stepOverStartLine)
		}
	}

	// PERF: invalidate the per-pause variable snapshot now that we're resuming.
	dbg.pausedVarSnapshot = nil

	dbg.active = false

	if debugActivate {
		totalActivate := time.Since(activateStart)
		if debugActivate {
			fmt.Printf("[DEBUGGER-ACTIVATE] Total activate() time: %dms at %s:%d\n",
			totalActivate.Milliseconds(), filename, line)
		}
	}
}

type trackedChan struct {
	ch        chan DebuggerActivation
	closeOnce sync.Once
}

func newTrackedChan() *trackedChan {
	return &trackedChan{
		ch: make(chan DebuggerActivation),
	}
}

func (tc *trackedChan) Close() {
	if tc == nil {
		return
	}
	tc.closeOnce.Do(func() {
		close(tc.ch)
	})
}

func safeCloseActivationCh(ch chan DebuggerActivation) {
	if ch == nil {
		return
	}
	// Use defer+recover to handle the race where another goroutine closes
	// the channel between our check and our close() call.
	// NOTE: The previous select{case <-ch / default: close(ch)} pattern had
	// a TOCTOU race: another goroutine could close the channel between the
	// default branch (channel is open) and the close() call, causing a panic.
	// The recover-based approach is the only correct way to handle this in Go.
	defer func() {
		if r := recover(); r != nil {
			if debugContinue {
				fmt.Printf("[DEBUGGER-SAFE-CLOSE] Recovered from close on already-closed channel: %v\n", r)
			}
		}
	}()
	close(ch)
}

// safeSendActivation sends an activation on ch, recovering gracefully if ch
// was closed by a concurrent Continue()/Next()/StepIn() call.
// Returns true if the send succeeded, false if the channel was closed.
func safeSendActivation(ch chan DebuggerActivation, activation DebuggerActivation) (ok bool) {
	defer func() {
		if r := recover(); r != nil {
			// "send on closed channel" — the DAP handler already moved on.
			if debugActivate {
				fmt.Printf("[DEBUGGER-SAFE-SEND] Recovered from send on closed channel: %v\n", r)
			}
			ok = false
		}
	}()
	ch <- activation
	return true
}

func (dbg *Debugger) Continue() DebuggerActivation {
	var continueStart time.Time
	if debugContinue {
		continueStart = time.Now()
	}


	if dbg.pendingCh != nil {
		if dbg.pendingCh != dbg.currentCh {
			safeCloseActivationCh(dbg.pendingCh)
		}
		dbg.pendingCh = nil
	}
	if dbg.currentCh != nil {
		safeCloseActivationCh(dbg.currentCh)
		dbg.currentCh = nil
	}
	dbg.currentCh = make(chan DebuggerActivation)

	if debugContinue {
		fmt.Printf("[DEBUGGER-CONTINUE] Attempting to send continue signal (vuID=%d, stepIn=%v, next=%v, lifecycleTransition=%v)\n",
			dbg.vuID, dbg.stepIn, dbg.next, dbg.lifecycleTransition)
	}

	isMultiVU := globalDebugCoordinator.IsMultiVUDebug()

	// Determine if the local VM is already dead.
	localDead := dbg.vmExited
	if !localDead {
		select {
		case <-dbg.vmDoneCh:
			localDead = true
		default:
		}
	}
	if !localDead {
		if activeDbg := globalDebugCoordinator.GetActiveDebugger(); activeDbg != nil {
			if activeDbg.vmExited || activeDbg != dbg {
				localDead = true
			}
		}
	}

	if debugContinue {
		fmt.Printf("[DEBUGGER-CONTINUE] localDead=%v, isMultiVU=%v, vuID=%d\n",
			localDead, isMultiVU, dbg.vuID)
	}

	// ─── Phase 1: Local VM is alive ────────────────────────────────────
	// Send currentCh to activationCh, then block on currentCh + vmDoneCh.
	// No timeouts — activate() will eventually receive from activationCh
	// when the VM hits a breakpoint/step. vmDoneCh fires if the VM exits.
	if !localDead {
		// Try to send currentCh to both local and coordinator channels.
		// The first one that activate() reads from will get our channel.
		vuActivationCh := globalDebugCoordinator.GetVUActivationChannel(dbg.vuID)

		// Non-blocking attempt to send to coordinator first (for step state),
		// then blocking send to local activationCh + vmDoneCh.
		sent := false
		select {
		case vuActivationCh <- dbg.currentCh:
			sent = true
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] Sent to coordinator channel (vuID=%d)\n", dbg.vuID)
			}
		default:
		}
		if !sent {
			// Block: send to either local activationCh or detect VM exit.
			select {
			case dbg.activationCh <- dbg.currentCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] Sent to local activationCh\n")
				}
			case <-dbg.vmDoneCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] VM exited while trying to send to activationCh\n")
				}
				localDead = true
			}
		}

		// If we successfully sent, block on currentCh + vmDoneCh for the response.
		if !localDead {
			select {
			case activation := <-dbg.currentCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] ✅ Received activation: %s:%d (vuID=%d, wait=%dms)\n",
						activation.Filename, activation.Line, activation.VUID,
						time.Since(continueStart).Milliseconds())
				}
				return activation
			case <-dbg.vmDoneCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] VM exited while waiting for activation response\n")
				}
				// Drain stale entry from activationCh if we sent one.
				select {
				case <-dbg.activationCh:
				default:
				}
				localDead = true
			}
		}
	}

	// ─── Phase 2: Local VM is dead (lifecycle transition or test end) ──
	// The VM exited. We need to wait for a NEW VM to start and call
	// activate(), or detect that all VMs are done (test finished).
	// No timeouts — we block on currentCh and use a notification channel
	// from the coordinator for "all done" detection.
	if debugContinue {
		fmt.Printf("[DEBUGGER-CONTINUE] Entering dead-VM phase (vuID=%d)\n", dbg.vuID)
	}

	crossVUSent := false

	for {
		// Recreate currentCh if it was nil'd by ResetForPhaseTransition.
		if dbg.currentCh == nil {
			dbg.currentCh = make(chan DebuggerActivation)
			crossVUSent = false
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] Recreated currentCh after phase transition\n")
			}
		}

		// Check: all VMs exited → test is finished.
		allVMsExited := true
		allDbgs := globalDebugCoordinator.GetAllDebuggers()
		for _, d := range allDbgs {
			if !d.vmExited {
				select {
				case <-d.vmDoneCh:
				default:
					allVMsExited = false
				}
			}
		}
		if allVMsExited && len(allDbgs) == 0 {
			allVMsExited = true
		}
		if allVMsExited && globalDebugCoordinator.HasWaitForFunctionEntry() {
			allVMsExited = false
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] All VMs exited but waitForFunctionEntry set — waiting\n")
			}
		}
		if allVMsExited {
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] All VMs exited — returning terminated\n")
			}
			// Clear stale step state.
			if isMultiVU {
				globalDebugCoordinator.ClearVUStepState(dbg.vuID)
			} else {
				globalDebugCoordinator.ClearGlobalStepState()
			}
			return DebuggerActivation{
				Reason:   TerminatedActivation,
				Filename: dbg.Filename(),
				Line:     dbg.Line(),
				VUID:     dbg.vuID,
			}
		}

		// Check: pending uncaught exception.
		if dbg.pendingUncaughtException != nil {
			activation := *dbg.pendingUncaughtException
			dbg.pendingUncaughtException = nil
			dbg.active = true
			dbg.exceptionBreakActive = true
			if globalDebugCoordinator.IsInitialized() {
				globalDebugCoordinator.SetActiveDebugger(dbg)
			}
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] ✅ Returning pending uncaught exception: %s:%d\n",
					activation.Filename, activation.Line)
			}
			return activation
		}

		// Send currentCh to all reachable channels (cross-VU routing).
		if !crossVUSent {
			dbg.sendToAllActivationChannels(isMultiVU)
			crossVUSent = true
		} else if activeDbg := globalDebugCoordinator.GetActiveDebugger(); activeDbg != nil && activeDbg != dbg && activeDbg.IsActive() {
			// A new active debugger appeared — re-route.
			dbg.currentCh = make(chan DebuggerActivation)
			dbg.sendToAllActivationChannels(isMultiVU)
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] Re-routed to new active debugger (vuID=%d)\n", activeDbg.GetVUID())
			}
		}

		// Block: wait for activation on currentCh. Use a poll interval ONLY
		// to re-check allVMsExited / new active debugger — not for the
		// activation itself. 500ms is generous; this only matters for
		// detecting test-end or cross-VU debugger changes.
		pollTimer := time.NewTimer(500 * time.Millisecond)
		select {
		case activation := <-dbg.currentCh:
			pollTimer.Stop()
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] ✅ Received activation (dead-VM phase): %s:%d (vuID=%d, wait=%dms)\n",
					activation.Filename, activation.Line, activation.VUID,
					time.Since(continueStart).Milliseconds())
			}
			return activation
		case <-pollTimer.C:
			// Re-check allVMsExited, pending exceptions, new active debuggers.
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] Dead-VM poll: re-checking state\n")
			}
		}
	}
}

// sendToAllActivationChannels attempts to send dbg.currentCh to all reachable
// activation channels for cross-VU routing when the local VM has exited.
func (dbg *Debugger) sendToAllActivationChannels(isMultiVU bool) {
	if debugContinue {
		fmt.Printf("[DEBUGGER-CONTINUE] sendToAllActivationChannels (vuID=%d, isMultiVU=%v)\n", dbg.vuID, isMultiVU)
	}

	if isMultiVU {
		// Try active debugger's local channel first.
		if activeDbg := globalDebugCoordinator.GetActiveDebugger(); activeDbg != nil && activeDbg != dbg {
			targetCh := activeDbg.ActivationCh()
			select {
			case targetCh <- dbg.currentCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] ✅ Sent to active debugger's local channel (vuID=%d→%d)\n",
						dbg.vuID, activeDbg.GetVUID())
				}
				return
			default:
			}
			// Try active debugger's per-VU coordinator channel.
			targetVUCh := globalDebugCoordinator.GetVUActivationChannel(activeDbg.GetVUID())
			select {
			case <-targetVUCh:
			default:
			}
			select {
			case targetVUCh <- dbg.currentCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] ✅ Sent to active debugger's per-VU channel (vuID=%d→%d)\n",
						dbg.vuID, activeDbg.GetVUID())
				}
				return
			default:
			}
		}
	}

	// Global activation channel — any VU's activate() can pick this up.
	globalCh := globalDebugCoordinator.ActivationChannel()
	select {
	case <-globalCh:
	default:
	}
	select {
	case globalCh <- dbg.currentCh:
		if debugContinue {
			fmt.Printf("[DEBUGGER-CONTINUE] Sent to global activation channel (vuID=%d)\n", dbg.vuID)
		}
		return
	default:
	}

	// Own per-VU channel as last resort.
	vuActivationCh := globalDebugCoordinator.GetVUActivationChannel(dbg.vuID)
	select {
	case <-vuActivationCh:
	default:
	}
	select {
	case vuActivationCh <- dbg.currentCh:
		if debugContinue {
			fmt.Printf("[DEBUGGER-CONTINUE] Sent to own per-VU channel (vuID=%d)\n", dbg.vuID)
		}
	default:
		if debugContinue {
			fmt.Printf("[DEBUGGER-CONTINUE] All channels full (vuID=%d)\n", dbg.vuID)
		}
	}
}

// SetConditionalBreakpoint sets a breakpoint that only fires when condition is truthy.
// condition="" means unconditional (same as SetBreakpoint).
func (dbg *Debugger) SetConditionalBreakpoint(filename string, line int, condition string) (id int, err error) {
	id, err = dbg.SetBreakpoint(filename, line)
	if err != nil && err.Error() == "breakpoint exists" {
		id = globalBreakpoints.GetBreakpointID(normalizeFilename(filename), line)
		err = nil
	}
	if condition != "" {
		if dbg.conditionalBPs == nil {
			dbg.conditionalBPs = make(map[bpKey]*conditionalBreakpoint)
		}
		key := bpKey{normalizeFilename(filename), line}
		dbg.conditionalBPs[key] = &conditionalBreakpoint{condition: condition}
	}
	return
}

// shouldFireBreakpoint checks conditional breakpoints.
// Returns true if the breakpoint should cause a pause.
func (dbg *Debugger) shouldFireBreakpoint(normalizedFilename string, line int) bool {
	if dbg.conditionalBPs == nil {
		return true
	}
	key := bpKey{normalizedFilename, line}
	cond, exists := dbg.conditionalBPs[key]
	if !exists {
		return true // unconditional
	}
	cond.hitCount++
	// Hit count condition
	if cond.hitTarget > 0 && cond.hitCount%cond.hitTarget != 0 {
		return false
	}
	// Logpoint — evaluate message, print, don't pause
	if cond.logMessage != "" {
		msg, evalErr := dbg.Evaluate(cond.logMessage)
		if evalErr == nil && msg != nil {
			fmt.Printf("[LOGPOINT] %s:%d: %s\n", normalizedFilename, line, msg.String())
		} else {
			fmt.Printf("[LOGPOINT] %s:%d: %s\n", normalizedFilename, line, cond.logMessage)
		}
		return false // logpoints never pause
	}
	// Expression condition
	if cond.condition != "" {
		result, evalErr := dbg.Evaluate(cond.condition)
		if evalErr != nil {
			// Condition error — fire the breakpoint so the user sees the problem
			if debugBreakpoint {
				fmt.Printf("[CONDITIONAL-BP] Condition error at %s:%d: %v\n", normalizedFilename, line, evalErr)
			}
			return true
		}
		fires := result != nil && result.ToBoolean()
		if debugBreakpoint {
			fmt.Printf("[CONDITIONAL-BP] %s:%d condition=%q result=%v fires=%v\n",
				normalizedFilename, line, cond.condition, result, fires)
		}
		return fires
	}
	return true
}

// SetLogpoint sets a breakpoint that logs a message without pausing execution.
// message is a JS expression that gets evaluated and printed.
func (dbg *Debugger) SetLogpoint(filename string, line int, message string) (id int, err error) {
	id, err = dbg.SetBreakpoint(filename, line)
	if err != nil && err.Error() == "breakpoint exists" {
		id = globalBreakpoints.GetBreakpointID(normalizeFilename(filename), line)
		err = nil
	}
	if dbg.conditionalBPs == nil {
		dbg.conditionalBPs = make(map[bpKey]*conditionalBreakpoint)
	}
	key := bpKey{normalizeFilename(filename), line}
	dbg.conditionalBPs[key] = &conditionalBreakpoint{logMessage: message}
	return
}

// SetHitCountBreakpoint fires only every N hits.
func (dbg *Debugger) SetHitCountBreakpoint(filename string, line int, every int) (id int, err error) {
	id, err = dbg.SetBreakpoint(filename, line)
	if err != nil && err.Error() == "breakpoint exists" {
		id = globalBreakpoints.GetBreakpointID(normalizeFilename(filename), line)
		err = nil
	}
	if dbg.conditionalBPs == nil {
		dbg.conditionalBPs = make(map[bpKey]*conditionalBreakpoint)
	}
	key := bpKey{normalizeFilename(filename), line}
	dbg.conditionalBPs[key] = &conditionalBreakpoint{hitTarget: every}
	return
}

func (dbg *Debugger) SetConfigured() {
	if dbg.waitingForConfig {
		dbg.waitingForConfig = false
		close(dbg.configuredCh)
	}
}

func (dbg *Debugger) SetHasConnection(connected bool) {
	dbg.hasConnection = connected
	if globalDebugCoordinator.IsInitialized() {
		globalDebugCoordinator.SetGlobalConnection(connected)
	}
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] Connection status set to: %v\n", connected)
	}
}

func (dbg *Debugger) HasConnection() bool {
	if dbg.hasConnection {
		return true
	}
	if globalDebugCoordinator.IsInitialized() {
		return globalDebugCoordinator.HasGlobalConnection()
	}
	return false
}

// SetPauseResumeCallbacks registers callbacks that are invoked when the debugger
// pauses and resumes the VM. k6 uses this to call ExecutionState.Pause()/Resume()
// so that debug-pause time is excluded from iteration duration metrics and the
// progress bar freezes while the user is inspecting variables / stepping.
//
// Both callbacks must be goroutine-safe. They are called on the VM goroutine
// inside activate(). Pass nil to clear a previously registered callback.
func (dbg *Debugger) SetPauseResumeCallbacks(onPause, onResume func()) {
	dbg.mu.Lock()
	dbg.onPause = onPause
	dbg.onResume = onResume
	dbg.mu.Unlock()
}

// SetSuppressBreakpoints temporarily suppresses ALL debugger activity when v=true.
// Use this to prevent breakpoints firing during Go→JS orchestration calls (e.g.
// gherkin's Run() internals). Un-suppress before calling actual user step functions.
func (dbg *Debugger) SetSuppressBreakpoints(v bool) {
	dbg.suppressDebugger = v
}

// SetInTestExecution marks whether the VM is currently executing a Gherkin step
// function. When false, vm.debug() skips ALL breakpoint and stepping logic so
// the debugger never fires during init, default() setup, or gherkin orchestration.
// Set true before calling the step callable; defer reset to false.
func (dbg *Debugger) SetInTestExecution(v bool) {
	dbg.inTestExecution = v
}

// SetLifecycleTransition controls the lifecycleTransition flag.
// Set true before calling a user JS function from Go; set false after.
func (dbg *Debugger) SetLifecycleTransition(v bool) {
	dbg.lifecycleTransition = v
}

// SetSuppressDefaultEntry tells sobek to suppress all breakpoints when the
// "default" JS function is next entered. Gherkin calls this after LoadFeature
// to prevent the debugger stopping on step-definition bodies during setup.
func (c *GlobalDebugCoordinator) SetSuppressDefaultEntry(v bool) {
	c.mu.Lock()
	c.suppressDefaultEntry = v
	c.mu.Unlock()
}

// GetSuppressDefaultEntry returns the current suppressDefaultEntry flag.
func (c *GlobalDebugCoordinator) GetSuppressDefaultEntry() bool {
	c.mu.RLock()
	defer c.mu.RUnlock()
	return c.suppressDefaultEntry
}

func (dbg *Debugger) EnableDebugLogging() {
	dbg.enableDebugLogging = true
}

func (dbg *Debugger) DisableDebugLogging() {
	dbg.enableDebugLogging = false
}

// SetHasGlobalBPs allows external code to flag that the global breakpoint registry
// has breakpoints, so breakpoint() will check globalBreakpoints without needing
// to copy every breakpoint into the local debugger.
func (dbg *Debugger) SetHasGlobalBPs(v bool) {
	dbg.hasGlobalBPs = v
}

func (dbg *Debugger) SetInitPhase(inInit bool) {
	wasInInit := dbg.initPhase
	dbg.initPhase = inInit

	if debugInit {
		fmt.Printf("[DEBUGGER] Init phase set to: %v\n", inInit)
	}

	if inInit && !wasInInit {
		if debugInit || debugAll {
			// DIAGNOSTIC: Dump all registered breakpoints to help trace filename mismatches
			allBPs := globalBreakpoints.GetAllBreakpoints()
			fmt.Printf("[DEBUGGER-INIT-START] Init phase starting. Global breakpoints (%d files):\n", len(allBPs))
			for file, lines := range allBPs {
				fmt.Printf("[DEBUGGER-INIT-START]   file=%q, lines=%v\n", file, lines)
			}
			dbg.breakpointMutex.RLock()
			fmt.Printf("[DEBUGGER-INIT-START] Local breakpoints (%d files):\n", len(dbg.breakpoints))
			for file, lines := range dbg.breakpoints {
				fmt.Printf("[DEBUGGER-INIT-START]   file=%q, lines=%v\n", file, lines)
			}
			dbg.breakpointMutex.RUnlock()
		}
	}

	if inInit && !wasInInit && dbg.initFilename == "" {
		if dbg.vm != nil && dbg.vm.prg != nil && dbg.vm.prg.src != nil {
			filename := dbg.Filename()
			if filename != "" {
				dbg.initFilename = normalizeFilename(filename)
				if debugInit {
					fmt.Printf("[DEBUGGER] Captured init filename from VM: %s\n", dbg.initFilename)
				}
			}
		}
	}

	if wasInInit && !inInit {
		filename := dbg.initFilename
		if filename == "" && dbg.vm != nil && dbg.vm.prg != nil && dbg.vm.prg.src != nil {
			filename = normalizeFilename(dbg.Filename())
			if debugInit {
				fmt.Printf("[DEBUGGER] Captured init filename at completion: %s\n", filename)
			}
		}
		if filename != "" {
			if !globalInitTracker.IsInitCompleted(filename) {
				globalInitTracker.MarkInitCompleted(filename)
				if debugInit {
					fmt.Printf("[DEBUGGER] Marked init complete for: %s\n", filename)
				}
			} else {
				if debugInit {
					fmt.Printf("[DEBUGGER] Init already completed for: %s (skipping mark)\n", filename)
				}
			}
		} else {
			if debugInit {
				fmt.Printf("[DEBUGGER] WARNING: Could not mark init complete - no filename available (initFilename=%q)\n", dbg.initFilename)
			}
		}
		dbg.initFilename = ""
	}
}

func (dbg *Debugger) SetInitFilename(filename string) {
	dbg.initFilename = filename
	if debugInit {
		fmt.Printf("[DEBUGGER] Init filename explicitly set to: %s\n", filename)
	}
}

func (dbg *Debugger) IsInitPhase() bool {
	return dbg.initPhase
}

func (dbg *Debugger) logDebug(format string, args ...interface{}) {
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] "+format+"\n", args...)
	}
}

func (dbg *Debugger) WaitForConfiguration() {
	if dbg.waitingForConfig {
		<-dbg.configuredCh
	}
}

func (dbg *Debugger) PC() int {
	return dbg.vm.pc
}

func (dbg *Debugger) GetRuntime() *Runtime {
	if dbg.vm == nil {
		return nil
	}
	return dbg.vm.r
}

// SetVUID assigns a VU identifier to this debugger instance. In multi-VU debug
// mode, this ID is included in every DebuggerActivation so the DAP handler can
// map activations to DAP thread IDs. Call this once after creating the debugger.
func (dbg *Debugger) SetVUID(id uint64) {
	dbg.vuID = id
}

// GetVUID returns the VU identifier for this debugger (0 if not set).
func (dbg *Debugger) GetVUID() uint64 {
	return dbg.vuID
}

func (dbg *Debugger) IsActive() bool {
	return dbg.active
}

// IsVMExited returns true if the VM has exited (e.g. due to an uncaught exception
// or end of execution). Used by the DAP layer to distinguish uncaught exceptions
// (VM dead → terminate debug session) from caught exceptions (VM alive → continue).
func (dbg *Debugger) IsVMExited() bool {
	if dbg.vmExited {
		return true
	}
	// Also check the channel in case vmExited hasn't been set yet
	select {
	case <-dbg.vmDoneCh:
		return true
	default:
		return false
	}
}

// ReleaseException unblocks the VM goroutine that is waiting in runTryInner's
// defer after an uncaught exception. Called by the DAP layer when the user
// dismisses the exception popup (clicks Continue/Step/Stop).
func (dbg *Debugger) ReleaseException() {
	if dbg.exceptionWaitCh != nil {
		select {
		case <-dbg.exceptionWaitCh:
			// already closed
		default:
			close(dbg.exceptionWaitCh)
		}
		dbg.exceptionWaitCh = nil
	}
	// Clear the exception-active state so the debugger transitions cleanly
	dbg.exceptionBreakActive = false
	dbg.exceptionStash = nil
	dbg.exceptionPrg = nil
	dbg.active = false
}

// HasPendingException returns true if there is a pending uncaught exception
// that hasn't been released yet (exceptionWaitCh still open).
func (dbg *Debugger) HasPendingException() bool {
	return dbg.exceptionWaitCh != nil
}

// GetLastExceptionStack returns the saved call stack from the throw site.
// This is used by the DAP layer when CaptureCallStack returns empty
// (because handleThrow unwound vm.callStack before the exception was stored).
func (dbg *Debugger) GetLastExceptionStack() []StackFrame {
	return dbg.lastExceptionStack
}

// SetLastExceptionStack saves the exception's stack frames in the debugger
// so the DAP layer can use them for stackTrace requests after the VM has exited.
func (dbg *Debugger) SetLastExceptionStack(stack []StackFrame) {
	dbg.lastExceptionStack = stack
}

// AddWatch registers a watch expression. Returns its ID.
func (dbg *Debugger) AddWatch(expression string) int {
	id := int(atomic.AddInt64(&watchExprCounter, 1))
	dbg.watchExpressions = append(dbg.watchExpressions, watchExpr{id: id, expression: expression})
	return id
}

// RemoveWatch removes a watch expression by ID.
func (dbg *Debugger) RemoveWatch(id int) bool {
	for i, w := range dbg.watchExpressions {
		if w.id == id {
			dbg.watchExpressions = append(dbg.watchExpressions[:i], dbg.watchExpressions[i+1:]...)
			return true
		}
	}
	return false
}

// EvaluateWatches evaluates all registered watch expressions at the current pause point.
// Returns a map of expression -> (value, error).
// Call this from your DAP handler when paused, to populate the "Watch" panel.
func (dbg *Debugger) EvaluateWatches() map[string]WatchResult {
	results := make(map[string]WatchResult, len(dbg.watchExpressions))
	for _, w := range dbg.watchExpressions {
		val, err := dbg.Evaluate(w.expression)
		results[w.expression] = WatchResult{ID: w.id, Value: val, Err: err}
	}
	return results
}

func (dbg *Debugger) ActivationCh() chan chan DebuggerActivation {
	return dbg.activationCh
}

func (dbg *Debugger) GetCurrentBreakpointInfo() (string, int, int, bool) {
	if !dbg.active || dbg.vm == nil || dbg.vm.prg == nil || dbg.vm.prg.src == nil {
		return "", 0, 0, false
	}
	filename := dbg.Filename()
	line := dbg.Line()
	id := globalBreakpoints.GetBreakpointID(filename, line)
	if id == 0 {
		dbg.breakpointMutex.RLock()
		id = dbg.breakpointIDs[bpKey{filename, line}]
		dbg.breakpointMutex.RUnlock()
	}
	return filename, line, id, true
}

// GetCurrentFuncName returns the name of the function currently being executed.
// Returns "" for module-level code (init phase).
func (dbg *Debugger) GetCurrentFuncName() string {
	if dbg.vm == nil || dbg.vm.prg == nil {
		return ""
	}
	return string(dbg.vm.prg.funcName)
}

// ReleasePendingChannel closes pendingCh and currentCh so that activate()
// (which is blocked on <-ch) can return and the VM resumes execution.
// Called when the DAP layer detects a stale activation and needs to let
// the old VM continue before switching to a different debugger.
func (dbg *Debugger) ReleasePendingChannel() {
	if dbg.pendingCh != nil {
		safeCloseActivationCh(dbg.pendingCh)
		dbg.pendingCh = nil
	}
	if dbg.currentCh != nil {
		safeCloseActivationCh(dbg.currentCh)
		dbg.currentCh = nil
	}
}

func (dbg *Debugger) GetActivationEpoch() uint64 {
	return globalDebugCoordinator.GetGlobalEpoch()
}

func (dbg *Debugger) Detach() {
	dbg.vm.debugger = nil
	dbg.vm.debugMode = false
	dbg.vm = nil
	dbg.active = false
	if dbg.pendingCh != nil {
		if dbg.pendingCh != dbg.currentCh {
			safeCloseActivationCh(dbg.pendingCh)
		}
		dbg.pendingCh = nil
	}
	if dbg.currentCh != nil {
		safeCloseActivationCh(dbg.currentCh)
		dbg.currentCh = nil
	}
}

func (dbg *Debugger) SetBreakpoint(filename string, line int) (id int, err error) {
	if debugBP {
		fmt.Printf("[DEBUGGER-SET-BP] Setting breakpoint: filename='%s', line=%d, debugger=%p, vm=%p\n", filename, line, dbg, dbg.vm)
	}

	// Normalize at write time so all read paths use the canonical form.
	normalizedFilename := normalizeFilename(filename)

	id, globalErr := globalBreakpoints.SetBreakpoint(normalizedFilename, line)
	if globalErr != nil && globalErr.Error() == "breakpoint exists" {
		id = globalBreakpoints.GetBreakpointID(normalizedFilename, line)
	}

	dbg.breakpointMutex.Lock()
	idx := sort.SearchInts(dbg.breakpoints[normalizedFilename], line)
	if idx >= len(dbg.breakpoints[normalizedFilename]) || dbg.breakpoints[normalizedFilename][idx] != line {
		dbg.breakpoints[normalizedFilename] = append(dbg.breakpoints[normalizedFilename], line)
		if len(dbg.breakpoints[normalizedFilename]) > 1 {
			sort.Ints(dbg.breakpoints[normalizedFilename])
		}
		if id == 0 {
			id = dbg.breakPointCount
			dbg.breakPointCount++
		}
		dbg.breakpointIDs[bpKey{normalizedFilename, line}] = id
	}

	dbg.hasLocalBPs = len(dbg.breakpoints) > 0
	dbg.breakpointMutex.Unlock()

	// Keep hasGlobalBPs in sync.
	dbg.hasGlobalBPs = globalBreakpoints.Count() > 0

	// Invalidate isUserFile cache — breakpoint changes affect the result.
	dbg.cachedIsUserFilePrg = nil
	dbg.cachedIsUserFileByName = nil

	if debugBP {
		fmt.Printf("[DEBUGGER-SET-BP] ✅ Breakpoint added: id=%d, local=%d, globalCount=%d\n",
			id, len(dbg.breakpoints[normalizedFilename]), globalBreakpoints.Count())
	}
	return
}

func (dbg *Debugger) ClearBreakpoint(filename string, line int) (err error) {
	normalizedFilename := normalizeFilename(filename)

	_ = globalBreakpoints.ClearBreakpoint(normalizedFilename, line)

	dbg.breakpointMutex.Lock()
	defer dbg.breakpointMutex.Unlock()

	if len(dbg.breakpoints[normalizedFilename]) == 0 {
		return errors.New("no breakpoints")
	}

	idx := sort.SearchInts(dbg.breakpoints[normalizedFilename], line)
	if idx < len(dbg.breakpoints[normalizedFilename]) && dbg.breakpoints[normalizedFilename][idx] == line {
		dbg.breakpoints[normalizedFilename] = append(dbg.breakpoints[normalizedFilename][:idx], dbg.breakpoints[normalizedFilename][idx+1:]...)
		if len(dbg.breakpoints[normalizedFilename]) == 0 {
			delete(dbg.breakpoints, normalizedFilename)
		}
		delete(dbg.breakpointIDs, bpKey{normalizedFilename, line})
	} else {
		err = errors.New("breakpoint doesn't exist")
	}

	dbg.hasLocalBPs = len(dbg.breakpoints) > 0
	dbg.hasGlobalBPs = globalBreakpoints.Count() > 0
	// Invalidate isUserFile cache — breakpoint changes affect the result.
	dbg.cachedIsUserFilePrg = nil
	dbg.cachedIsUserFileByName = nil
	return
}

// ClearFileBreakpoints removes ALL breakpoints for a given file from both the
// local debugger instance and the global registry. It also clears any associated
// conditional breakpoints, logpoints, and hit-count breakpoints for that file.
// This is used by the DAP setBreakpoints handler which uses replacement semantics:
// the client sends the complete list of desired breakpoints and the server must
// first remove all existing breakpoints for the file before setting the new ones.
func (dbg *Debugger) ClearFileBreakpoints(filename string) {
	normalizedFilename := normalizeFilename(filename)

	if debugBP {
		fmt.Printf("[DEBUGGER-CLEAR-FILE] Clearing all breakpoints for file '%s' (normalized: '%s')\n",
			filename, normalizedFilename)
	}

	// Clear from global registry first.
	globalBreakpoints.ClearFileBreakpoints(normalizedFilename)

	// Clear from local debugger state.
	dbg.breakpointMutex.Lock()

	localLines := dbg.breakpoints[normalizedFilename]
	// Remove all local breakpoint IDs and conditional BPs for this file.
	for _, line := range localLines {
		delete(dbg.breakpointIDs, bpKey{normalizedFilename, line})
		if dbg.conditionalBPs != nil {
			delete(dbg.conditionalBPs, bpKey{normalizedFilename, line})
		}
	}
	delete(dbg.breakpoints, normalizedFilename)

	dbg.hasLocalBPs = len(dbg.breakpoints) > 0
	dbg.breakpointMutex.Unlock()

	dbg.hasGlobalBPs = globalBreakpoints.Count() > 0

	// Invalidate isUserFile cache — breakpoint changes affect the result.
	dbg.cachedIsUserFilePrg = nil
	dbg.cachedIsUserFileByName = nil

	if debugBP {
		fmt.Printf("[DEBUGGER-CLEAR-FILE] ✅ Cleared %d breakpoints for file '%s', localBPs=%v, globalCount=%d\n",
			len(localLines), normalizedFilename, dbg.hasLocalBPs, globalBreakpoints.Count())
	}
}

func (dbg *Debugger) Breakpoints() (map[string][]int, error) {
	globalBPs := globalBreakpoints.GetAllBreakpoints()

	result := make(map[string][]int)
	for k, v := range globalBPs {
		result[k] = append([]int(nil), v...)
	}
	dbg.breakpointMutex.RLock()
	for k, v := range dbg.breakpoints {
		if existing, ok := result[k]; ok {
			for _, line := range v {
				found := false
				for _, existingLine := range existing {
					if existingLine == line {
						found = true
						break
					}
				}
				if !found {
					result[k] = append(result[k], line)
				}
			}
			sort.Ints(result[k])
		} else {
			result[k] = append([]int(nil), v...)
		}
	}
	dbg.breakpointMutex.RUnlock()

	if len(result) == 0 {
		return nil, errors.New("no breakpoints")
	}
	return result, nil
}

func (dbg *Debugger) Next() error {
	if debugContinue {
		fmt.Printf("[DEBUGGER-NEXT] Called: was stepIn=%v, next=%v, lifecycleTransition=%v\n",
			dbg.stepIn, dbg.next, dbg.lifecycleTransition)
	}
	dbg.next = true
	dbg.stepIn = false
	dbg.continuing = false
	dbg.lifecycleTransition = false
	dbg.userCommandIssued = true

	// Invalidate per-pause snapshot — we're resuming.
	dbg.pausedVarSnapshot = nil

	activeDbg := globalDebugCoordinator.GetActiveDebugger()
	var steppingFilename string
	var targetDepth int
	var startLine int
	var gotValidState bool

	// Use lastBreakpoint snapshot values (set at pause time) instead of live
	// VM state (Filename()/Line()) which can be temporarily wrong if
	// withSuppressedDebugger is running a getter on another goroutine.
	if activeDbg != nil {
		steppingFilename = activeDbg.lastBreakpoint.filename
		targetDepth = activeDbg.lastBreakpoint.stackDepth
		startLine = activeDbg.lastBreakpoint.line
		gotValidState = startLine >= 0 && steppingFilename != ""
		if debugContinue {
			fmt.Printf("[DEBUGGER-NEXT] Using active debugger state: file=%s, depth=%d, line=%d, valid=%v\n",
				steppingFilename, targetDepth, startLine, gotValidState)
		}
	}

	if !gotValidState && dbg.vm != nil {
		steppingFilename = dbg.lastBreakpoint.filename
		targetDepth = dbg.lastBreakpoint.stackDepth
		startLine = dbg.lastBreakpoint.line
		gotValidState = startLine >= 0 && steppingFilename != ""
		if debugContinue {
			fmt.Printf("[DEBUGGER-NEXT] Fallback to local debugger state: file=%s, depth=%d, line=%d, valid=%v\n",
				steppingFilename, targetDepth, startLine, gotValidState)
		}
	}

	if !gotValidState {
		steppingFilename = dbg.lastBreakpoint.filename
		targetDepth = dbg.lastBreakpoint.stackDepth
		startLine = dbg.lastBreakpoint.line
		gotValidState = startLine >= 0 && steppingFilename != ""
		if debugContinue {
			fmt.Printf("[DEBUGGER-NEXT] Fallback to lastBreakpoint: file=%s, depth=%d, line=%d, valid=%v\n",
				steppingFilename, targetDepth, startLine, gotValidState)
		}
	}

	if gotValidState {
		dbg.stepOverTargetDepth = targetDepth
		dbg.stepOverOriginalTargetDepth = targetDepth // preserve authoritative value
		dbg.stepOverStartLine = startLine
		dbg.stepOverMissCount = 0
		dbg.steppingFilename = steppingFilename
		// Compute the last PC whose source-mapped line == startLine.
		// Step-over won't break until currentPC > this value, which skips
		// sub-expressions in multi-line call expressions (e.g., object literal
		// properties that map to different source lines but are part of the
		// same expression — the call instruction at the end maps back to startLine).
		if dbg.vm != nil && dbg.vm.prg != nil && !dbg.vmResuming.Load() {
			dbg.stepOverLastPC = dbg.vm.prg.lastPCForLine(startLine, dbg.lastBreakpoint.pc, steppingFilename)
			dbg.stepOverLastPCPrg = dbg.vm.prg
			// LOOP GUARD: If the computed range [breakpointPC .. stepOverLastPC]
			// contains a backward jump instruction, it spans a loop body
			// (for/while/do-while). The sub-expression skip must be disabled
			// so that step-over stops at the first line inside the loop body,
			// matching Node.js/V8 debugger behaviour.
			// Also: when stepOverLastPC <= breakpointPC, there are NO sub-expressions
			// ahead to skip (e.g., loop update/back-edge on 2nd+ iteration).
			if dbg.stepOverLastPC > dbg.lastBreakpoint.pc {
				if dbg.vm.prg.hasBackwardJumpBetween(dbg.lastBreakpoint.pc, dbg.stepOverLastPC) {
					if debugContinue {
						fmt.Printf("[NEXT] Loop detected in PC range [%d..%d] for line %d — disabling sub-expression skip\n",
							dbg.lastBreakpoint.pc, dbg.stepOverLastPC, startLine)
					}
					dbg.stepOverLastPC = -1
					dbg.stepOverLastPCPrg = nil
				}
			} else {
				// stepOverLastPC <= breakpointPC: no sub-expressions ahead.
				// Disable skip so step-over re-enters loop body on next iteration.
				dbg.stepOverLastPC = -1
				dbg.stepOverLastPCPrg = nil
			}
		} else {
			dbg.stepOverLastPC = -1
			dbg.stepOverLastPCPrg = nil
		}
	} else {
		dbg.stepOverTargetDepth = dbg.lastBreakpoint.stackDepth
		dbg.stepOverOriginalTargetDepth = dbg.stepOverTargetDepth
		dbg.stepOverStartLine = 0
		dbg.stepOverLastPC = -1
		dbg.stepOverLastPCPrg = nil
		dbg.stepOverMissCount = 0
		dbg.steppingFilename = ""
		if debugContinue {
			fmt.Printf("[DEBUGGER-NEXT] ⚠️ No valid state, using safe defaults: targetDepth=%d, startLine=0\n",
				dbg.stepOverTargetDepth)
		}
	}

	if gotValidState {
		// Don't overwrite lastBreakpoint.pc — keep the snapshot value set at pause time.
		// vm.pc may be temporarily wrong if withSuppressedDebugger is running concurrently.
		dbg.lastBreakpoint.line = startLine
		dbg.lastBreakpoint.filename = steppingFilename
		dbg.lastBreakpoint.stackDepth = targetDepth
	}

	// In multi-VU debug mode, step operations are local to this VU only — do NOT
	// propagate to the global coordinator. This prevents VU1's Next() from causing
	// VU2 to inherit step state and pause unexpectedly.
	// Instead, use per-VU step state so the correct VU receives the step command.
	if !globalDebugCoordinator.IsMultiVUDebug() {
		globalDebugCoordinator.SetGlobalStepState(true, false, steppingFilename, targetDepth)
	} else {
		globalDebugCoordinator.SetVUStepState(dbg.vuID, true, false, steppingFilename, targetDepth)
	}
	if debugContinue {
		fmt.Printf("[DEBUGGER-NEXT] After SetGlobalStepState: next=%v, stepIn=%v, steppingFilename=%s, targetDepth=%d, multiVU=%v, vuID=%d\n",
			dbg.next, dbg.stepIn, steppingFilename, targetDepth, globalDebugCoordinator.IsMultiVUDebug(), dbg.vuID)
	}


	if dbg.pendingCh != nil {
		if dbg.pendingCh == dbg.currentCh {
			safeCloseActivationCh(dbg.pendingCh)
			dbg.pendingCh = nil
			dbg.currentCh = nil
		} else {
			safeCloseActivationCh(dbg.pendingCh)
			dbg.pendingCh = nil
		}
	}
	return nil
}

func (dbg *Debugger) ClearStepFlags() {
	if debugContinue {
		fmt.Printf("[DEBUGGER-CLEAR] ClearStepFlags called: was stepIn=%v, next=%v, continuing=%v\n",
			dbg.stepIn, dbg.next, dbg.continuing)
	}
	dbg.lastBreakpoint.pc = dbg.vm.pc
	dbg.lastBreakpoint.line = dbg.Line()
	dbg.lastBreakpoint.filename = dbg.Filename()
	dbg.next = false
	dbg.stepIn = false
	dbg.stepOverStartLine = 0
	dbg.stepOverOriginalTargetDepth = 0
	dbg.stepInLastPC = -1
	dbg.stepInStartLine = 0
	dbg.continuing = false
	dbg.userCommandIssued = true
	// Invalidate per-pause snapshot — we're resuming.
	dbg.pausedVarSnapshot = nil
	globalDebugCoordinator.ClearGlobalStepState()
}

// ClearLastBreakpoint resets the lastBreakpoint position tracking so that
// same-line-skip logic doesn't prevent breakpoints from firing after a phase
// transition. This is needed when the init phase stopped at a line that also
// has a breakpoint in setup/default/teardown — without clearing, the debugger
// thinks it's still on the same line and skips the breakpoint.
func (dbg *Debugger) ClearLastBreakpoint() {
	dbg.lastBreakpoint.filename = ""
	dbg.lastBreakpoint.line = 0
	dbg.lastBreakpoint.pc = -1
	dbg.lastBreakpoint.stackDepth = 0
}

// ResetForPhaseTransition clears stale step/pause state from a cached Debugger
// when reusing it for a new lifecycle phase (setup → default → teardown →
// handleSummary) within the SAME k6 run.  Unlike ResetForNewRun it preserves
// init-tracking state (initComplete, initFilename, initPhase) so that
// init-breakpoint deduplication keeps working, and it preserves breakpoints,
// connection status, and channels.
func (dbg *Debugger) ResetForPhaseTransition() {
	if debugActivate {
		fmt.Printf("[DEBUGGER] ResetForPhaseTransition: clearing stale step state (stepIn=%v, next=%v, continuing=%v, lifecycleTransition=%v, userCommandIssued=%v)\n",
			dbg.stepIn, dbg.next, dbg.continuing, dbg.lifecycleTransition, dbg.userCommandIssued)
	}

	// Step / pause state — must be zeroed so the new phase starts clean
	dbg.next = false
	dbg.stepIn = false
	dbg.continuing = false
	dbg.lifecycleTransition = false
	dbg.userCommandIssued = false
	dbg.skipPhaseEntryBreak = false
	dbg.stepOverTargetDepth = 0
	dbg.stepOverOriginalTargetDepth = 0
	dbg.stepOverStartLine = 0
	dbg.steppingFilename = ""
	dbg.stepInLastPC = -1
	dbg.stepInStartLine = 0

	// Position tracking — reset so the first line of the new function is seen as "new"
	// pc must be -1 (not 0) so that pcAdvanced is true at PC=0 (first instruction)
	dbg.lastBreakpoint.filename = ""
	dbg.lastBreakpoint.line = 0
	dbg.lastBreakpoint.pc = -1
	dbg.lastBreakpoint.stackDepth = 0
	dbg.lastDebugLine = -1
	dbg.lastDebugDepth = -1
	dbg.lastLine = 0
	dbg.currentLine = 0

	// Conditional breakpoints — stale from previous phase
	dbg.conditionalBPs = nil

	// Variable / scope caches — stale from previous phase
	// PERF: set to nil instead of make() — nil map reads return zero value safely in Go.
	// Write paths lazy-init them when needed, avoiding 5 map allocations per phase transition.
	dbg.pausedVarSnapshot = nil
	dbg.pausedVarSnapshotLine = 0
	dbg.pausedVarSnapshotPC = -1
	dbg.sourceVarCache = nil
	dbg.globalVarCache = nil
	dbg.sourceCacheValid = false
	dbg.varDeclLines = nil
	dbg.varValueCache = nil
	dbg.varValueCacheLine = -1
	dbg.cachedGlobalNames = nil
	dbg.globalsCaptured = false

	// Call stack / return value caches
	dbg.functionCallStack = nil
	dbg.pendingReturnValues = nil
	dbg.returnValueCache = nil
	dbg.currentScopeDepth = 0
	dbg.scopeVariables = nil

	// Filename / line cache (will be rebuilt on first breakpoint() call)
	dbg.cachedPrg = nil
	dbg.cachedFilename = ""
	dbg.cachedNormFile = ""
	dbg.cachedLinePrg = nil
	dbg.cachedPC = -1
	dbg.cachedLine = 0
	dbg.cachedSourceLines = nil
	dbg.cachedSourceLinesPrg = nil
	dbg.cachedIsUserFilePrg = nil
	dbg.cachedIsUserFileByName = nil
	dbg.cachedBaseFilePrg = nil

	// VM exit state — reset for the new phase
	dbg.vmExited = false
	dbg.vmDoneCh = make(chan struct{})

	// Exception state — clear stale exception data from previous phase.
	// Without this, a caught exception in setup could leak exceptionBreakActive=true
	// into the default phase, causing incorrect behaviour.
	dbg.lastException = nil
	dbg.exceptionBreakActive = false
	dbg.exceptionStash = nil
	dbg.exceptionPrg = nil
	dbg.uncaughtExceptionExit = false
	dbg.pendingUncaughtException = nil
	// Release any blocked exception wait before clearing
	if dbg.exceptionWaitCh != nil {
		select {
		case <-dbg.exceptionWaitCh:
		default:
			close(dbg.exceptionWaitCh)
		}
		dbg.exceptionWaitCh = nil
	}

	// Drain stale entries from the activation channel
	select {
	case <-dbg.activationCh:
	default:
	}
	// CRITICAL: Also drain the coordinator's activation channel.
	// If a stale currentCh was sent to the coordinator before the phase
	// transition, it won't be drained by the local drain above. This prevents
	// 0ms phantom handshakes on the first breakpoint of the new phase.
	globalDebugCoordinator.DrainActivationChannel()
	// In multi-VU mode, also drain the per-VU activation channel.
	if globalDebugCoordinator.IsMultiVUDebug() {
		globalDebugCoordinator.DrainVUActivationChannel(dbg.vuID)
		globalDebugCoordinator.ClearVUStepState(dbg.vuID)
	}
	// RACE FIX: Close pendingCh and currentCh BEFORE nil-ing them.
	// If Continue() is in-flight on another goroutine, it may have sent
	// currentCh into an activation channel. When activate() receives it
	// and tries to send, the channel must be closed (unblocking activate())
	// rather than orphaned (causing activate() to block forever on a channel
	// nobody reads from). safeCloseActivationCh handles double-close safely.
	if dbg.pendingCh != nil {
		if dbg.pendingCh != dbg.currentCh {
			safeCloseActivationCh(dbg.pendingCh)
		}
	}
	if dbg.currentCh != nil {
		safeCloseActivationCh(dbg.currentCh)
	}
	dbg.pendingCh = nil
	dbg.currentCh = nil

	// NOTE: we intentionally do NOT touch:
	//   - initPhase / initFilename / initComplete  (init dedup must survive)
	//   - breakpoints / breakpointIDs / hasLocalBPs / hasGlobalBPs
	//   - hasConnection
	//   - initRuntime / setupData (may still be needed)
}

// PrepareForCallback resets only position-tracking state so that breakpoints
// can fire in a new callback without disrupting the Continue() <-> activate()
// channel handshake.  Unlike ResetForPhaseTransition this does NOT:
//   - drain activation channels (avoids 200ms Continue() retry per step)
//   - recreate vmDoneCh (the VM is still alive inside the same phase)
//   - clear step/pause flags (caller decides whether to set stepIn)
//
// Use this for sub-step transitions within the SAME lifecycle phase — for
// example, gherkin step/hook callbacks within the default() function.
// Use ResetForPhaseTransition for real lifecycle transitions (setup → default
// → teardown → handleSummary).
func (dbg *Debugger) PrepareForCallback() {
	if debugActivate {
		fmt.Printf("[DEBUGGER] PrepareForCallback: resetting position tracking (stepIn=%v, next=%v)\n",
			dbg.stepIn, dbg.next)
	}

	// Position tracking — reset so the first line of the callback is seen as "new"
	dbg.lastBreakpoint.filename = ""
	dbg.lastBreakpoint.line = 0
	dbg.lastBreakpoint.pc = -1
	dbg.lastBreakpoint.stackDepth = 0
	dbg.lastDebugLine = -1
	dbg.lastDebugDepth = -1
	dbg.lastLine = 0
	dbg.currentLine = 0

	// Variable / scope caches — stale from previous callback
	dbg.pausedVarSnapshot = nil
	dbg.pausedVarSnapshotLine = 0
	dbg.pausedVarSnapshotPC = -1
	dbg.sourceVarCache = nil
	dbg.globalVarCache = nil
	dbg.sourceCacheValid = false
	dbg.varDeclLines = nil
	dbg.varValueCache = nil
	dbg.varValueCacheLine = -1
	dbg.cachedGlobalNames = nil
	dbg.globalsCaptured = false

	// Call stack / return value caches
	dbg.functionCallStack = nil
	dbg.pendingReturnValues = nil
	dbg.returnValueCache = nil
	dbg.currentScopeDepth = 0
	dbg.scopeVariables = nil

	// Filename / line cache (will be rebuilt on next breakpoint() call)
	dbg.cachedPrg = nil
	dbg.cachedFilename = ""
	dbg.cachedNormFile = ""
	dbg.cachedLinePrg = nil
	dbg.cachedPC = -1
	dbg.cachedLine = 0
	dbg.cachedSourceLines = nil
	dbg.cachedSourceLinesPrg = nil
	dbg.cachedIsUserFilePrg = nil
	dbg.cachedIsUserFileByName = nil
	dbg.cachedBaseFilePrg = nil

	// Conditional breakpoints — stale from previous callback
	dbg.conditionalBPs = nil

	// CRITICAL: Disable init-BP dedup inside gherkin callbacks.
	// During init, the VM evaluates `Given(pattern, function() { ... })` —
	// the function literal at (say) line 55 is "hit" and recorded in the
	// init-BP set. Later, when gherkin.run() actually CALLS that callback,
	// the breakpoint at line 55 would be suppressed because the init-BP
	// dedup thinks it already fired. Setting initBPSnapshotDone=true with
	// a nil snapshot makes wasHitDuringInit() return false for ALL lines,
	// so breakpoints fire normally inside the callback.
	// This is safe because:
	//   - PrepareForCallback is only called by gherkin (sub-step transitions)
	//   - Between callbacks, suppressDebugger=true prevents any breakpoint checks
	//   - Non-gherkin code uses ResetForPhaseTransition which does NOT clear this
	dbg.initBPSnapshot = nil
	dbg.initBPSnapshotDone = true
}

// ResetForNewRun clears all per-run step/phase state from a cached Debugger so it
// can be reused cleanly for a new k6 run without carrying over stale flags.
// It preserves the VM pointer, breakpoints, connection status, and channels.
func (dbg *Debugger) ResetForNewRun() {
	// CRITICAL: Reset the global init tracker so that stale init breakpoint data
	// from a previous k6 run doesn't suppress breakpoints in the new run.
	// Without this, breakpoints that fired during init in the first run are
	// incorrectly skipped in subsequent runs because globalInitTracker retains
	// its data across runs (it's a package-level global).
	globalInitTracker.Reset()

	// Step / pause state
	dbg.next = false
	dbg.stepIn = false
	dbg.continuing = false
	dbg.lifecycleTransition = false
	dbg.userCommandIssued = false
	dbg.skipPhaseEntryBreak = false
	dbg.stepOverTargetDepth = 0
	dbg.stepOverOriginalTargetDepth = 0
	dbg.stepOverStartLine = 0
	dbg.steppingFilename = ""
	dbg.stepInLastPC = -1
	dbg.stepInStartLine = 0

	// CRITICAL: Reset suppression state. If a previous session crashed during
	// ExecuteModule (onFulfilled panic) or a Go→JS callback, suppressDebugger
	// could be stuck true. Without clearing it here, the new session would
	// silently skip ALL breakpoints.
	dbg.suppressDebugger = false
	dbg.suppressDebugDepth = 0

	// Breakpoint position cache
	// FIX: pc must be -1 (not 0) so that pcAdvanced (currentPC != prevPC) is true
	// at PC=0 (function entry). Without this, the first instruction is skipped
	// during step-in after a new run starts.
	dbg.lastBreakpoint.filename = ""
	dbg.lastBreakpoint.line = 0
	dbg.lastBreakpoint.pc = -1
	dbg.lastBreakpoint.stackDepth = 0
	dbg.lastDebugLine = -1
	dbg.lastDebugDepth = -1
	dbg.lastLine = 0
	dbg.currentLine = 0

	// Init phase flags
	dbg.initPhase = false
	dbg.initFilename = ""
	dbg.initComplete = false
	dbg.initBPSnapshot = nil
	dbg.initBPSnapshotDone = false

	// Conditional breakpoints
	dbg.conditionalBPs = nil

	// Variable / scope caches
	// PERF: set to nil instead of make() — nil map reads return zero value safely in Go.
	// Write paths lazy-init them when needed, avoiding allocations on reset.
	dbg.pausedVarSnapshot = nil
	dbg.pausedVarSnapshotLine = 0
	dbg.pausedVarSnapshotPC = -1
	dbg.sourceVarCache = nil
	dbg.globalVarCache = nil
	dbg.sourceCacheValid = false
	dbg.varDeclLines = nil
	dbg.varValueCache = nil
	dbg.varValueCacheLine = -1
	dbg.cachedGlobalNames = nil
	dbg.globalsCaptured = false

	// Call stack / return value caches
	dbg.functionCallStack = nil
	dbg.pendingReturnValues = nil
	dbg.returnValueCache = nil
	dbg.currentScopeDepth = 0
	dbg.scopeVariables = nil

	// Filename / line cache (will be rebuilt on first breakpoint() call)
	dbg.cachedPrg = nil
	dbg.cachedFilename = ""
	dbg.cachedNormFile = ""
	dbg.cachedLinePrg = nil
	dbg.cachedPC = -1
	dbg.cachedLine = 0
	dbg.cachedSourceLines = nil
	dbg.cachedSourceLinesPrg = nil
	dbg.cachedIsUserFilePrg = nil
	dbg.cachedIsUserFileByName = nil
	dbg.cachedBaseFilePrg = nil

	// VM exit state — new run means a new VM lifecycle
	dbg.vmExited = false
	// Don't replace vmDoneCh if it's already fresh; replace it so old
	// goroutines waiting on it don't accidentally unblock.
	dbg.vmDoneCh = make(chan struct{})

	// Runtime / setup data from previous run
	dbg.initRuntime = nil
	dbg.setupData = nil

	// Drain stale entries from the activation channel
	select {
	case <-dbg.activationCh:
	default:
	}
	// pendingCh / currentCh — clear without closing (they may already be closed)
	dbg.pendingCh = nil
	dbg.currentCh = nil
}

func (dbg *Debugger) ClearLocalStepState() {
	if debugActivate {
		fmt.Printf("[DEBUGGER-CLEAR] ClearLocalStepState called: was stepIn=%v, next=%v, stepOverStartLine=%d, stepOverTargetDepth=%d\n",
			dbg.stepIn, dbg.next, dbg.stepOverStartLine, dbg.stepOverTargetDepth)
	}
	dbg.next = false
	dbg.stepIn = false
	dbg.stepOverStartLine = 0
	dbg.stepOverTargetDepth = 0
	dbg.stepOverOriginalTargetDepth = 0
	dbg.steppingFilename = ""
	dbg.lifecycleTransition = false
	dbg.pausedVarSnapshot = nil
	globalDebugCoordinator.ClearGlobalStepState()
	if globalDebugCoordinator.IsMultiVUDebug() {
		globalDebugCoordinator.ClearVUStepState(dbg.vuID)
	}
}



func (dbg *Debugger) Exec(expr string) (Value, error) {
	if expr == "" {
		return nil, errors.New("nothing to execute")
	}
	return dbg.Evaluate(expr)
}

func (dbg *Debugger) Print(varName string) (string, error) {
	if varName == "" {
		return "", errors.New("please specify variable name")
	}
	val, err := dbg.getValue(varName)

	if val == Undefined() {
		return fmt.Sprint(dbg.vm.stash.values), err
	}
	return fmt.Sprint(val), err
}

func stringToLines(s string) (lines []string, err error) {
	scanner := bufio.NewScanner(strings.NewReader(s))
	for scanner.Scan() {
		lines = append(lines, scanner.Text())
	}
	err = scanner.Err()
	return
}

// breakpoint is called by the VM on every instruction in debug mode.
// PERF critical path — minimize allocations and lock acquisitions.
func (dbg *Debugger) breakpoint() bool {
	// PERF: Lazily sync hasGlobalBPs from the global registry.
	// Breakpoints are set on VU0's debugger during DAP init, but default() runs
	// on VU1 with a fresh debugger that never had SetBreakpoint() called.
	// Without this sync, VU1's breakpoint() returns false immediately.
	if !dbg.hasGlobalBPs {
		dbg.hasGlobalBPs = globalBreakpoints.Count() > 0
	}
	if dbg.vm.prg == nil || (!dbg.hasLocalBPs && !dbg.hasGlobalBPs) {
		if dbg.breakpointCheckCount <= 5 {
			if debugBreakpoint {
				fmt.Printf("[BP-TRACE] EARLY EXIT: prg=%v, hasLocal=%v, hasGlobal=%v\n", dbg.vm.prg != nil, dbg.hasLocalBPs, dbg.hasGlobalBPs)
			}
		}
		return false
	}

	// PERF: skip all debugger work during getter evaluation (resolveIndirectValue/safeCallGetter).
	// Without this, variable inspection can trigger breakpoints and corrupt step state.
	if dbg.suppressDebugger {
		return false
	}

	// PERF: Never break inside external jslib bundles loaded from https://
	// These are instrumentation libraries (tempo, httpx, etc.) that must
	// execute transparently, exactly as Node.js skips node_modules.
	// This eliminates ALL breakpoint overhead for tempo code — no line lookup,
	// no breakpoint map scan, no source-map resolution.
	if strings.HasPrefix(dbg.cachedNormFile, "https://") ||
		strings.HasPrefix(dbg.cachedNormFile, "http://") {
		return false
	}

	// PERF: Use cached filename from vm.debug() — refreshFilenameCache() was already
	// called there before breakpoint(), so we skip the redundant call here.
	normalizedFilename := dbg.cachedNormFile
	line := dbg.Line()

	// DIAGNOSTIC: Log EVERY call to breakpoint() for the specific file that has breakpoints.
	// Only log distinct lines to avoid flooding on repeated line=2 import bytecodes.
	if (debugBreakpoint || debugAll) && strings.HasSuffix(normalizedFilename, "LoadTests.ts") {
		if dbg.bpCallLogLastLine != line {
			dbg.bpCallLogLastLine = line
			if dbg.bpCallLogCount < 50 {
				dbg.bpCallLogCount++
				fmt.Printf("[BP-ENTRY] breakpoint() called: file=%q, line=%d, initPhase=%v, initComplete=%v, vuID=%d, hasLocal=%v, hasGlobal=%v, suppress=%v, active=%v\n",
					normalizedFilename, line, dbg.initPhase, dbg.initComplete, dbg.vuID, dbg.hasLocalBPs, dbg.hasGlobalBPs, dbg.suppressDebugger, dbg.active)
			}
		}
	}

	// DIAGNOSTIC: Always log when breakpoint() is called for a file+line that has a registered BP.
	// This is NOT gated by bpTraceLimit — it only fires for actual breakpoint lines.
	if (debugBreakpoint || debugAll) && dbg.hasGlobalBPs {
		srcMap := dbg.cachedSrcMapFile
		checkFile := normalizedFilename
		if srcMap != "" {
			checkFile = srcMap
		}
		if globalBreakpoints.HasBreakpoint(checkFile, line) || globalBreakpoints.HasBreakpoint(normalizedFilename, line) {
			fmt.Printf("[BP-CHECK-HIT] breakpoint() checking REGISTERED BP line: file=%q, srcMap=%q, line=%d, initPhase=%v, initComplete=%v, suppress=%v, vuID=%d, active=%v\n",
				normalizedFilename, srcMap, line, dbg.initPhase, dbg.initComplete, dbg.suppressDebugger, dbg.vuID, dbg.active)
		}
	}

	// TEMP DEBUG: Log breakpoint checks on LINE TRANSITIONS to diagnose filename matching.
	// Instead of logging every check (which floods with repeated line=2 during init),
	// only log when the line number changes. This ensures we see all unique lines checked
	// without exhausting the trace limit on repeated import-resolution bytecodes.
	bpTraceLimit := 200
	lineChanged := dbg.lastBPTraceLine != line || dbg.lastBPTraceFile != normalizedFilename
	if lineChanged && dbg.breakpointCheckCount < bpTraceLimit {
		dbg.breakpointCheckCount++
		dbg.lastBPTraceLine = line
		dbg.lastBPTraceFile = normalizedFilename
		srcMapFile := dbg.cachedSrcMapFile
		if debugBreakpoint {
			fmt.Printf("[BP-TRACE] vuID=%d, normFile=%q, srcMapFile=%q, line=%d, hasLocal=%v, hasGlobal=%v, globalCount=%d, initPhase=%v\n",
			dbg.vuID, normalizedFilename, srcMapFile, line, dbg.hasLocalBPs, dbg.hasGlobalBPs, globalBreakpoints.Count(), dbg.initPhase)
		}
	}

	// Capture init filename lazily (same as before, but uses cached normalized form).
	if dbg.initPhase && dbg.initFilename == "" && normalizedFilename != "" {
		dbg.initFilename = normalizedFilename
		if debugInit {
			fmt.Printf("[BREAKPOINT-CHECK] Captured init filename during breakpoint check: %s\n", normalizedFilename)
		}
	}

	// PERF: initComplete is a local monotonic copy — once true we never ask the
	// global tracker again (eliminating 1-3 RLocks per instruction).
	if !dbg.initComplete {
		dbg.initComplete = globalInitTracker.HasAnyInitCompleted()
	}
	if dbg.initComplete {
		// Apply init-BP dedup: skip breakpoints that already fired during init.
		// Uses composite {file, line} keys so breakpoints in different files at the
		// same line number are NOT suppressed. The inFunctionBody guard was removed
		// because module-level init code runs inside a Go callback wrapper (bundle.go
		// call(nil)) that pushes a call frame — callStackDepth >= 1 even at module level.
		dbg.ensureInitBPSnapshot()
		// FIX: Use source-mapped filename for the dedup check, not the bundle filename.
		// This matches the recording side (RecordInitBreakpoint) which also uses srcMapFile.
		initCheckFile := normalizedFilename
		if dbg.cachedSrcMapFile != "" {
			initCheckFile = dbg.cachedSrcMapFile
		}
		if dbg.wasHitDuringInit(initCheckFile, line) {
			if debugBreakpoint || debugAll {
				fmt.Printf("[BP-DEDUP] ⛔ Init dedup suppressed: file=%q, initCheckFile=%q, line=%d, vuID=%d\n",
					normalizedFilename, initCheckFile, line, dbg.vuID)
			}
			return false
		}
	}

	//  also reset when the call stack depth increased (new function entry)
	// This detects re-entry into the same arrow function from a loop.
	currentDepth := len(dbg.vm.callStack)
	isNewLine := dbg.lastDebugLine != line || currentDepth != dbg.lastDebugDepth
	if isNewLine {
		dbg.lastDebugLine = line
		dbg.lastDebugDepth = currentDepth
	}

	// PERF: check local breakpoints first (no lock needed for empty map fast path,
	// but we still hold RLock for the actual lookup).
	found := false

	// FIX: In bundled TypeScript (esbuild), all code is in a single vm.prg with
	// src.Name() pointing to the main bundle file (e.g., LoadTests.ts). But
	// breakpoints are registered under the ORIGINAL source filenames (e.g., CcsApi.ts).
	// The source map maps each PC to its original file+line. We must check BOTH
	// the program filename AND the source-mapped filename against the breakpoint registry.
	srcMapFile := dbg.cachedSrcMapFile // populated by Line() above

	if dbg.hasLocalBPs {
		dbg.breakpointMutex.RLock()
		lines := dbg.breakpoints[normalizedFilename]
		idx := sort.SearchInts(lines, line)
		found = idx < len(lines) && lines[idx] == line
		// Also check source-mapped filename if different from program filename
		if !found && srcMapFile != "" && srcMapFile != normalizedFilename {
			lines = dbg.breakpoints[srcMapFile]
			idx = sort.SearchInts(lines, line)
			found = idx < len(lines) && lines[idx] == line
		}
		dbg.breakpointMutex.RUnlock()
	}

	// PERF: check global registry only if not found locally.
	if !found && dbg.hasGlobalBPs {
		found = globalBreakpoints.HasBreakpoint(normalizedFilename, line)
		if !found && srcMapFile != "" && srcMapFile != normalizedFilename {
			found = globalBreakpoints.HasBreakpoint(srcMapFile, line)
		}
	}


	// DIAGNOSTIC: Always log when a breakpoint is found (or when we're at a line with a
	// global breakpoint but didn't find it via the normal lookup — filename mismatch diagnosis).
	if found && dbg.initPhase {
		// Use source-mapped filename for init-BP recording when available.
		// In bundled TypeScript, normalizedFilename is the bundle file — using it
		// causes cross-file collisions (e.g., CcsApi.ts line 15 suppresses
		// Stores.ts line 15 because both share the same bundle filename).
		initRecordFile := normalizedFilename
		if srcMapFile != "" {
			initRecordFile = srcMapFile
		}
		globalInitTracker.RecordInitBreakpoint(initRecordFile, line)
		if debugBreakpoint || debugAll {
			fmt.Printf("[BP-INIT-HIT] ✅ Init breakpoint found: file=%q, srcMapFile=%q, initRecordFile=%q, line=%d, vuID=%d, active=%v, hasConnection=%v\n",
				normalizedFilename, srcMapFile, initRecordFile, line, dbg.vuID, dbg.active, dbg.HasConnection())
		}
	}
	if !found && dbg.initPhase && dbg.hasGlobalBPs && (debugBreakpoint || debugAll) {
		// Check if ANY global breakpoint exists at this line (regardless of filename)
		// to diagnose filename mismatches
		gbr := globalBreakpoints.GetAllBreakpoints()
		for bpFile, bpLines := range gbr {
			for _, bpLine := range bpLines {
				if bpLine == line {
					fmt.Printf("[BP-INIT-MISS] ⚠️ Global BP exists at line %d in file=%q, but not found for normFile=%q, srcMapFile=%q (vuID=%d, initPhase=%v)\n",
						line, bpFile, normalizedFilename, srcMapFile, dbg.vuID, dbg.initPhase)
				}
			}
		}
	}

	if found && (debugBreakpoint || dbg.enableDebugLogging) && isNewLine {
		willStop := true
		skipReason := ""
		if dbg.next {
			startLine := dbg.stepOverStartLine
			// PERF: reuse currentDepth from line ~2551 — already computed above
			targetDepth := dbg.stepOverTargetDepth
			if startLine == line {
				willStop = false
				skipReason = fmt.Sprintf("step-over still on start line %d", startLine)
			} else if currentDepth > targetDepth {
				willStop = false
				skipReason = fmt.Sprintf("step-over at deeper depth %d > target %d", currentDepth, targetDepth)
			}
		} else if dbg.stepIn {
			skipReason = "step-in active (will break at new line)"
		}
		if willStop {
			if debugBreakpoint {
				fmt.Printf("[BREAKPOINT-CHECK] ✅✅ BREAKPOINT HIT at line %d in '%s' (initPhase=%v) - will activate debugger\n", line, dbg.cachedFilename, dbg.initPhase)
			}
		} else {
			if debugBreakpoint {
				fmt.Printf("[BREAKPOINT-CHECK] ⚠️ BREAKPOINT at line %d in '%s' - WILL BE SKIPPED (%s)\n", line, dbg.cachedFilename, skipReason)
			}
		}
	}

	if found {
		dbg.logBreakpointFound(line, normalizedFilename, srcMapFile)
	}

	return found
}

// DIAGNOSTIC: logBreakpointFound is called whenever breakpoint() returns true.
// This is always-on (not gated by debugBreakpoint) to trace breakpoint activation
// issues across k6 stages (init, setup, default, teardown).
func (dbg *Debugger) logBreakpointFound(line int, normalizedFilename, srcMapFile string) {
	if !(debugBreakpoint || debugAll) {
		return
	}
	phase := "default"
	if dbg.initPhase {
		phase = "init"
	} else if dbg.initComplete {
		phase = "post-init"
	}
	fmt.Printf("[BP-FOUND] ✅ breakpoint() found match: file=%q, srcMap=%q, line=%d, phase=%s, vuID=%d, active=%v, next=%v, stepIn=%v, suppress=%v, depth=%d\n",
		normalizedFilename, srcMapFile, line, phase, dbg.vuID, dbg.active, dbg.next, dbg.stepIn, dbg.suppressDebugger, dbg.callStackDepth())
}

func (dbg *Debugger) getLastLine() int {
	if dbg.lastLine >= 0 {
		return dbg.lastLine
	}
	return dbg.Line()
}

func (dbg *Debugger) getSourceLine(lineNum int) string {
	if dbg.vm.prg == nil || dbg.vm.prg.src == nil {
		return ""
	}
	if dbg.cachedSourceLinesPrg != dbg.vm.prg {
		dbg.cachedSourceLines = strings.Split(dbg.vm.prg.src.Source(), "\n")
		dbg.cachedSourceLinesPrg = dbg.vm.prg
	}
	lines := dbg.cachedSourceLines
	if lineNum < 1 || lineNum > len(lines) {
		return ""
	}
	line := strings.TrimSpace(lines[lineNum-1])
	if len(line) > 60 {
		line = line[:60] + "..."
	}
	return line
}

func (dbg *Debugger) updateLastLine(lineNumber int) {
	if dbg.lastLine != lineNumber {
		dbg.lastLine = lineNumber
	}
}

func (dbg *Debugger) callStackDepth() int {
	return len(dbg.vm.callStack)
}

func (dbg *Debugger) Line() int {
	if dbg.vm.prg == nil || dbg.vm.prg.src == nil {
		return -1
	}
	// PERF: cache line number per-PC — src.Position(sourceOffset(pc)) is expensive
	// and Line() is called multiple times per instruction in the hot path.
	// Gate on BOTH vm.pc AND vm.prg (via cachedLinePrg) — different programs can
	// reuse the same PC value (e.g. pc=0 at every function entry), which would
	// serve stale data.
	if dbg.vm.pc == dbg.cachedPC && dbg.vm.prg == dbg.cachedLinePrg && dbg.cachedLine != 0 {
		return dbg.cachedLine
	}
	dbg.cachedPC = dbg.vm.pc
	dbg.cachedLinePrg = dbg.vm.prg
	pos := dbg.vm.prg.src.Position(dbg.vm.prg.sourceOffset(dbg.vm.pc))
	dbg.cachedLine = pos.Line
	// Cache the source-mapped filename from the Position. When there's a source map,
	// this will be the ORIGINAL filename (e.g., CcsApi.ts), not the bundled file.
	// breakpoint() needs this to find breakpoints in imported/bundled files.
	dbg.cachedSrcMapFile = normalizeFilename(pos.Filename)
	return dbg.cachedLine
}

func (dbg *Debugger) Filename() string {
	dbg.refreshFilenameCache()
	// When a source map is active and the Line() cache is valid for the current PC,
	// cachedSrcMapFile contains the ORIGINAL filename (e.g., CcsApi.ts). Prefer it
	// over cachedFilename (the bundle filename) so the IDE navigates to the correct
	// source file on breakpoint/step activation.
	if dbg.cachedSrcMapFile != "" &&
		dbg.vm.pc == dbg.cachedPC && dbg.vm.prg == dbg.cachedLinePrg {
		return dbg.cachedSrcMapFile
	}
	return dbg.cachedFilename
}

// Column returns the 1-based column number for the current PC.
// NOT cached — only called from activate() which is off the hot path.
func (dbg *Debugger) Column() int {
	if dbg.vm.prg == nil || dbg.vm.prg.src == nil {
		return 0
	}
	return dbg.vm.prg.src.Position(dbg.vm.prg.sourceOffset(dbg.vm.pc)).Column
}

func (dbg *Debugger) updateCurrentLine() {
	if dbg.vm.prg == nil || dbg.vm.prg.src == nil {
		return
	}
	dbg.currentLine = dbg.Line()
}

func (dbg *Debugger) getNextLine() int {
	if dbg.vm.prg == nil || dbg.vm.prg.src == nil || dbg.vm.pc >= len(dbg.vm.prg.code) {
		return 0
	}
	for idx := range dbg.vm.prg.code[dbg.vm.pc:] {
		nextLine := dbg.vm.prg.src.Position(dbg.vm.prg.sourceOffset(dbg.vm.pc + idx + 1)).Line
		if nextLine > dbg.Line() {
			return nextLine
		}
	}
	return 0
}

func (dbg *Debugger) safeToRun() bool {
	if dbg.vm.prg == nil || dbg.vm.prg.code == nil {
		return false
	}
	return dbg.vm.pc < len(dbg.vm.prg.code)
}


func (dbg *Debugger) StepIn() error {
	if debugContinue {
		fmt.Printf("[DEBUGGER-STEPIN] Called: was stepIn=%v, next=%v, lifecycleTransition=%v\n",
			dbg.stepIn, dbg.next, dbg.lifecycleTransition)
	}
	dbg.stepIn = true
	dbg.next = false
	dbg.continuing = false
	dbg.lifecycleTransition = false
	dbg.userCommandIssued = true

	// Invalidate per-pause snapshot — we're resuming.
	dbg.pausedVarSnapshot = nil

	activeDbg := globalDebugCoordinator.GetActiveDebugger()
	var steppingFilename string
	var callDepth int
	var gotValidState bool

	if activeDbg != nil {
		steppingFilename = activeDbg.lastBreakpoint.filename
		callDepth = activeDbg.lastBreakpoint.stackDepth
		startLine := activeDbg.lastBreakpoint.line
		gotValidState = startLine >= 0 && steppingFilename != ""
		if debugContinue {
			fmt.Printf("[DEBUGGER-STEPIN] Using active debugger state: file=%s, depth=%d, line=%d, valid=%v\n",
				steppingFilename, callDepth, startLine, gotValidState)
		}
	}

	if !gotValidState && dbg.vm != nil {
		steppingFilename = dbg.lastBreakpoint.filename
		callDepth = dbg.lastBreakpoint.stackDepth
		startLine := dbg.lastBreakpoint.line
		gotValidState = startLine >= 0 && steppingFilename != ""
		if debugContinue {
			fmt.Printf("[DEBUGGER-STEPIN] Fallback to local debugger state: file=%s, depth=%d, line=%d, valid=%v\n",
				steppingFilename, callDepth, startLine, gotValidState)
		}
	}

	if !gotValidState {
		steppingFilename = dbg.lastBreakpoint.filename
		callDepth = dbg.lastBreakpoint.stackDepth
		gotValidState = dbg.lastBreakpoint.line >= 0 && steppingFilename != ""
		if debugContinue {
			fmt.Printf("[DEBUGGER-STEPIN] Fallback to lastBreakpoint: file=%s, depth=%d, line=%d, valid=%v\n",
				steppingFilename, callDepth, dbg.lastBreakpoint.line, gotValidState)
		}
	}

	if gotValidState {
		// Don't overwrite lastBreakpoint.pc/line — keep the snapshot values set at pause time.
		dbg.lastBreakpoint.filename = steppingFilename
		dbg.lastBreakpoint.stackDepth = callDepth
	}

	if gotValidState {
		dbg.steppingFilename = steppingFilename
		// Compute lastPC for the start line so sub-expressions are skipped
		// even across temporary depth changes (e.g., method call arguments).
		if dbg.vm != nil && dbg.vm.prg != nil && !dbg.vmResuming.Load() {
			startLine := dbg.lastBreakpoint.line
			dbg.stepInStartLine = startLine
			dbg.stepInLastPC = dbg.vm.prg.lastPCForLine(startLine, dbg.lastBreakpoint.pc, steppingFilename)
			dbg.stepInLastPCPrg = dbg.vm.prg
			// LOOP GUARD: same as step-over — disable sub-expression skip
			// if the range spans a loop body (contains a backward jump),
			// OR if there are no sub-expressions ahead (lastPC <= breakpointPC).
			if dbg.stepInLastPC > dbg.lastBreakpoint.pc {
				if dbg.vm.prg.hasBackwardJumpBetween(dbg.lastBreakpoint.pc, dbg.stepInLastPC) {
					dbg.stepInLastPC = -1
					dbg.stepInLastPCPrg = nil
				}
			} else {
				dbg.stepInLastPC = -1
				dbg.stepInLastPCPrg = nil
			}
		} else {
			dbg.stepInStartLine = 0
			dbg.stepInLastPC = -1
			dbg.stepInLastPCPrg = nil
		}
	} else {
		dbg.steppingFilename = ""
		dbg.stepInStartLine = 0
		dbg.stepInLastPC = -1
		dbg.stepInLastPCPrg = nil
		if debugContinue {
			fmt.Printf("[DEBUGGER-STEPIN] ⚠️ No valid state, using empty steppingFilename\n")
		}
	}

	if !globalDebugCoordinator.IsMultiVUDebug() {
		globalDebugCoordinator.SetGlobalStepState(false, true, steppingFilename, callDepth)
	} else {
		globalDebugCoordinator.SetVUStepState(dbg.vuID, false, true, steppingFilename, callDepth)
	}
	if debugContinue {
		fmt.Printf("[DEBUGGER-STEPIN] After SetGlobalStepState: stepIn=%v, next=%v, steppingFilename=%s, callDepth=%d, multiVU=%v, vuID=%d\n",
			dbg.stepIn, dbg.next, steppingFilename, callDepth, globalDebugCoordinator.IsMultiVUDebug(), dbg.vuID)
	}


	if dbg.pendingCh != nil {
		if dbg.pendingCh == dbg.currentCh {
			safeCloseActivationCh(dbg.pendingCh)
			dbg.pendingCh = nil
			dbg.currentCh = nil
		} else {
			safeCloseActivationCh(dbg.pendingCh)
			dbg.pendingCh = nil
		}
	}
	return nil
}

func (dbg *Debugger) EnableStepIn() {
	if debugActivate {
		fmt.Printf("[DEBUGGER] EnableStepIn: BEFORE - stepIn=%v, next=%v, lifecycleTransition=%v\n",
			dbg.stepIn, dbg.next, dbg.lifecycleTransition)
	}
	dbg.stepIn = true
	dbg.continuing = false
	dbg.next = false
	dbg.lifecycleTransition = true

	globalDebugCoordinator.SetPendingLifecycleStepIn(true)
	globalDebugCoordinator.SetGlobalStepState(false, true, dbg.Filename(), 0)

	if debugActivate {
		fmt.Printf("[DEBUGGER] EnableStepIn: AFTER - stepIn=%v, next=%v, lifecycleTransition=%v (step-in mode enabled for next execution)\n",
			dbg.stepIn, dbg.next, dbg.lifecycleTransition)
	}
}

func (dbg *Debugger) SetStepIn(v bool) {
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] SetStepIn: %v (was: %v)\n", v, dbg.stepIn)
	}
	dbg.stepIn = v
}

// SetSkipPhaseEntryBreak tells the debug loop to skip the very first break
// at a lifecycle function entry (the function-signature line) and instead
// continue to the first executable statement.  This eliminates the extra
// step-over the user would otherwise need to reach real code.
func (dbg *Debugger) SetSkipPhaseEntryBreak(v bool) {
	dbg.skipPhaseEntryBreak = v
}

func (dbg *Debugger) GetStepIn() bool {
	return dbg.stepIn
}

func (dbg *Debugger) SetNext(v bool) {
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] SetNext: %v (was: %v)\n", v, dbg.next)
	}
	dbg.next = v
}

func (dbg *Debugger) GetNext() bool {
	return dbg.next
}

func (dbg *Debugger) SetContinuing(v bool) {
	dbg.continuing = v
}

func (dbg *Debugger) ResetLastBreakpoint() {
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] ResetLastBreakpoint: clearing (was: file=%s, line=%d, pc=%d)\n",
			dbg.lastBreakpoint.filename, dbg.lastBreakpoint.line, dbg.lastBreakpoint.pc)
	}
	dbg.lastBreakpoint.line = 0
	dbg.lastBreakpoint.pc = -1
	dbg.lastBreakpoint.filename = ""
	dbg.lastBreakpoint.stackDepth = 0
}

func (dbg *Debugger) ResetVMExited() {
	if debugActivate {
		fmt.Printf("[DEBUGGER] ResetVMExited: was=%v, uncaughtException=%v, setting to false\n", dbg.vmExited, dbg.uncaughtExceptionExit)
	}

	// If the previous iteration exited due to an uncaught exception, the old
	// Continue() may have left a stale currentCh in the coordinator channel.
	// Drain it so the new iteration's activate() doesn't pick it up — which
	// would cause the debugger to "loop back" to the same breakpoint.
	if dbg.uncaughtExceptionExit {
		// Drain per-VU coordinator channel
		vuCh := globalDebugCoordinator.GetVUActivationChannel(dbg.vuID)
		select {
		case <-vuCh:
			if debugActivate {
				fmt.Printf("[DEBUGGER] ResetVMExited: drained stale channel from per-VU coordinator (vuID=%d)\n", dbg.vuID)
			}
		default:
		}
		// Drain global coordinator channel
		globalCh := globalDebugCoordinator.ActivationChannel()
		select {
		case <-globalCh:
			if debugActivate {
				fmt.Printf("[DEBUGGER] ResetVMExited: drained stale channel from global coordinator\n")
			}
		default:
		}
		// Drain local activation channel
		select {
		case <-dbg.activationCh:
			if debugActivate {
				fmt.Printf("[DEBUGGER] ResetVMExited: drained stale channel from local activationCh\n")
			}
		default:
		}
	}

	dbg.uncaughtExceptionExit = false
	dbg.pendingUncaughtException = nil
	// Release any blocked exception wait before clearing
	if dbg.exceptionWaitCh != nil {
		select {
		case <-dbg.exceptionWaitCh:
		default:
			close(dbg.exceptionWaitCh)
		}
		dbg.exceptionWaitCh = nil
	}
	dbg.vmExited = false
	dbg.vmDoneCh = make(chan struct{})
}

func (dbg *Debugger) List() ([]string, error) {
	if dbg.vm.prg == nil || dbg.vm.prg.src == nil {
		return nil, errors.New("no program source available")
	}
	return stringToLines(dbg.vm.prg.src.Source())
}

// StepOut resumes execution until the current function returns,
// then breaks at the call site in the parent frame.
func (dbg *Debugger) StepOut() error {
	if debugContinue {
		fmt.Printf("[DEBUGGER-STEPOUT] Called: depth=%d, stepIn=%v, next=%v\n",
			dbg.callStackDepth(), dbg.stepIn, dbg.next)
	}
	dbg.stepIn = false
	dbg.next = false
	dbg.continuing = false
	dbg.lifecycleTransition = false
	dbg.userCommandIssued = true
	dbg.pausedVarSnapshot = nil

	// Target depth is ONE LESS than current — we want to break when we return
	// to the caller.
	currentDepth := dbg.callStackDepth()
	targetDepth := currentDepth - 1
	if targetDepth < 0 {
		targetDepth = 0
	}

	steppingFilename := ""
	if dbg.vm != nil && dbg.vm.prg != nil {
		steppingFilename = dbg.Filename()
	}

	// Reuse the global step state mechanism — but use stepOut sentinel:
	// We encode step-out as next=true with targetDepth = current-1.
	// The vm.debug() loop's atValidDepth check handles this correctly:
	//   atValidDepth := currentStackDepth <= stepOverTargetDepth
	// When we return from the function, depth drops to targetDepth, and
	// the NEXT line at that depth will trigger a break.
	dbg.next = true // use next's depth-gated break logic
	dbg.stepOverTargetDepth = targetDepth
	dbg.stepOverOriginalTargetDepth = targetDepth
	dbg.stepOverStartLine = dbg.Line() // don't re-break on current line
	dbg.steppingFilename = steppingFilename

	if !globalDebugCoordinator.IsMultiVUDebug() {
		globalDebugCoordinator.SetGlobalStepState(true, false, steppingFilename, targetDepth)
	} else {
		globalDebugCoordinator.SetVUStepState(dbg.vuID, true, false, steppingFilename, targetDepth)
	}
	if debugContinue {
		fmt.Printf("[DEBUGGER-STEPOUT] targetDepth=%d, steppingFilename=%s, multiVU=%v, vuID=%d\n",
			targetDepth, steppingFilename, globalDebugCoordinator.IsMultiVUDebug(), dbg.vuID)
	}


	if dbg.pendingCh != nil {
		if dbg.pendingCh == dbg.currentCh {
			safeCloseActivationCh(dbg.pendingCh)
			dbg.pendingCh = nil
			dbg.currentCh = nil
		} else {
			safeCloseActivationCh(dbg.pendingCh)
			dbg.pendingCh = nil
		}
	}
	return nil
}

// getSourceVarInfo parses the source to find params and locals visible at the current line.
// PERF: cache is now keyed by (functionStartLine, currentLine) so it correctly
// invalidates when the current line changes, and correctly reuses within the same pause.
func (dbg *Debugger) getSourceVarInfo(functionStartLine int) *sourceVarInfo {
	currentLine := dbg.Line()
	key := sourceVarCacheKey{functionStartLine, currentLine}
	if info, exists := dbg.sourceVarCache[key]; exists {
		return info
	}

	if dbg.vm.prg == nil || dbg.vm.prg.src == nil {
		return nil
	}

	info := &sourceVarInfo{
		params:    make(map[string]int),
		locals:    make(map[string]int),
		declLines: make(map[string]int),
	}

	// PERF: cache the split lines keyed by prg pointer — source is stable per-Program.
	// Avoids allocating a []string slice on every cache miss.
	if dbg.cachedSourceLinesPrg != dbg.vm.prg {
		dbg.cachedSourceLines = strings.Split(dbg.vm.prg.src.Source(), "\n")
		dbg.cachedSourceLinesPrg = dbg.vm.prg
	}
	lines := dbg.cachedSourceLines

	if currentLine < 0 || currentLine > len(lines) {
		return info
	}

	functionStart := -1
	var functionLine string
	braceDepth := 0

	for i := currentLine - 1; i >= 0; i-- {
		if i >= len(lines) {
			continue
		}
		line := lines[i]

		for _, ch := range line {
			if ch == '}' {
				braceDepth++
			} else if ch == '{' {
				braceDepth--
				if braceDepth < 0 {
					trimmed := strings.TrimSpace(line)
					// FIXED: detect arrow functions AND regular functions AND methods
					isFunctionLike := strings.Contains(trimmed, "function") ||
						strings.Contains(trimmed, "=>") ||
						isMethodOrConstructorLine(trimmed)
					if isFunctionLike {
						functionStart = i
						functionLine = trimmed
						goto foundFunction
					}
					// Even if not a function-like line, treat any opening brace
					// that closes our scan as a function boundary (handles
					// shorthand methods in object literals: { myMethod(x) { )
					functionStart = i
					functionLine = trimmed
					goto foundFunction
				}
			}
		}
	}

foundFunction:
	if functionStart < 0 {
		if dbg.sourceVarCache == nil {
			dbg.sourceVarCache = make(map[sourceVarCacheKey]*sourceVarInfo)
		}
		dbg.sourceVarCache[key] = info
		return info
	}

	// Extract params — handles:
	//   function foo(a, b)
	//   (a, b) =>
	//   foo(a, b) {        (method)
	//   constructor(a, b)
	if openParen := strings.Index(functionLine, "("); openParen >= 0 {
		// Find matching close paren (handles nested parens in default values)
		depth := 0
		closeParen := -1
		for j := openParen; j < len(functionLine); j++ {
			switch functionLine[j] {
			case '(':
				depth++
			case ')':
				depth--
				if depth == 0 {
					closeParen = j
				}
			}
			if closeParen >= 0 {
				break
			}
		}
		if closeParen > openParen {
			paramsStr := functionLine[openParen+1 : closeParen]
			if strings.TrimSpace(paramsStr) != "" {
				params := splitParams(paramsStr)
				for _, param := range params {
					paramName := extractParamName(param)
					if paramName != "" && isSimpleIdentifier(paramName) {
						info.params[paramName] = -(len(info.params) + 1)
						info.numParams++
					}
				}
			}
		}
	}

	endLine := currentLine - 1
	if endLine >= len(lines) {
		endLine = len(lines) - 1
	}

	localVarCount := 0
	braceDepth = 0

	for i := functionStart; i <= endLine; i++ {
		line := lines[i]
		trimmed := strings.TrimSpace(line)
		braceDepth += strings.Count(line, "{") - strings.Count(line, "}")

		if braceDepth == 1 {
			for _, keyword := range []string{"let ", "const ", "var "} {
				if !strings.HasPrefix(trimmed, keyword) {
					continue
				}
				rest := strings.TrimSpace(trimmed[len(keyword):])
				varName := ""
				for _, ch := range rest {
					if ch == ' ' || ch == '=' || ch == ';' || ch == ',' || ch == ':' || ch == '\t' {
						break
					}
					varName += string(ch)
				}
				varName = strings.TrimSpace(varName)
				if varName != "" && isSimpleIdentifier(varName) {
					if _, exists := info.locals[varName]; !exists {
						info.locals[varName] = localVarCount
						localVarCount++
						info.declLines[varName] = i + 1
					}
					break
				}
			}
		}
	}

	if dbg.sourceVarCache == nil {
		dbg.sourceVarCache = make(map[sourceVarCacheKey]*sourceVarInfo)
	}
	dbg.sourceVarCache[key] = info
	return info
}

// isMethodOrConstructorLine detects shorthand object/class methods:
//
//	myMethod(x, y) {
//	constructor(x) {
//	async fetchData(url) {
func isMethodOrConstructorLine(trimmed string) bool {
	// Must end with { or have { before a comment
	hasBrace := strings.Contains(trimmed, "{")
	if !hasBrace {
		return false
	}
	// Strip async/static/get/set prefixes
	s := trimmed
	for _, prefix := range []string{"async ", "static ", "get ", "set ", "public ", "private ", "protected "} {
		s = strings.TrimPrefix(s, prefix)
	}
	// Must have identifier followed by (
	parenIdx := strings.Index(s, "(")
	if parenIdx <= 0 {
		return false
	}
	name := strings.TrimSpace(s[:parenIdx])
	return isSimpleIdentifier(name) || name == "constructor"
}

// splitParams splits a parameter string by top-level commas
// (respecting nested parens/brackets for destructuring and defaults).
func splitParams(s string) []string {
	var params []string
	depth := 0
	start := 0
	for i, ch := range s {
		switch ch {
		case '(', '[', '{', '<':
			depth++
		case ')', ']', '}', '>':
			depth--
		case ',':
			if depth == 0 {
				params = append(params, strings.TrimSpace(s[start:i]))
				start = i + 1
			}
		}
	}
	if rest := strings.TrimSpace(s[start:]); rest != "" {
		params = append(params, rest)
	}
	return params
}

// extractParamName gets the binding identifier from a param pattern.
// Handles: plain `x`, typed `x: string`, defaulted `x = 5`,
// rest `...x`, destructured `{ x }` (skipped — can't be a simple identifier).
func extractParamName(param string) string {
	param = strings.TrimSpace(param)
	// Skip destructured params
	if strings.HasPrefix(param, "{") || strings.HasPrefix(param, "[") {
		return ""
	}
	// Strip rest prefix
	param = strings.TrimPrefix(param, "...")
	// Strip type annotation
	if colonIdx := strings.Index(param, ":"); colonIdx >= 0 {
		param = strings.TrimSpace(param[:colonIdx])
	}
	// Strip default value
	if eqIdx := strings.Index(param, "="); eqIdx >= 0 {
		param = strings.TrimSpace(param[:eqIdx])
	}
	return strings.TrimSpace(param)
}

func isSimpleIdentifier(s string) bool {
	if len(s) == 0 {
		return false
	}
	first := rune(s[0])
	if !((first >= 'a' && first <= 'z') || (first >= 'A' && first <= 'Z') || first == '_' || first == '$') {
		return false
	}
	for _, ch := range s[1:] {
		if !((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch == '_' || ch == '$') {
			return false
		}
	}
	return true
}

func isDotPropertyChain(s string) bool {
	if len(s) == 0 || !strings.Contains(s, ".") {
		return false
	}
	for _, ch := range s {
		if !((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch == '_' || ch == '$' || ch == '.' || ch == '?') {
			return false
		}
	}
	// Normalize: strip optional chaining operator for validation
	normalized := strings.ReplaceAll(s, "?.", ".")
	normalized = strings.TrimRight(normalized, "?")
	if normalized[0] == '.' || normalized[len(normalized)-1] == '.' || strings.Contains(normalized, "..") {
		return false
	}
	return true
}

// ── Source Map Name Mapping (Node.js / Chrome DevTools parity) ───────────────
//
// When TypeScript is bundled, the bundler may rename variables to avoid
// collisions (e.g., "import {test} from 'k6/execution'" plus "let test = ..."
// causes the bundler to rename the local to "test2"). The source map's "names"
// array encodes the original identifier name at each generated position.
//
// buildSourceMapNameMapping walks all VarLocation entries from debug symbols,
// queries the source map at each variable's access-point PCs, and builds two
// maps:
//   - genToOrig: generated stash name → original source name  (display)
//   - origToGen: original source name → generated stash name  (lookup)
//
// Cached per *Program — the mapping is stable for the lifetime of a compiled
// function. Only built when debugMode is enabled and a source map exists.

// buildSourceMapNameMapping builds (or returns cached) bidirectional name
// mappings between generated variable names and original source names using
// the source map. Returns (genToOrig, origToGen). Both maps may be nil when
// no source map is available or no renames were detected.
// Only runs in debug mode — all source map access is confined here.
// Wrapped in recover so a panic can never crash the calling goroutine.
func (dbg *Debugger) buildSourceMapNameMapping() (genToOrig, origToGen map[string]string) {
	if !dbg.vm.debugMode {
		return nil, nil
	}

	// Recover from any panic — this is a best-effort debugger enhancement.
	// A failure here must never affect stepping/continue/activation flow.
	defer func() {
		if r := recover(); r != nil {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] buildSourceMapNameMapping: recovered from panic: %v\n", r)
			}
			genToOrig = nil
			origToGen = nil
			dbg.cachedNameMapPrg = nil // invalidate cache on error
		}
	}()

	prg := dbg.vm.prg
	if prg == nil || prg.src == nil || prg.src.SourceMap() == nil {
		return nil, nil
	}

	// Return cached mapping if still valid for this program.
	if dbg.cachedNameMapPrg == prg {
		return dbg.cachedGenToOrig, dbg.cachedOrigToGen
	}

	sm := prg.src.SourceMap()
	genSrc := prg.src.Source()
	genToOrig = make(map[string]string)
	origToGen = make(map[string]string)

	// Strategy: walk all debug-symbol VarLocations. For each variable, probe
	// the source map at a few PCs within its range to find a name mapping.
	// The source map entry at a given generated position returns the original
	// identifier name — we pair that with the VarLocation.Name (the generated
	// name) to build the bidirectional map.
	if prg.debugSymbols != nil {
		allVarLocs := prg.debugSymbols.LookupVarsAtPC(dbg.vm.pc)

		for _, varLoc := range allVarLocs {
			genName := varLoc.Name
			if !isSimpleIdentifier(genName) || strings.TrimSpace(genName) == "this" {
				continue
			}

			// Probe the source map at the VarLocation's StartPC and the
			// current PC. The source map name entry is only set at positions
			// that correspond to identifier tokens, so we may need to check
			// multiple PCs.
			probePCs := []int{varLoc.StartPC}
			if dbg.vm.pc != varLoc.StartPC {
				probePCs = append(probePCs, dbg.vm.pc)
			}

			for _, probePC := range probePCs {
				if probePC < 0 || probePC >= len(prg.code) {
					continue
				}
				srcOffset := prg.sourceOffset(probePC)
				originalName := debugSourceMapNameAtOffset(sm, genSrc, srcOffset)
				if originalName != "" && originalName != genName && isSimpleIdentifier(originalName) {
					genToOrig[genName] = originalName
					origToGen[originalName] = genName
					break
				}
			}
		}

		// If the direct approach didn't find mappings, try a bounded scan
		// of srcMap entries. Cap at 500 entries to prevent slowness on large
		// bundles — this is a best-effort fallback.
		if len(genToOrig) == 0 && len(prg.srcMap) > 0 {
			limit := len(prg.srcMap)
			if limit > 500 {
				limit = 500
			}
			for i := 0; i < limit; i++ {
				item := prg.srcMap[i]
				originalName := debugSourceMapNameAtOffset(sm, genSrc, item.srcPos)
				if originalName == "" || !isSimpleIdentifier(originalName) {
					continue
				}
				genToken := extractIdentifierAt(genSrc, item.srcPos)
				if genToken != "" && genToken != originalName {
					if _, exists := genToOrig[genToken]; !exists {
						genToOrig[genToken] = originalName
					}
					if _, exists := origToGen[originalName]; !exists {
						origToGen[originalName] = genToken
					}
				}
			}
		}
	}

	// Cache for this program.
	dbg.cachedNameMapPrg = prg
	dbg.cachedGenToOrig = genToOrig
	dbg.cachedOrigToGen = origToGen

	if debugCompiler && len(genToOrig) > 0 {
		fmt.Printf("[DEBUGGER] Source map name mapping built: %d entries\n", len(genToOrig))
		for gen, orig := range genToOrig {
			if debugActivate {
				fmt.Printf("[DEBUGGER]   %s → %s (original)\n", gen, orig)
			}
		}
	}

	return genToOrig, origToGen
}

// debugSourceMapNameAtOffset queries the source map for the original identifier
// name at the given source offset in the generated JS code. Returns "" if no
// name mapping exists. This duplicates the line/col computation from
// file.Position() so the debugger can query the source map without modifying
// any runtime code — all calls are gated by if-debugMode.
func debugSourceMapNameAtOffset(sm *sourcemap.Consumer, genSrc string, offset int) string {
	if sm == nil || offset < 0 || offset >= len(genSrc) {
		return ""
	}

	// Compute generated line/col from the source offset.
	// This mirrors the logic in file.File.Position() exactly.
	line := 0
	lastLineStart := 0
	for i := 0; i < offset && i < len(genSrc); i++ {
		if genSrc[i] == '\n' {
			line++
			lastLineStart = i + 1
		} else if genSrc[i] == '\r' {
			line++
			if i+1 < len(genSrc) && genSrc[i+1] == '\n' {
				i++ // skip \r\n as one newline
			}
			lastLineStart = i + 1
		}
	}

	// file.Position uses 1-based (row = line+2, col = offset-lineStart+1)
	// because lineOffsets stores positions after newlines and starts scanning
	// from 0. Our simpler scan counts actual newlines, so:
	row := line + 1 // 1-based line number in generated code
	col := offset - lastLineStart + 1

	_, name, _, _, ok := sm.Source(row, col)
	if ok {
		return name
	}
	return ""
}

// extractIdentifierAt extracts the JavaScript identifier token starting at or
// near the given offset in the source string. Returns "" if no identifier is
// found. This reads the generated JS code to figure out what identifier the
// bundler placed at a given source map position.
func extractIdentifierAt(src string, offset int) string {
	if offset < 0 || offset >= len(src) {
		return ""
	}

	// The source map offset might point to the start of the identifier or
	// slightly before/after. Scan forward to find the start of an identifier.
	start := offset
	// If we're not at an identifier start, scan forward a little.
	if start < len(src) && !isIdentStart(rune(src[start])) {
		// Try a few positions forward (whitespace, operator, etc.)
		for i := start; i < start+5 && i < len(src); i++ {
			if isIdentStart(rune(src[i])) {
				start = i
				break
			}
		}
	}
	if start >= len(src) || !isIdentStart(rune(src[start])) {
		return ""
	}

	// Collect the identifier.
	end := start + 1
	for end < len(src) && isIdentPart(rune(src[end])) {
		end++
	}
	token := src[start:end]
	if isSimpleIdentifier(token) {
		return token
	}
	return ""
}

func isIdentStart(r rune) bool {
	return (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || r == '_' || r == '$'
}

func isIdentPart(r rune) bool {
	return isIdentStart(r) || (r >= '0' && r <= '9')
}

// resolveOriginalName translates an original source name to its generated
// (bundler-renamed) counterpart using the source map name mapping.
// Returns "" if no mapping exists. Only works in debug mode.
func (dbg *Debugger) resolveOriginalName(originalName string) string {
	if !dbg.vm.debugMode {
		return ""
	}
	_, origToGen := dbg.buildSourceMapNameMapping()
	if origToGen == nil {
		return ""
	}
	return origToGen[originalName]
}

// resolveGeneratedName translates a generated (bundler) name back to the
// original source name. Returns "" if no mapping exists. Only works in debug mode.
func (dbg *Debugger) resolveGeneratedName(generatedName string) string {
	if !dbg.vm.debugMode {
		return ""
	}
	genToOrig, _ := dbg.buildSourceMapNameMapping()
	if genToOrig == nil {
		return ""
	}
	return genToOrig[generatedName]
}

// stripTypeScriptSyntax removes TypeScript-only syntax from an expression
// so the JS runtime can evaluate it. Handles:
//   - Type assertions: "expr as Type", "expr as const" → "expr"
//   - Satisfies operator: "expr satisfies Type" → "expr"
//   - Parenthesized: "(expr as Type).prop" → "(expr).prop"
//   - Angle-bracket casts: "<Type>expr" → "expr"
//   - Non-null assertions: "expr!" → "expr"
//   - Type annotations: "x: Type" in simple contexts
//
// Uses a regex-based approach that handles the common patterns seen in
// debug evaluate/hover without needing a full TS parser.
//
// The regex handles both uppercase types (Error, Map<K,V>) and lowercase
// TS built-in types (string, number, boolean, any, unknown, never, void,
// object, symbol, bigint, undefined, null, const, readonly).
var tsAsTypeRegex = regexp.MustCompile(`\s+as\s+(?:const|readonly|[A-Za-z_$][\w$]*(?:\[\]|\<[^>]*\>)*)`)

// tsNonNullRegex matches TypeScript's non-null assertion operator (!)
// in all positions. It captures the char before ! ($1) and the char/end
// after ! ($2), stripping only the !. It requires ! to be preceded by a
// word char, ), or ], and followed by ., [, ,, ), ;, whitespace, or EOL.
// This avoids stripping logical-not (!expr) and != / !==.
// Examples: allStores!.length → allStores.length, arr![0] → arr[0]
var tsNonNullRegex = regexp.MustCompile(`([\w)\]])!([.\[,);\s])`)

// tsBuiltinLowercaseTypes are TypeScript-only type names that start with
// a lowercase letter and would never appear in valid JS after "<" as a
// comparison. Used by angle-bracket type cast stripping.
var tsBuiltinLowercaseTypes = map[string]bool{
	"string": true, "number": true, "boolean": true, "any": true,
	"unknown": true, "never": true, "void": true, "object": true,
	"symbol": true, "bigint": true, "undefined": true, "null": true,
}

// stripTypeScriptGenerics removes TypeScript generic type parameters from
// function/method calls. Handles all TypeScript type argument patterns:
//
//   - Simple types:         parseJson<Store[]>(x)          → parseJson(x)
//   - Nested generics:      Map<string, Array<number>>()   → Map()
//   - Function types:       fn<(x: number) => string>(y)   → fn(y)
//   - Object/mapped types:  fn<{key: string}>(obj)         → fn(obj)
//   - Default type params:  fn<T = string>(x)              → fn(x)
//   - Union/intersection:   fn<A | B>(x), fn<A & B>(x)    → fn(x)
//   - Conditional types:    fn<T extends U ? X : Y>(x)     → fn(x)
//   - Tuple types:          fn<[string, number]>(x)        → fn(x)
//   - Optional chaining:    obj?.method<T>(x)              → obj?.method(x)
//
// The algorithm scans left-to-right. When '<' is preceded by a word
// character, it tracks angle-bracket, parenthesis, and brace depth.
// The closing '>' is only recognised at the outermost paren/brace level.
// If the matching '>' is immediately followed by '(', the <…> span is
// a TypeScript generic call and is stripped. Otherwise it is treated as
// a less-than comparison and emitted verbatim.
func stripTypeScriptGenerics(expr string) string {
	var buf strings.Builder
	buf.Grow(len(expr))
	i := 0
	for i < len(expr) {
		ch := expr[i]
		if ch == '<' && i > 0 && isWordOrCloseBracket(expr[i-1]) {
			// Potential generic call: scan for matching '>' with full
			// depth tracking for nested angle brackets, parentheses
			// (function types), and braces (object/mapped types).
			angleDepth := 1
			parenDepth := 0
			braceDepth := 0
			j := i + 1
			valid := true
			for j < len(expr) && angleDepth > 0 {
				switch expr[j] {
				case '<':
					// Only count angle brackets at the top paren/brace level.
					// Inside (...) or {...}, '<' is a less-than operator.
					if parenDepth == 0 && braceDepth == 0 {
						angleDepth++
					}
				case '>':
					// Distinguish closing '>' from the '=>' arrow in function types.
					// In "(x: number) => string", the '>' after '=' is part of the
					// arrow operator, NOT a closing angle bracket.
					if j > 0 && expr[j-1] == '=' {
						// This is '=>' (arrow) — skip, not a closing angle bracket.
					} else if parenDepth == 0 && braceDepth == 0 {
						angleDepth--
					}
				case '(':
					parenDepth++
				case ')':
					parenDepth--
					if parenDepth < 0 {
						// Unbalanced paren — not a type argument.
						valid = false
						angleDepth = 0
					}
				case '{':
					braceDepth++
				case '}':
					braceDepth--
					if braceDepth < 0 {
						valid = false
						angleDepth = 0
					}
				case ';':
					// Semicolons never appear inside type arguments.
					valid = false
					angleDepth = 0
				}
				if angleDepth > 0 {
					j++
				}
			}
			// Generic call confirmed when:
			//   - valid (no unbalanced parens/braces/semis)
			//   - all depths balanced (angle=0, paren=0, brace=0)
			//   - closing '>' immediately followed by '('
			if valid && angleDepth == 0 && parenDepth == 0 && braceDepth == 0 &&
				j+1 < len(expr) && expr[j+1] == '(' {
				// Skip the entire <TypeArgs> span — advance i past '>' to '('
				i = j + 1
				continue
			}
		}
		buf.WriteByte(ch)
		i++
	}
	return buf.String()
}

// isWordOrCloseBracket returns true if b can precede a TypeScript generic
// '<' in a call expression. This includes identifier characters and ')'/']'
// to handle expressions like `(expr as Fn)<T>(x)`.
func isWordOrCloseBracket(b byte) bool {
	return (b >= 'a' && b <= 'z') || (b >= 'A' && b <= 'Z') ||
		(b >= '0' && b <= '9') || b == '_' || b == '$' || b == ')' || b == ']'
}

// stripArrowParamTypes removes TypeScript type annotations from arrow function
// parameter lists. It finds `) =>` patterns, walks back to the matching `(`,
// and strips `: Type` annotations from each parameter within.
// e.g., "(c: RefinedResponse<ResponseType>) => expr" → "(c) => expr"
// e.g., "(a: string, b: number) => expr"             → "(a, b) => expr"
// e.g., "(a: Map<string, number>, b: string) => x"   → "(a, b) => x"
func stripArrowParamTypes(expr string) string {
	// Find all `) =>` or `)=>` positions and process each arrow function's params.
	result := expr
	for {
		arrowIdx := strings.Index(result, "=>")
		if arrowIdx < 0 {
			break
		}

		// Find the `)` before `=>`
		closeIdx := -1
		for i := arrowIdx - 1; i >= 0; i-- {
			if result[i] == ')' {
				closeIdx = i
				break
			} else if result[i] != ' ' && result[i] != '\t' {
				break
			}
		}
		if closeIdx < 0 {
			// Single param without parens (x => ...) or no match — skip this arrow
			// Move past this `=>` and keep searching
			remaining := result[arrowIdx+2:]
			nextArrow := strings.Index(remaining, "=>")
			if nextArrow < 0 {
				break
			}
			arrowIdx = arrowIdx + 2 + nextArrow
			continue
		}

		// Find the matching `(` by counting nesting
		openIdx := -1
		depth := 1
		for i := closeIdx - 1; i >= 0; i-- {
			switch result[i] {
			case ')':
				depth++
			case '(':
				depth--
				if depth == 0 {
					openIdx = i
				}
			}
			if openIdx >= 0 {
				break
			}
		}
		if openIdx < 0 {
			break
		}

		// Extract the parameter list and strip type annotations
		paramStr := result[openIdx+1 : closeIdx]
		if strings.Contains(paramStr, ":") {
			stripped := stripParamTypeAnnotations(paramStr)
			result = result[:openIdx+1] + stripped + result[closeIdx:]
		}

		// Move past this arrow to avoid infinite loop
		// The result may have shifted, so just break and re-run if needed
		break
	}

	// Handle multiple arrows by recursing if there are more
	if strings.Count(result, "=>") > 1 && result != expr {
		// Avoid infinite recursion — only recurse if we made progress
		result = stripArrowParamTypes(result)
	}

	return result
}

// stripParamTypeAnnotations strips `: Type` from each parameter in a
// comma-separated parameter list, handling nested generics like Map<K, V>.
// e.g., "c: RefinedResponse<ResponseType>" → "c"
// e.g., "a: string, b: number"             → "a, b"
// e.g., "a: Map<string, number>, b: Foo"   → "a, b"
func stripParamTypeAnnotations(params string) string {
	var result []string
	// Split by commas, but respect angle-bracket nesting
	var current strings.Builder
	depth := 0 // angle bracket depth
	for i := 0; i < len(params); i++ {
		ch := params[i]
		switch ch {
		case '<':
			depth++
			current.WriteByte(ch)
		case '>':
			depth--
			current.WriteByte(ch)
		case ',':
			if depth == 0 {
				result = append(result, stripSingleParamType(current.String()))
				current.Reset()
			} else {
				current.WriteByte(ch)
			}
		default:
			current.WriteByte(ch)
		}
	}
	if current.Len() > 0 {
		result = append(result, stripSingleParamType(current.String()))
	}
	return strings.Join(result, ", ")
}

// stripSingleParamType strips the `: Type` annotation from a single parameter.
// e.g., "c: RefinedResponse<ResponseType>" → "c"
// e.g., " a: string " → "a"
func stripSingleParamType(param string) string {
	param = strings.TrimSpace(param)
	colonIdx := strings.Index(param, ":")
	if colonIdx < 0 {
		return param
	}
	// Everything before the colon is the parameter name (possibly with ? for optional)
	name := strings.TrimSpace(param[:colonIdx])
	if name == "" || !isSimpleIdentifier(strings.TrimRight(name, "?")) {
		// Not a param type annotation (might be destructuring or something else)
		return param
	}
	return name
}

func stripTypeScriptSyntax(expr string) string {
	// ── Arrow function parameter type annotations ────────────────────────
	// e.g., "(c: RefinedResponse<ResponseType>) => ..." → "(c) => ..."
	// e.g., "(a: string, b: number) => ..."             → "(a, b) => ..."
	// Must run BEFORE generics stripping to handle types with generics.
	if strings.Contains(expr, "=>") && strings.Contains(expr, ":") {
		expr = stripArrowParamTypes(expr)
	}

	// ── Generic call syntax: identifier<TypeArgs>( → identifier( ──────
	// This MUST run first because type args can contain [] and other chars
	// that would confuse subsequent patterns.
	// e.g., "this.parseJson<Store[]>(response)" → "this.parseJson(response)"
	// e.g., "new Map<string, number>()"          → "new Map()"
	// e.g., "fn<T, U>(a, b)"                     → "fn(a, b)"
	if strings.Contains(expr, "<") && strings.Contains(expr, ">(") {
		expr = stripTypeScriptGenerics(expr)
	}

	// Strip "as Type" / "as const" / "as readonly" assertions
	// (including "as Type[]", "as Map<K,V>", "as string", "as number")
	// e.g., "(error as Error).message" → "(error).message"
	// e.g., "arr as string[]" → "arr"
	// e.g., "x as const" → "x"
	if strings.Contains(expr, " as ") {
		expr = tsAsTypeRegex.ReplaceAllString(expr, "")
	}

	// Strip "satisfies Type" (TypeScript 4.9+)
	// e.g., "config satisfies Config" → "config"
	if strings.Contains(expr, " satisfies ") {
		expr = tsSatisfiesRegex.ReplaceAllString(expr, "")
	}

	// Strip angle-bracket type casts: "<Error>error" → "error"
	// Only at the start of the expression or after ( to avoid matching
	// less-than comparisons like "a < b"
	if strings.HasPrefix(expr, "<") {
		if idx := strings.Index(expr, ">"); idx > 0 {
			inner := expr[1:idx]
			if len(inner) > 0 {
				// Accept uppercase types (Error, Map, etc.) and known lowercase TS types
				if (inner[0] >= 'A' && inner[0] <= 'Z') || tsBuiltinLowercaseTypes[inner] {
					expr = expr[idx+1:]
				}
			}
		}
	}

	// Strip TypeScript non-null assertion operator (!) in all positions.
	// Handles: obj!.prop, arr![0], fn(arg!), getValue()!, expr!
	// Does NOT strip: !expr (logical not), !== , !=
	if strings.Contains(expr, "!") {
		expr = tsNonNullRegex.ReplaceAllString(expr, "${1}${2}")
		// Also strip trailing ! (e.g., "getValue()!" → "getValue()")
		for len(expr) > 1 && expr[len(expr)-1] == '!' {
			before := expr[len(expr)-2]
			if before == ')' || before == ']' || (before >= 'a' && before <= 'z') ||
				(before >= 'A' && before <= 'Z') || (before >= '0' && before <= '9') || before == '_' || before == '$' {
				expr = expr[:len(expr)-1]
			} else {
				break
			}
		}
	}

	// Strip trailing TypeScript optional parameter marker (?).
	// When hovering on a TypeScript optional parameter like "businessContext?: string",
	// the IDE may send "businessContext?" as the expression. Strip the trailing ?
	// so it resolves as the plain identifier "businessContext".
	// Only strip when ? is at the end after a word character (not ternary operator).
	if len(expr) > 1 && expr[len(expr)-1] == '?' {
		before := expr[len(expr)-2]
		if (before >= 'a' && before <= 'z') || (before >= 'A' && before <= 'Z') ||
			(before >= '0' && before <= '9') || before == '_' || before == '$' {
			expr = expr[:len(expr)-1]
		}
	}

	// Strip TypeScript type annotations from parameter-like expressions.
	// e.g., "businessContext?: string" → "businessContext"
	// e.g., "market?: string" → "market"
	if strings.Contains(expr, ":") {
		if idx := strings.Index(expr, ":"); idx > 0 {
			candidate := strings.TrimRight(strings.TrimSpace(expr[:idx]), "?")
			if isSimpleIdentifier(candidate) {
				expr = candidate
			}
		}
	}

	return strings.TrimSpace(expr)
}

func (dbg *Debugger) Evaluate(expr string) (Value, error) {
	if expr == "" {
		return nil, errors.New("nothing to evaluate")
	}
	// Fast-reject if the VM is resuming — no point evaluating, the pause
	// is over and VM state will change momentarily.
	if dbg.vmResuming.Load() {
		return nil, fmt.Errorf("cannot evaluate: VM is resuming")
	}

	// Strip TypeScript syntax that the JS runtime can't parse.
	// e.g., "(error as Error).message" → "(error).message"
	expr = stripTypeScriptSyntax(expr)

	// Strip spread operator (...) — when hovering over "...profile.options" or
	// "...profile.options?.tags", the IDE sends the full text including the spread.
	// The user wants to see the value being spread, not execute a spread expression.
	if strings.HasPrefix(expr, "...") {
		expr = expr[3:]
	}

	if isSimpleIdentifier(expr) {
		val, err := dbg.getValue(expr)
		if err == nil && val != nil {
			if _, isUnresolved := val.(valueUnresolved); !isUnresolved {
				return val, nil
			}
		}
		// PERF: For simple identifiers that getValue couldn't resolve, check
		// the paused variable snapshot. If the identifier isn't there either,
		// it's definitely not in scope — return immediately without calling
		// evaluateComplexExpression (which would compile JS, run it, and throw
		// a ReferenceError). This is critical for inline value preview which
		// sends hundreds of evaluate requests for every identifier in the viewport.
		snap := dbg.buildPausedVarSnapshot()
		if snap != nil {
			if _, found := snap[expr]; !found {
				return nil, fmt.Errorf("variable '%s' not found in current scope", expr)
			}
		}
	}

	if isDotPropertyChain(expr) {
		// Normalize optional chaining: "this.tokens?.backofficeAuth" → split on "."
		// but track which segments had "?" (optional chaining)
		parts := strings.Split(expr, ".")
		root := parts[0]
		rootVal, err := dbg.getValue(root)
		if debugVM && root == "this" {
			fmt.Printf("[DEBUGGER-EVAL] Evaluate(%q): root='this', getValue returned val=%v (nil=%v), err=%v\n",
				expr, rootVal, rootVal == nil, err)
		}
		if err == nil && rootVal != nil {
			if _, isUnresolved := rootVal.(valueUnresolved); !isUnresolved {
				// Wrap property access in withSuppressedDebugger — obj.Get()
				// can trigger JS getters which would re-enter vm.debug(),
				// causing deadlocks or corrupted VM state.
				result := dbg.withSuppressedDebugger(func() Value {
					val := rootVal
					for _, prop := range parts[1:] {
						// Handle optional chaining: strip trailing "?" from property name
						optional := strings.HasSuffix(prop, "?")
						prop = strings.TrimSuffix(prop, "?")

						obj, ok := val.(*Object)
						if !ok {
							if optional {
								return _undefined
							}
							return nil
						}
						propVal := obj.Get(prop)
						if propVal == nil || propVal == _undefined {
							return _undefined
						}
						val = propVal
					}
					return val
				})
				if result != nil {
					return result, nil
				}
			}
		}
		// PERF: If the root identifier isn't in the paused var snapshot,
		// it's not in scope — skip the expensive evaluateComplexExpression
		// which would compile+run JS only to get a ReferenceError.
		// This is critical for VS Code inline value preview (hover context)
		// which sends hundreds of evaluate requests per pause.
		snap := dbg.buildPausedVarSnapshot()
		if snap != nil {
			if _, found := snap[root]; !found {
				return nil, fmt.Errorf("variable '%s' not found in current scope", root)
			}
		}
	}

	return dbg.evaluateComplexExpression(expr)
}

// buildPausedVarSnapshot collects all accessible variables once per pause and caches them.
// Subsequent evals during the same pause reuse the snapshot without re-walking the stash.
func (dbg *Debugger) buildPausedVarSnapshot() map[string]Value {
	// PERF: If frozen (during eval), return the existing snapshot to prevent
	// corruption from getter-triggered rebuilds.
	if dbg.pausedVarSnapshotFrozen && dbg.pausedVarSnapshot != nil {
		return dbg.pausedVarSnapshot
	}

	currentLine := dbg.Line()
	currentPC := dbg.vm.pc
	// Cache key includes BOTH line and PC. Multiple instructions can map to the
	// same source line (e.g., before and after a call expression). Using line-only
	// would serve stale data when the PC advances within the same line.
	if dbg.pausedVarSnapshot != nil && dbg.pausedVarSnapshotLine == currentLine && dbg.pausedVarSnapshotPC == currentPC {
		return dbg.pausedVarSnapshot
	}

	// PERF: Reuse the pool map instead of allocating a new one on every pause.
	// Delete-loop removes all entries without releasing the underlying memory.
	snap := dbg.pausedVarPool
	if snap == nil {
		snap = make(map[string]Value, 64)
		dbg.pausedVarPool = snap
	} else {
		for k := range snap {
			delete(snap, k)
		}
	}

	// Walk stash chain.
	// When paused on an exception, use the stash captured at the throw site
	// (before handleThrow unwound it) so the user sees variables from the
	// scope where the exception was thrown — matching Chrome DevTools.
	thisKey := unistring.String(thisBindingName)
	stashLevel := 0
	startStash := dbg.vm.stash
	if dbg.exceptionBreakActive && dbg.exceptionStash != nil {
		startStash = dbg.exceptionStash
	}
	for s := startStash; s != nil; s = s.outer {
		if s.names != nil {
			for name, idx := range s.names {
				// PERF: Handle " this" using direct constant comparison
				// instead of String()+TrimSpace() for every name.
				if name == thisKey {
					actualIdx := idx & uint32(maskIndex)
					if int(actualIdx) < len(s.values) {
						val := s.values[actualIdx]
						if val != nil && !isNullValue(val) {
							if snap["this"] == nil {
								snap["this"] = val
							}
						}
						// skip — uninitialized this is not useful
					}
					continue
				}
				nameStr := name.String()
				if snap[nameStr] != nil || globalBuiltinKeys[nameStr] {
					continue
				}
				actualIdx := idx & uint32(maskIndex)
				isIndirect := (idx & maskIndirect) != 0
				if int(actualIdx) < len(s.values) {
					val := s.values[actualIdx]
					if val != nil && !isNullValue(val) {
						if isIndirect && !lifecycleFunctionKeys[nameStr] {
							val = dbg.safeResolveIndirectValue(nameStr, val)
						}
						if isSimpleIdentifier(nameStr) {
							snap[nameStr] = val
						}
					} else if dbg.vm.debugMode {
						// Variable exists in stash but is nil (const/let before
						// assignment, e.g. RHS threw). Show as undefined so
						// hover/variables panel displays it instead of nothing.
						if isSimpleIdentifier(nameStr) {
							snap[nameStr] = _undefined
						}
					}
				}
			}
		}
		if s.obj != nil {
			for _, keyStr := range safeStringKeys(s.obj) {
				if snap[keyStr] != nil || !isSimpleIdentifier(keyStr) || globalBuiltinKeys[keyStr] || globalUnsafeKeys[keyStr] {
					continue
				}
				if v := safeGetGlobalProperty(s.obj, unistring.String(keyStr)); v != nil && !isNullValue(v) {
					snap[keyStr] = v
				}
			}
		}
		stashLevel++
	}

	// Global object.
	if dbg.vm.r != nil {
		if globalObj := dbg.vm.r.globalObject; globalObj != nil {
			for _, keyStr := range safeStringKeys(globalObj) {
				if snap[keyStr] != nil {
					continue
				}
				if isIdentifierLike(keyStr) && keyStr != "" &&
					!globalBuiltinKeys[keyStr] && !globalUnsafeKeys[keyStr] {
					if v := safeGetGlobalProperty(globalObj, unistring.String(keyStr)); v != nil && !isNullValue(v) {
						snap[keyStr] = v
					}
				}
			}
		}
	}

	// ── Source map name remapping (debug mode only) ──────────────────────
	// When the bundler renames variables (e.g., "test" → "test2"), the stash
	// stores them under the generated name. Remap to original names so the
	// variables panel shows what the user wrote in their TypeScript source.
	// This mirrors how Chrome DevTools / Node.js present renamed variables.
	// Wrapped in func+recover so it can never affect stepping/continue flow.
	if dbg.vm.debugMode {
		func() {
			defer func() {
				if r := recover(); r != nil {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] buildPausedVarSnapshot: name remapping panicked: %v\n", r)
					}
				}
			}()
			genToOrig, _ := dbg.buildSourceMapNameMapping()
			if len(genToOrig) > 0 {
				for genName, origName := range genToOrig {
					if genName == origName {
						continue
					}
					if val, hasGen := snap[genName]; hasGen {
						if _, hasOrig := snap[origName]; !hasOrig {
							snap[origName] = val
							delete(snap, genName) // hide bundler-renamed variable
						}
					}
				}
			}
		}()
	}

	dbg.pausedVarSnapshot = snap
	dbg.pausedVarSnapshotLine = currentLine
	dbg.pausedVarSnapshotPC = currentPC

	// ── Promise unwrapping ──────────────────────────────────────────────
	// Unwrap settled Promises in the snapshot so the Variables panel and
	// hover show resolved values instead of opaque Promise objects.
	// This matches Node.js / Chrome DevTools behavior where variables
	// holding fulfilled promises display their resolved value.
	// Wrapped in func+recover for safety.
	func() {
		defer func() {
			if r := recover(); r != nil {
				if dbg.enableDebugLogging {
					fmt.Printf("[DEBUGGER] buildPausedVarSnapshot: promise unwrapping panicked: %v\n", r)
				}
			}
		}()
		for k, v := range snap {
			if v != nil && IsPromise(v) {
				unwrapped := UnwrapPromiseForDisplay(v)
				if unwrapped != v {
					snap[k] = unwrapped
				}
			}
		}
	}()

	return snap
}

func (dbg *Debugger) evaluateComplexExpression(expr string) (Value, error) {
	// If the VM is resuming, don't start a new eval — it would race.
	if dbg.vmResuming.Load() {
		return nil, fmt.Errorf("cannot evaluate: VM is resuming")
	}
	// CRITICAL: Only allow eval when the debugger is paused (active=true).
	// If the VM is running (not stopped at a breakpoint), eval would run
	// on the same VM concurrently — corrupting stack, stash, pc, and
	// causing nil pointer panics or wrong exceptions that kill the VU.
	if !dbg.active {
		return nil, fmt.Errorf("cannot evaluate: VM is not paused")
	}
	dbg.evalMutex.Lock()
	defer dbg.evalMutex.Unlock()
	// Track this operation so activate() waits for it before resuming.
	dbg.evalWG.Add(1)
	defer dbg.evalWG.Done()
	// Double-check after acquiring locks.
	if dbg.vmResuming.Load() {
		return nil, fmt.Errorf("cannot evaluate: VM is resuming")
	}

	if dbg.vm == nil || dbg.vm.r == nil {
		return nil, fmt.Errorf("cannot evaluate: no runtime")
	}

	// Try registry first (multi-scope eval for setup/teardown phases)
	// PERF: Only use the registry for simple identifiers or dot-property roots.
	// Complex expressions (function calls, array access, etc.) will never match
	// a variable name in the registry — skip to avoid expensive phase iteration.
	registry := GetGlobalRegistry()
	if registry != nil && isSimpleIdentifier(expr) {
		var result Value
		var err error
		func() {
			defer func() {
				if r := recover(); r != nil {
					err = fmt.Errorf("registry eval panicked: %v", r)
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] Registry eval panicked: %v\n", r)
					}
				}
			}()
			result, err = registry.MultiScopeEval(dbg.vm.r, expr)
		}()
		if err == nil && result != nil {
			return result, nil
		}
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] Registry eval failed: %v, falling back to direct eval\n", err)
		}
	}

	if dbg.vm.sb < 0 || dbg.vm.stash == nil {
		return nil, fmt.Errorf("cannot evaluate: invalid execution state")
	}

	// CRITICAL FIX (Bug 2 + Bug 3): Save state that can be corrupted by an
	// exception inside the eval expression (ReferenceError, TypeError, etc.).
	// BreakOnException → activateWithStepState overwrites lastBreakpoint,
	// causing the debugger to jump to the wrong location when the user resumes.
	// Also set inEvalContext so BreakOnException can bail out early (Bug 3).
	savedLastBreakpoint := dbg.lastBreakpoint
	savedExceptionBreakActive := dbg.exceptionBreakActive
	savedLastException := dbg.lastException
	savedPausedVarSnapshot := dbg.pausedVarSnapshot
	savedPausedVarSnapshotLine := dbg.pausedVarSnapshotLine
	savedPausedVarSnapshotPC := dbg.pausedVarSnapshotPC

	dbg.inEvalContext = true
	// PERF: Freeze the var snapshot during eval so getter-triggered rebuilds
	// don't overwrite it with stale data mid-evaluation.
	dbg.pausedVarSnapshotFrozen = true
	defer func() {
		dbg.lastBreakpoint = savedLastBreakpoint
		dbg.exceptionBreakActive = savedExceptionBreakActive
		dbg.lastException = savedLastException
		dbg.pausedVarSnapshot = savedPausedVarSnapshot
		dbg.pausedVarSnapshotLine = savedPausedVarSnapshotLine
		dbg.pausedVarSnapshotPC = savedPausedVarSnapshotPC
		dbg.inEvalContext = false
		dbg.pausedVarSnapshotFrozen = false
	}()

	// ── Core: compile as a direct-eval program with ctxVM=dbg.vm ──────────
	//
	// By passing dbg.vm as evalVm to the compiler, the compiled program
	// sees the current stash chain as its outer scope, giving it access to:
	//   - All local variables in the current function
	//   - All closure variables from enclosing functions
	//   - The correct `this` binding (resolved naturally from the stash chain)
	//   - The full prototype chain
	//   - Import bindings from ESM modules
	//
	// This mirrors how Node.js/V8 evaluates watch/hover expressions: compile
	// in the context of the paused call frame so the eval code uses dynamic
	// scope lookup (loadMixed/resolveMixed in sobek, LD_VAR_SCOPE in V8).
	//
	// This is strictly better than the previous approach of injecting variables
	// into the global object because: (a) closures actually work, (b) `this`
	// is correct without wrapping, (c) prototype methods are available,
	// (d) no global pollution, (e) lexical bindings work correctly.

	// ── Await support in debug console ─────────────────────────────────
	// If the expression contains `await`, strip it and evaluate the inner
	// expression directly. The function call will return a Promise; we then
	// poll-wait for the Promise to settle (Go-backed k6 functions resolve
	// promises via goroutines that call RegisterCallback → event loop).
	// After it settles, unwrapPromiseResult extracts the resolved value.
	// This matches Chrome DevTools / Node.js behavior where `await fetch(...)`
	// works in the console.
	containsAwait := containsAwaitKeyword(expr)
	if containsAwait {
		expr = stripAwaitKeyword(expr)
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] evaluateComplexExpression: stripped await, evaluating: %q\n", expr)
		}
	}

	// Determine inGlobal: mirror runtime.eval()'s logic for direct eval.
	// If there's any variable stash between the current scope and global,
	// we're NOT in global scope.
	inGlobal := true
	for s := dbg.vm.stash; s != nil; s = s.outer {
		if s.isVariable() {
			inGlobal = false
			break
		}
	}

	// Determine strict mode from the current execution context.
	// ESM modules (k6 TypeScript via esbuild) are always strict.
	inStrict := dbg.isCurrentScopeStrict()

	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] evaluateComplexExpression: compiling %q (inGlobal=%v, strict=%v)\n", expr, inGlobal, inStrict)
	}

	// ── Inject 'this' into the stash chain ────────────────────────────────
	//
	// When the compiler compiles eval code, it emits getThisDynamic{} for
	// 'this' references. getThisDynamic walks the stash chain looking for
	// thisBindingName (" this"). But if the enclosing function was compiled
	// without knowing an eval() would happen, 'this' may still be on the
	// stack (vm.stack[vm.sb]) instead of in any stash.
	//
	// Fix: create a temporary wrapper stash containing the correct 'this'
	// value. This stash wraps the current stash chain so getThisDynamic
	// finds it immediately. We set vm.stash to this wrapper BEFORE
	// compilation (so the compiler accounts for the extra scope level in
	// its stash walking at compiler.go:1761) and BEFORE execution.
	// After execution, we restore the original stash.
	//
	// This is safe because:
	//   - loadDynamic/getThisDynamic search by name → will find " this"
	//   - Other name lookups skip this stash (they search by name too)
	//   - The wrapper has funcType=funcNone so the compiler's funcType
	//     detection (line 1761-1766) walks past it correctly

	thisVal := dbg.getCurrentThis()

	// When paused on an exception, swap in the throw-site stash so eval
	// expressions can access variables from the scope where the error occurred.
	var preExceptionStash *stash
	if dbg.exceptionBreakActive && dbg.exceptionStash != nil {
		preExceptionStash = dbg.vm.stash
		dbg.vm.stash = dbg.exceptionStash
	}

	origStash := dbg.vm.stash

	// Only inject the wrapper if we actually have a valid 'this' to inject.
	// For top-level module code, 'this' is undefined and doesn't need injection.
	thisInjected := false
	if thisVal != nil && thisVal != _undefined {
		thisKey := unistring.String(thisBindingName)
		wrapperStash := &stash{
			values: []Value{thisVal},
			names:  map[unistring.String]uint32{thisKey: 0},
			outer:  origStash,
			vm:     dbg.vm,
			// funcType stays funcNone — the compiler's funcType detection
			// (line 1761) will walk past this to find the real function stash.
		}
		dbg.vm.stash = wrapperStash
		thisInjected = true
	}

	// Compile with dbg.vm as evalVm — this is the key difference from
	// the previous approach. The compiler emits loadDynamic/getThisDynamic
	// instructions that dynamically search the live stash chain at runtime,
	// exactly as eval(...) inside the paused function would.
	//
	// PERF: Check the eval cache first. When the IDE sends multiple evaluate
	// requests for the same expression during a single pause (e.g., inline
	// values / CodeLens updates), we can reuse the compiled program and skip
	// the full parse+compile cycle. The cache is cleared on each new pause.
	var prog *Program
	var compileErr error

	prog, compileErr = compile("<debugger-eval>", expr, inStrict, inGlobal, dbg.vm, dbg.vm.debugMode, dbg.vm.r.parserOptions...)
	if compileErr != nil {
		// Restore stash before returning on compile error.
		if thisInjected {
			dbg.vm.stash = origStash
		}
		if preExceptionStash != nil {
			dbg.vm.stash = preExceptionStash
		}
		return nil, fmt.Errorf("compilation error: %w", compileErr)
	}

	var result Value
	var evalErr error

	// Execute using the pushCtx/runTry/popCtx pattern (mirrors runtime.eval
	// for direct eval). We must NOT use RunProgram because it resets
	// vm.stash to global in recursive calls, wiping the scope chain
	// that the compiled program needs.
	func() {
		dbg.suppressDebugDepth++
		dbg.suppressDebugger = true
		defer func() {
			dbg.suppressDebugDepth--
			if dbg.suppressDebugDepth == 0 {
				dbg.suppressDebugger = false
			}
		}()
		defer func() {
			// Always restore the original stash, even on panic.
			if thisInjected {
				dbg.vm.stash = origStash
			}
			if preExceptionStash != nil {
				dbg.vm.stash = preExceptionStash
			}
		}()
		defer func() {
			if r := recover(); r != nil {
				if ex, ok := r.(*Exception); ok {
					evalErr = ex
				} else if ex, ok := r.(*StackOverflowError); ok {
					evalErr = fmt.Errorf("evaluation error: %s", ex.Error())
				} else {
					evalErr = fmt.Errorf("evaluation panicked: %v", r)
				}
				// Always log panics in eval (not just when enableDebugLogging)
				// to diagnose nil pointer dereferences
				buf := make([]byte, 4096)
				n := runtime.Stack(buf, false)
				if debugActivate {
					fmt.Printf("[DEBUGGER] evaluateComplexExpression: panicked: %v\nStack:\n%s\n", r, buf[:n])
				}
			}
		}()

		vm := dbg.vm

		// CRITICAL: Save vm.sp before eval. pushCtx does NOT save sp (only
		// prg, stash, privEnv, newTarget, result, pc, sb, args). If the eval
		// expression throws an exception, handleThrow resets vm.sp to the try
		// frame's saved value, and then "vm.sp -= 2" below could push sp below
		// the pre-eval value — corrupting the main program's stack. On resume,
		// instructions like concatStrings see a wrong sp and panic with
		// "slice bounds out of range".
		savedSP := vm.sp
		savedResult := vm.result

		// CRITICAL: Save the live stack values at and just below sp.
		// The eval's pushCtx/push(funcObj)/push(nil) writes into stack slots
		// starting at savedSP. If the eval's enterFunc/runTry modifies these
		// slots and an exception causes incomplete cleanup, the paused program
		// could read corrupted values when it resumes. Saving and restoring
		// the stack region guarantees the paused program's live data is intact.
		// We save up to 4 slots above sp as a safety margin for intermediate
		// values that might be live on the stack during a mid-expression pause.
		const stackGuardSlots = 4
		stackGuardEnd := savedSP + stackGuardSlots
		if stackGuardEnd > len(vm.stack) {
			stackGuardEnd = len(vm.stack)
		}
		var savedStackRegion []Value
		if stackGuardEnd > savedSP {
			savedStackRegion = make([]Value, stackGuardEnd-savedSP)
			copy(savedStackRegion, vm.stack[savedSP:stackGuardEnd])
		}

		// Save context — pushCtx saves prg, stash, pc, sb, args (NOT sp).
		vm.pushCtx()
		// CRITICAL: Defer the restore so it runs on ALL exit paths —
		// normal return, vmResuming early return, AND panics caught by
		// the recover defer above. Without this, an early return (e.g.,
		// vmResuming at line ~5736) skips popCtx + sp restore, leaving
		// the VM with a corrupted call stack and sp. On resume, getProp
		// or similar opcodes hit "index out of range" because sp points
		// past the stack.
		ctxPushed := true
		defer func() {
			if !ctxPushed {
				return
			}
			// Guard against popCtx panicking (empty callStack).
			func() {
				defer func() { recover() }()
				vm.popCtx()
			}()
			vm.sp = savedSP
			vm.result = savedResult
			if savedStackRegion != nil && savedSP+len(savedStackRegion) <= len(vm.stack) {
				copy(vm.stack[savedSP:savedSP+len(savedStackRegion)], savedStackRegion)
			}
		}()

		// Get the function object from the current frame (like runtime.eval direct mode)
		funcObj := Value(_undefined)
		if vm.sb > 0 && vm.sb-1 < len(vm.stack) {
			if v := vm.stack[vm.sb-1]; v != nil {
				funcObj = v
			}
		}

		// DO NOT reset vm.stash — keeping the current stash (with the
		// injected 'this' wrapper) is what makes this a "direct eval"
		// with full scope chain access.

		vm.prg = prog
		vm.pc = 0
		vm.args = 0
		vm.result = _undefined
		vm.push(funcObj)
		vm.sb = vm.sp
		vm.push(nil) // this slot — actual 'this' is resolved via stash chain
		ex := vm.runTry()
		retval := vm.result

		// Mark context as handled — the defer will still run but
		// we do the popCtx/restore here for the normal path so we
		// can capture retval correctly.
		ctxPushed = false

		// If the VM has resumed while we were running, do NOT use
		// the result — but sp/ctx are already restored by the defer.
		if dbg.vmResuming.Load() {
			evalErr = fmt.Errorf("evaluation aborted: VM resumed")
			return
		}

		vm.popCtx()
		vm.sp = savedSP
		vm.result = savedResult

		if savedStackRegion != nil && savedSP+len(savedStackRegion) <= len(vm.stack) {
			copy(vm.stack[savedSP:savedSP+len(savedStackRegion)], savedStackRegion)
		}

		if ex != nil {
			evalErr = ex
		} else {
			result = retval
		}

		// ── Await support: poll for Promise settlement ────────────
		// When the user's expression contained `await` (now stripped),
		// the result is likely a Promise from a Go-backed k6 function.
		// The Go goroutine resolving it runs concurrently. We poll for
		// the Promise to settle, draining the job queue each iteration
		// to process promise reactions.
		if containsAwait && result != nil {
			result = dbg.waitForPromiseSettlement(vm.r, result)
		}
	}()

	if evalErr != nil {
		if exc, ok := evalErr.(*Exception); ok {
			return nil, exc
		}
		return nil, fmt.Errorf("evaluation error: %w", evalErr)
	}

	// Unwrap Promises: k6 functions often return Promises; the user wants
	// the resolved value, not a Promise wrapper.
	result = dbg.unwrapPromiseResult(result)

	return result, nil
}

// isCurrentScopeStrict returns true if the current VM scope is in strict mode.
// ESM modules compiled by k6 (via esbuild) are always strict.
func (dbg *Debugger) isCurrentScopeStrict() bool {
	if dbg.vm == nil || dbg.vm.stash == nil {
		return false
	}
	for s := dbg.vm.stash; s != nil; s = s.outer {
		if s.funcType == funcModule {
			return true
		}
	}
	return false
}

// containsAwaitKeyword returns true if the expression contains a top-level
// `await` keyword. It does a simple check for the word "await" preceded and
// followed by non-identifier characters (or string boundaries). This avoids
// false positives like variable names containing "await" (e.g., "awaiter").
func containsAwaitKeyword(expr string) bool {
	idx := 0
	for {
		pos := strings.Index(expr[idx:], "await")
		if pos < 0 {
			return false
		}
		pos += idx
		// Check that "await" is not part of a larger identifier
		if pos > 0 {
			ch := expr[pos-1]
			if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch == '_' || ch == '$' {
				idx = pos + 5
				continue
			}
		}
		end := pos + 5
		if end < len(expr) {
			ch := expr[end]
			if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch == '_' || ch == '$' {
				idx = end
				continue
			}
		}
		return true
	}
}

// stripAwaitKeyword removes all top-level `await` keywords from an expression.
// "await authorizeBtn.textContent()" → "authorizeBtn.textContent()"
// "await (await page.locator('x')).click()" → "(page.locator('x')).click()"
// This allows the debug console to evaluate async expressions by calling
// the function directly and then polling for the Promise to settle.
func stripAwaitKeyword(expr string) string {
	result := expr
	for {
		prev := result
		idx := 0
		var buf strings.Builder
		for {
			pos := strings.Index(result[idx:], "await")
			if pos < 0 {
				buf.WriteString(result[idx:])
				break
			}
			absPos := idx + pos
			// Check word boundaries
			isWord := true
			if absPos > 0 {
				ch := result[absPos-1]
				if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch == '_' || ch == '$' {
					isWord = false
				}
			}
			end := absPos + 5
			if isWord && end < len(result) {
				ch := result[end]
				if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch == '_' || ch == '$' {
					isWord = false
				}
			}
			if isWord {
				buf.WriteString(result[idx:absPos])
				// Skip "await" and any following whitespace
				idx = end
				for idx < len(result) && (result[idx] == ' ' || result[idx] == '\t') {
					idx++
				}
			} else {
				buf.WriteString(result[idx : end])
				idx = end
			}
		}
		result = buf.String()
		if result == prev {
			break
		}
	}
	return strings.TrimSpace(result)
}

// waitForPromiseSettlement polls a Promise value until it settles or times out.
// Used by the debug console to support `await expr` — the expression is evaluated
// without `await` (returning a Promise), then we poll for the Go goroutine that
// resolves it to complete. Between polls, we drain the runtime's job queue so
// promise reactions (resolve/reject callbacks) are processed.
//
// For non-Promise values, returns the value immediately.
// Timeout: 30 seconds (matching k6 browser default timeout).
func (dbg *Debugger) waitForPromiseSettlement(r *Runtime, val Value) Value {
	if val == nil {
		return val
	}
	obj, ok := val.(*Object)
	if !ok {
		return val
	}
	promise, ok := obj.self.(*Promise)
	if !ok {
		return val // not a Promise, return as-is
	}

	// Already settled?
	if promise.State() != PromiseStatePending {
		return val
	}

	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] waitForPromiseSettlement: polling for Promise to settle...\n")
	}

	// Poll with increasing backoff: 1ms, 2ms, 4ms, ..., up to 100ms
	// Total timeout: 30 seconds
	const maxWait = 30 * time.Second
	deadline := time.Now().Add(maxWait)
	sleepDuration := time.Millisecond

	for time.Now().Before(deadline) {
		// Step 1: Drain the host event loop (k6's event loop) to process
		// RegisterCallback entries that resolve/reject the Promise.
		if dbg.EventLoopDrainer != nil {
			dbg.EventLoopDrainer()
		}

		// Step 2: Drain sobek's job queue (promise reaction microtasks)
		for len(r.jobQueue) > 0 {
			jobs := r.jobQueue
			r.jobQueue = nil
			for _, job := range jobs {
				func() {
					defer func() { recover() }()
					job()
				}()
			}
		}

		// Check if the Promise settled
		if promise.State() != PromiseStatePending {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] waitForPromiseSettlement: Promise settled (state=%d)\n", promise.State())
			}
			return val
		}

		// Sleep before next poll
		time.Sleep(sleepDuration)
		if sleepDuration < 100*time.Millisecond {
			sleepDuration *= 2
		}
	}

	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] waitForPromiseSettlement: timeout after %v, Promise still pending\n", maxWait)
	}
	return val // return the still-pending Promise; unwrapPromiseResult will show "Promise <pending>"
}

// getCurrentThis returns the 'this' value for the current stack frame.
// Used by evaluateComplexExpression to inject 'this' into the stash chain
// so that getThisDynamic (emitted by the compiler for eval code) finds it.
//
// Resolution order:
//  1. Walk the stash chain for " this" (thisBindingName) — works for class
//     methods with closures, arrow functions with lexical this, etc.
//  2. Fall back to vm.stack[vm.sb] — works for regular function calls where
//     'this' is passed on the stack and never moved to a stash.
func (dbg *Debugger) getCurrentThis() Value {
	if dbg.vm == nil {
		return _undefined
	}
	// Try stash chain for " this" (thisBindingName) first.
	thisKey := unistring.String(thisBindingName)
	for s := dbg.vm.stash; s != nil; s = s.outer {
		if s.names == nil {
			continue
		}
		if idx, found := s.names[thisKey]; found {
			actualIdx := int(idx & uint32(maskIndex))
			if s.values != nil && actualIdx < len(s.values) {
				v := s.values[actualIdx]
				if v != nil && !isNullValue(v) {
					return v
				}
			}
		}
	}
	// Fallback: stack base (vm.sb) holds 'this' for regular function calls.
	if dbg.vm.sb >= 0 && dbg.vm.sb < len(dbg.vm.stack) {
		v := dbg.vm.stack[dbg.vm.sb]
		if v != nil && !isNullValue(v) {
			if _, isUnresolved := v.(valueUnresolved); !isUnresolved {
				return v
			}
		}
	}
	return _undefined
}

// unwrapPromiseResult checks if a Value is a fulfilled Promise and returns
// its resolved value. For rejected promises, returns _undefined. For
// pending promises or non-promise values, returns the value as-is.
func (dbg *Debugger) unwrapPromiseResult(val Value) Value {
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
		return promise.Result()
	case PromiseStateRejected:
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] Promise rejected: %v\n", promise.Result())
		}
		return _undefined
	default:
		// Pending — can't resolve synchronously, return as-is
		return val
	}
}

func (dbg *Debugger) captureReturnValue(varName string, value Value) {
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] Capturing return value for '%s': %v (type: %T)\n", varName, value, value)
	}
	currentLine := dbg.Line()
	filename := dbg.Filename()
	cacheKey := fmt.Sprintf("%s:%d:__return_%s", filename, currentLine, varName)
	if dbg.varValueCache == nil {
		dbg.varValueCache = make(map[string]Value)
	}
	dbg.varValueCache[cacheKey] = value
	dbg.varValueCacheLine = currentLine
	if varInfo := dbg.getSourceVarInfo(currentLine); varInfo != nil {
		if _, isLocal := varInfo.locals[varName]; isLocal {
			declLine := varInfo.declLines[varName]
			localCacheKey := fmt.Sprintf("%s:%d:%s", filename, declLine, varName)
			dbg.varValueCache[localCacheKey] = value
		}
	}
}

func (dbg *Debugger) debugVarLocations() []VarLocation {
	if dbg.vm.prg == nil {
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] debugVarLocations: prg is nil\n")
		}
		return nil
	}
	if dbg.vm.prg.debugSymbols == nil {
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] debugVarLocations: debugSymbols is nil for program %s (funcName=%s)\n",
				dbg.vm.prg.src.Name(), dbg.vm.prg.funcName)
		}
		return nil
	}
	varLocs := dbg.vm.prg.debugSymbols.LookupVarsAtPC(dbg.vm.pc)
	if len(varLocs) > 0 {
		return varLocs
	}
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] debugVarLocations: no symbols at PC %d for program %s (funcName=%s), ranges has %d entries\n",
			dbg.vm.pc, dbg.vm.prg.src.Name(), dbg.vm.prg.funcName, len(dbg.vm.prg.debugSymbols.ranges))
	}
	return nil
}

// withSuppressedDebugger saves/restores all VM and debugger state around fn().
// Used by resolveIndirectValue and safeCallGetter to prevent getter evaluation
// from corrupting step state when the user expands variables in the IDE.
// PERF: single implementation — eliminates the ~60-line duplication between
// resolveIndirectValue and safeCallGetter, and ensures both stay in sync when
// new fields are added to Debugger.
func (dbg *Debugger) withSuppressedDebugger(fn func() Value) (result Value) {
	if dbg.vm == nil {
		return nil
	}
	// CRITICAL: Only run getter evaluation when the debugger is paused.
	// If the VM is running (active=false), saving/restoring VM state races
	// with the executing goroutine and causes nil pointer panics or stack
	// corruption.
	if !dbg.active {
		return nil
	}
	// Track this operation so we can check vmResuming in the deferred restore.
	// If the VM resumes while we're running, we skip the restore to avoid
	// corrupting the VM's live state.
	dbg.evalWG.Add(1)
	defer dbg.evalWG.Done()
	// Double-check after Add — if vmResuming was set between the check and Add,
	// bail out immediately.
	if dbg.vmResuming.Load() {
		return nil
	}
	defer func() {
		if r := recover(); r != nil {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] withSuppressedDebugger: panicked: %v\n", r)
			}
			result = nil
		}
	}()

	savedPC := dbg.vm.pc
	savedSB := dbg.vm.sb
	savedSP := dbg.vm.sp
	savedArgs := dbg.vm.args
	savedPrg := dbg.vm.prg
	savedStash := dbg.vm.stash
	savedResult := dbg.vm.result
	savedCallStackLen := len(dbg.vm.callStack)
	savedStackLen := len(dbg.vm.stack)
	savedTryStackLen := len(dbg.vm.tryStack)

	// CRITICAL: Save the stack values at and around sp. Getter execution can
	// modify stack slots that contain the paused program's live intermediate
	// values (e.g., the result of loadStash before it's consumed by the next
	// instruction). Without this, intermittent corruption occurs when a hover
	// eval triggers a getter at a mid-expression pause point.
	stackGuardEnd := savedSP + 4
	if stackGuardEnd > savedStackLen {
		stackGuardEnd = savedStackLen
	}
	var savedStackValues []Value
	if stackGuardEnd > 0 {
		// Save values from 0..stackGuardEnd to protect all live values
		savedStackValues = make([]Value, stackGuardEnd)
		copy(savedStackValues, dbg.vm.stack[:stackGuardEnd])
	}

	savedNext := dbg.next
	savedStepIn := dbg.stepIn
	savedContinuing := dbg.continuing
	savedStepOverTargetDepth := dbg.stepOverTargetDepth
	savedStepOverOriginalTargetDepth := dbg.stepOverOriginalTargetDepth
	savedStepOverStartLine := dbg.stepOverStartLine
	savedStepInLastPC := dbg.stepInLastPC
	savedStepInStartLine := dbg.stepInStartLine
	savedSteppingFilename := dbg.steppingFilename
	savedActive := dbg.active
	savedLastBreakpoint := dbg.lastBreakpoint
	savedUserCommandIssued := dbg.userCommandIssued
	savedLifecycleTransition := dbg.lifecycleTransition

	dbg.suppressDebugDepth++
	dbg.suppressDebugger = true

	defer func() {
		dbg.suppressDebugDepth--
		if dbg.suppressDebugDepth == 0 {
			dbg.suppressDebugger = false
		}

		// If the VM has resumed (Next/Continue closed the channel while we
		// were running the getter), do NOT restore stale VM state — the VM
		// goroutine is already executing new instructions and restoring
		// old sp/pc/prg would corrupt the stack.
		if dbg.vmResuming.Load() {
			return
		}

		dbg.vm.pc = savedPC
		dbg.vm.sb = savedSB
		dbg.vm.sp = savedSP
		dbg.vm.args = savedArgs
		dbg.vm.prg = savedPrg
		dbg.vm.stash = savedStash
		dbg.vm.result = savedResult
		if len(dbg.vm.callStack) > savedCallStackLen {
			dbg.vm.callStack = dbg.vm.callStack[:savedCallStackLen]
		}
		// CRITICAL: Restore tryStack to prevent try frame leaks from getter
		// evaluation. If a getter pushed try frames (via vm.try or vm.runTry)
		// and an exception consumed them, or if extra frames were left behind,
		// truncate back to the saved length. This prevents the outer
		// runWrapped.try.popTryFrame from operating on a corrupted stack.
		//
		// IMPORTANT: Clamp to the SHORTER of saved vs current length.
		// When an external wrapper's handleThrow unwinds tryStack BEFORE
		// the recover fires, len(vm.tryStack) may already be less than
		// savedTryStackLen. Truncating to savedLen would panic with
		// "slice bounds out of range" (seen with tempo instrumentation).
		restoreTryLen := savedTryStackLen
		if restoreTryLen > len(dbg.vm.tryStack) {
			restoreTryLen = len(dbg.vm.tryStack)
		}
		if len(dbg.vm.tryStack) > restoreTryLen {
			dbg.vm.tryStack = dbg.vm.tryStack[:restoreTryLen]
		}
		if len(dbg.vm.stack) > savedStackLen {
			dbg.vm.stack = dbg.vm.stack[:savedStackLen]
		} else if len(dbg.vm.stack) < savedStackLen {
			for len(dbg.vm.stack) < savedStackLen {
				dbg.vm.stack = append(dbg.vm.stack, nil)
			}
		}

		dbg.next = savedNext
		dbg.stepIn = savedStepIn
		dbg.continuing = savedContinuing
		dbg.stepOverTargetDepth = savedStepOverTargetDepth
		dbg.stepOverOriginalTargetDepth = savedStepOverOriginalTargetDepth
		dbg.stepOverStartLine = savedStepOverStartLine
		dbg.stepInLastPC = savedStepInLastPC
		dbg.stepInStartLine = savedStepInStartLine
		dbg.steppingFilename = savedSteppingFilename
		dbg.active = savedActive
		dbg.lastBreakpoint = savedLastBreakpoint
		dbg.userCommandIssued = savedUserCommandIssued
		dbg.lifecycleTransition = savedLifecycleTransition

		// Also reset the prg caches since we restored vm.prg.
		dbg.cachedPrg = nil
		dbg.cachedLinePrg = nil
	}()

	result = fn()
	return result
}

// safeResolveIndirectValue resolves an indirect stash binding only when it is
// safe to do so. Go-backed functions (e.g. monkey-patched HTTP wrappers from
// tempo/tracing libraries) must NOT be called during variable snapshot because:
//   1. They may make real HTTP calls or access k6 internals invalid outside a
//      real VU iteration context → panic.
//   2. They push extra call frames / try frames that corrupt the saved VM state
//      in withSuppressedDebugger, causing slice-bounds panics on restore.
//   3. Their source position falls inside the jslib bundle, breaking line mapping.
//
// The heuristic: if the raw indirect value IS already a callable Go function
// (nativeFuncObject, boundFuncObject, Go reflect wrappers), skip resolution
// and return the raw value so the IDE shows "ƒ name()" rather than crashing.
// JS functions (arrow, regular, async) are safe — they are sobek-internal.
func (dbg *Debugger) safeResolveIndirectValue(name string, rawVal Value) Value {
	if rawVal == nil || dbg.vm == nil {
		return rawVal
	}

	// Fast path: check if the raw value wraps a Go-backed callable.
	if obj, ok := rawVal.(*Object); ok && obj.self != nil {
		switch obj.self.(type) {
		case *nativeFuncObject, *boundFuncObject:
			// Go-backed callable — do NOT invoke it.
			return rawVal
		}
	}

	return dbg.resolveIndirectValue(rawVal)
}

func (dbg *Debugger) resolveIndirectValue(rawVal Value) Value {
	if rawVal == nil || dbg.vm == nil {
		return rawVal
	}
	resolved := dbg.withSuppressedDebugger(func() Value {
		var f func(*vm) Value
		if err := dbg.vm.r.ExportTo(rawVal, &f); err == nil && f != nil {
			v := f(dbg.vm)
			if v != nil {
				return v
			}
			// Getter returned nil — the exported variable is uninitialized.
			// Return undefined instead of falling through to rawVal (the getter
			// function itself), which would leak into the display layer and be
			// suppressed as a "function" by the hover filter.
			return _undefined
		}
		return rawVal
	})
	if resolved == nil {
		return rawVal
	}
	return resolved
}

func (dbg *Debugger) safeCallGetter(getter func() Value) Value {
	if dbg.vm == nil {
		return nil
	}
	return dbg.withSuppressedDebugger(getter)
}

func (dbg *Debugger) getValueFromLocation(varLoc VarLocation) (Value, error) {
	if varLoc.InStash {
		// Look up the variable by NAME in the stash chain.
		//
		// We cannot rely on the compile-time stash level and index because:
		// 1. Block scopes (try/catch/for) create and destroy stashes at runtime.
		// 2. The debugger may break at a PC where a block stash has been popped
		//    (e.g., `return age < expiryMs` inside a try{} — the leaveBlock
		//    instruction pops the try stash BEFORE the return expression).
		// 3. The stash chain layout at runtime may differ from compile-time assumptions.
		//
		// By scanning the chain for the matching name, we always find the correct
		// value regardless of which stashes are currently alive.
		//
		// PERF: Convert varLoc.Name to unistring.String once, then compare using
		// the unistring key directly. This avoids calling n.String() (which allocates)
		// for every name in every stash level — O(N*M) allocations become O(1).
		targetName := unistring.String(varLoc.Name)
		isThis := strings.TrimSpace(varLoc.Name) == "this"
		for s := dbg.vm.stash; s != nil; s = s.outer {
			if s.names == nil {
				continue
			}
			idx, found := s.names[targetName]
			if !found {
				// Also try " this" (leading space) when looking for "this"
				if isThis && varLoc.Name == "this" {
					idx, found = s.names[" this"]
				}
				if !found {
					continue
				}
			}
			actualIdx := int(idx & uint32(maskIndex))
			if s.values != nil && actualIdx < len(s.values) {
				val := s.values[actualIdx]
				if val != nil && !isNullValue(val) {
					if (idx&maskIndirect) != 0 && !lifecycleFunctionKeys[varLoc.Name] {
						val = dbg.resolveIndirectValue(val)
					}
					return val, nil
				} else if dbg.vm.debugMode {
					// Variable exists in stash but is nil (const/let before
					// assignment, e.g. RHS threw). Show as undefined so
					// hover/variables panel displays it instead of nothing.
					if isThis {
						// skip — uninitialized this is not useful
					} else if isSimpleIdentifier(varLoc.Name) {
						return _undefined, nil
					}
				}
			}
			// Found the name but value is nil/undefined — variable exists but uninitialized
			return nil, fmt.Errorf("variable %s found but uninitialized", varLoc.Name)
		}
		// Variable name not found in any named stash — the block stash was
		// popped or the variable is genuinely unavailable at this point.
		return nil, fmt.Errorf("variable %s not found in stash chain", varLoc.Name)
	}
	// Stack-based variable
	stackIdx := varLoc.StackIdx
	if stackIdx < 0 {
		stackIdx = dbg.vm.sb + stackIdx
	} else {
		stackIdx = dbg.vm.sb + 1 + stackIdx
	}
	if stackIdx >= 0 && stackIdx < len(dbg.vm.stack) {
		val := dbg.vm.stack[stackIdx]
		if val != nil && !isNullValue(val) {
			return val, nil
		}
	}
	return nil, fmt.Errorf("variable not found")
}

func (dbg *Debugger) GetLocalVariables() (map[string]Value, error) {
	locals := make(map[string]Value, 16) // PERF: pre-allocate; will grow if needed

	// ── Exception break: use saved throw-site state ──────────────────────
	// When paused on an exception, handleThrow has already unwound vm.stash,
	// vm.sb, and vm.prg. The throw-site state was saved in exceptionStash/
	// exceptionSB/exceptionPrg. Use buildPausedVarSnapshot which already
	// handles this — it checks exceptionBreakActive and walks exceptionStash.
	// This matches how getValue/Evaluate works (which the user reports as
	// working), ensuring the Variables panel shows the same data as hover.
	if dbg.exceptionBreakActive && dbg.exceptionStash != nil {
		snap := dbg.buildPausedVarSnapshot()
		for k, v := range snap {
			if v != nil && isIdentifierLike(k) && !globalBuiltinKeys[k] && !globalUnsafeKeys[k] {
				locals[k] = v
			}
		}
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] GetLocalVariables: exception break — collected %d variables from snapshot\n", len(locals))
		}
		return locals, nil
	}

	if !dbg.active || dbg.vm.prg == nil {
		if dbg.vm.prg == nil {
			if debugVM {
				fmt.Printf("[DEBUGGER] GetLocalVariables: early return — active=%v, prg=nil\n", dbg.active)
			}
			return locals, nil
		}
		// active=false but prg is valid — allow access (ret transition)
	}

	if dbg.vm.sb < 0 {
		if debugVM {
			fmt.Printf("[DEBUGGER] GetLocalVariables: vm.sb=%d at PC=%d (function stash not yet pushed), returning empty locals\n", dbg.vm.sb, dbg.vm.pc)
		}
		return locals, nil
	}

	if dbg.vm.stash == nil {
		if debugVM {
			fmt.Printf("[DEBUGGER] GetLocalVariables: stash is nil at PC=%d, returning empty locals\n", dbg.vm.pc)
		}
		return locals, nil
	}

	if dbg.vm.debugMode && dbg.vm.prg.debugSymbols != nil {
		// Check if we're at module level (not inside any function).
		// Class constructors and methods may have empty funcName but they
		// ARE functions — they have a stash with parameter/this bindings.
		// Only skip if we're truly at the top-level module scope.
		// Check the ENTIRE stash chain — block scopes may have been popped
		// by leaveBlock but the function-level stash is still present.
		isModuleLevel := dbg.vm.prg.funcName == ""
		if isModuleLevel {
			for s := dbg.vm.stash; s != nil; s = s.outer {
				if s.names != nil && len(s.names) > 0 {
					isModuleLevel = false
					break
				}
				// Stop at function boundary — don't look into enclosing functions
				if s.funcType != 0 {
					break
				}
			}
		}
		if isModuleLevel {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] GetLocalVariables: at module-level code (funcName='', no stash names), returning empty locals (globals handled by GetGlobalVariables)\n")
			}
			return locals, nil
		}

		varLocs := dbg.debugVarLocations()
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] GetLocalVariables: using debug symbols, found %d variables at PC %d (funcName=%s)\n",
				len(varLocs), dbg.vm.pc, dbg.vm.prg.funcName)
		}

		for _, varLoc := range varLocs {
			// Handle " this" (leading space) — sobek stores class `this` with
			// a space prefix. Expose it as "this" so the user can inspect
			// class instance properties (this.service, this.envId, etc.).
			displayName := varLoc.Name
			if strings.TrimSpace(varLoc.Name) == "this" {
				displayName = "this"
			} else if !isIdentifierLike(varLoc.Name) {
				continue
			}
			// PERF: Skip if we already resolved this variable with a real value.
			// Overlapping PC ranges can include the same variable multiple times.
			if existing, exists := locals[displayName]; exists && existing != nil && existing != _undefined {
				continue
			}
			// Wrap in recovery — getValueFromLocation calls resolveIndirectValue
			// which executes getter functions that can panic/throw.
			func() {
				defer func() {
					if r := recover(); r != nil {
						if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] GetLocalVariables: getValueFromLocation panicked for '%s': %v\n", varLoc.Name, r)
						}
					}
				}()
				val, err := dbg.getValueFromLocation(varLoc)
				if err == nil && val != nil && !isNullValue(val) {
					locals[displayName] = val
				} else if err != nil && strings.Contains(err.Error(), "uninitialized") {
					// TDZ variable (let/const before assignment) — show as special string
					// so the IDE displays it rather than hiding it entirely.
					locals[displayName] = asciiString("(uninitialized)")
				} else if err == nil && val != nil && isJSNull(val) {
					// JavaScript null — show as null, not undefined
					locals[displayName] = _null
				} else if err == nil && (val == nil || isNullValue(val)) {
					// var hoisted as undefined, or let/const assigned undefined explicitly.
					// Show as undefined so the user knows the variable exists.
					// EXCEPT "this": in ESM modules (strict mode), `this` at the
					// top-level default function is always undefined — showing it
					// is pure noise. Mouse hover still resolves it via Evaluate.
					if displayName == "this" {
						return // skip — don't add undefined this to locals
					}
					locals[displayName] = _undefined
			} else if err != nil {
				// Variable has a debug symbol but could not be resolved from the
				// stash chain (e.g., block scope was popped, stash level mismatch,
				// or let binding in a nested scope). Record it as undefined so
				// the stash-chain fallback below can still find and fix its value.
				// EXCEPT "this": when the stash lookup fails, `this` is always
				// noise (ESM strict mode, top-level default, class constructor
				// before super()). Mouse hover still resolves it via Evaluate.
				if displayName == "this" {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] GetLocalVariables: skipping unresolvable 'this' (err: %v)\n", err)
					}
					return // skip — don't add unresolvable this to locals
				}
				if dbg.enableDebugLogging {
					fmt.Printf("[DEBUGGER] GetLocalVariables: getValueFromLocation error for '%s': %v — recording as undefined\n", varLoc.Name, err)
				}
				locals[displayName] = _undefined
			}
			}()
		}

		// Stash-chain fallback: debug symbols may miss variables when:
		//  - A catch parameter's PC range starts after the current PC.
		//  - let/const bindings in the function scope are shadowed by an
		//    inner block scope stash pushed at runtime (try/catch/for in
		//    debug mode). The debug-symbols loop above only checks
		//    debugVarLocations (keyed by PC in the current program), and
		//    getValueFromLocation walks the stash by name — but if the
		//    inner stash is the innermost and the variable lives in the
		//    function-scope stash (one level out), the old single-level
		//    scan missed it entirely.
		//
		// Fix: walk ALL stash levels inside the current function (up to
		// the module/global stash) and collect any named variable not
		// already in locals. For functions with default parameters, the
		// parameter environment is a separate stash OUTSIDE the function
		// body scope. We must continue past the first funcType boundary
		// to reach it, but stop at the module boundary (funcModule) or
		// after two function boundaries (to avoid leaking into enclosing
		// functions).
		{
			const maxFuncStashDepth = 10 // safety bound
			depth := 0
			funcBoundariesHit := 0
			for s := dbg.vm.stash; s != nil && depth < maxFuncStashDepth; s = s.outer {
				depth++
				if s.names == nil {
					if s.funcType != 0 {
						funcBoundariesHit++
						// Stop at module/global scope boundary
						if s.funcType == funcModule || funcBoundariesHit >= 2 {
							break
						}
					}
					continue
				}
				for name, idx := range s.names {
					// Map " this" (sobek internal name) to "this" for display.
					// Previously this was skipped entirely, making class instance
					// properties invisible in the Variables panel.
					nameStr := name.String()
					if name == unistring.String(thisBindingName) {
						nameStr = "this"
					}
					if !isIdentifierLike(nameStr) {
						continue
					}
					// Skip if we already have a REAL value (not undefined).
					// If the debug-symbols path set it to _undefined (e.g., because
					// the stash lookup failed), we want the fallback to overwrite it
					// with the actual value if the stash has it at this level.
					if existing, exists := locals[nameStr]; exists && existing != nil && !isNullValue(existing) {
						continue
					}
					if globalBuiltinKeys[nameStr] || globalUnsafeKeys[nameStr] {
						continue
					}
					if lifecycleFunctionKeys[nameStr] {
						continue
					}
					actualIdx := int(idx & uint32(maskIndex))
					isIndirect := (idx & maskIndirect) != 0
					if s.values != nil && actualIdx < len(s.values) {
						val := s.values[actualIdx]
						if isIndirect && val != nil {
							val = dbg.resolveIndirectValue(val)
						}
						if val != nil && !isNullValue(val) {
							locals[nameStr] = val
						} else if val == nil {
							// TDZ or not-yet-initialized — show as undefined
							// so the IDE displays the variable exists.
							locals[nameStr] = _undefined
						}
					}
				}
				// Track function scope boundaries. Stop at module/global
				// scope or after passing through 2 function boundaries
				// (body + params of the same function). This prevents
				// leaking variables from an enclosing function.
				if s.funcType != 0 {
					funcBoundariesHit++
					if s.funcType == funcModule || funcBoundariesHit >= 2 {
						break
					}
				}
			}
		}

		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] GetLocalVariables: collected %d function-local variables from debug symbols\n", len(locals))
		}

		// Ensure 'this' is in locals for class constructors/methods.
		// The stash names map may not include " this" (excluded by makeNamesMap
		// in production mode, or missing debug symbols). Resolve it explicitly
		// via getValue which checks both stash and stack[sb].
		if _, hasThis := locals["this"]; !hasThis {
			if thisVal, err := dbg.getValue("this"); err == nil && thisVal != nil && !isNullValue(thisVal) {
				if _, isUnresolved := thisVal.(valueUnresolved); !isUnresolved {
					locals["this"] = thisVal
				}
			}
		}

		// ── Snapshot enrichment ──────────────────────────────────────────
		// The debug-symbols path and stash-chain fallback above may miss
		// variables when:
		//   - The stash layout at runtime differs from compile-time
		//     assumptions (block scopes, try/catch pushed extra stashes).
		//   - Default parameters create a separate parameter scope that
		//     the funcType-bounded fallback doesn't reach.
		//   - The PC falls between two PCRange entries in the debug symbols.
		//
		// buildPausedVarSnapshot walks the ENTIRE stash chain (no funcType
		// boundary) and always finds these variables — that's why eval/hover
		// works while the Variables panel doesn't.
		//
		// Fix: merge in any snapshot variable whose NAME appears in the
		// debug symbols for this function. This scopes the enrichment to
		// function-local variables (params + body vars) and prevents
		// leaking module-level globals into the Local scope.
		func() {
			defer func() {
				if r := recover(); r != nil {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] GetLocalVariables: snapshot enrichment panicked: %v\n", r)
					}
				}
			}()
			// Build the set of variable names that debug symbols say are
			// local to this function. We already iterated varLocs above;
			// collect the names into a set for fast lookup.
			debugSymbolNames := make(map[string]bool, len(varLocs))
			for _, vl := range varLocs {
				dn := vl.Name
				if strings.TrimSpace(dn) == "this" {
					dn = "this"
				}
				debugSymbolNames[dn] = true
			}

			snap := dbg.buildPausedVarSnapshot()
			enriched := 0
			for name, val := range snap {
				// Only enrich variables that:
				// 1. Are in the debug symbols (function-scoped)
				// 2. Are missing from locals OR have a nil/_undefined value
				//    that the snapshot resolved to a real value
				if !debugSymbolNames[name] {
					continue
				}
				existing, exists := locals[name]
				if exists && existing != nil && existing != _undefined {
					continue // already have a real value
				}
				if val != nil && !isNullValue(val) {
					locals[name] = val
					enriched++
				}
			}
			if enriched > 0 && dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] GetLocalVariables: snapshot enrichment added %d variables\n", enriched)
			}
		}()

		// ── Source map name remapping ────────────────────────────────────
		// Remap generated names → original names so the IDE variables panel
		// shows what the user wrote in their TypeScript source.
		// Already inside if debugMode. Wrapped in recover for safety.
		func() {
			defer func() {
				if r := recover(); r != nil {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] GetLocalVariables: name remapping panicked: %v\n", r)
					}
				}
			}()
			genToOrig, _ := dbg.buildSourceMapNameMapping()
			if len(genToOrig) > 0 {
				for genName, origName := range genToOrig {
					if genName == origName {
						continue
					}
					if val, hasGen := locals[genName]; hasGen {
						if _, hasOrig := locals[origName]; !hasOrig {
							locals[origName] = val
							delete(locals, genName) // hide bundler-renamed variable
						}
					}
				}
			}
		}()

		// Expose $exception when paused on an exception — Node.js parity.
		if dbg.exceptionBreakActive && dbg.lastException != nil {
			locals["$exception"] = dbg.lastException
		}

		// ── Promise unwrapping ──────────────────────────────────────────
		// Unwrap settled Promises so the Variables panel shows resolved
		// values instead of opaque Promise objects (Node.js parity).
		func() {
			defer func() { recover() }()
			for k, v := range locals {
				if v != nil && IsPromise(v) {
					if unwrapped := UnwrapPromiseForDisplay(v); unwrapped != v {
						locals[k] = unwrapped
					}
				}
			}
		}()

		return locals, nil
	}

	if dbg.vm.stash != nil && dbg.vm.stash.names != nil {
		for name, idx := range dbg.vm.stash.names {
			nameStr := name.String()
			if !isIdentifierLike(nameStr) || nameStr == "" {
				continue
			}
			if _, exists := locals[nameStr]; exists {
				continue
			}
			if dbg.vm.stash.values != nil {
				actualIdx := idx & uint32(maskIndex)
				if int(actualIdx) < len(dbg.vm.stash.values) {
					val := dbg.vm.stash.values[actualIdx]
					if val != nil && !isNullValue(val) {
						if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] GetLocalVariables: captured %s from stash (idx=%d)\n",
								nameStr, actualIdx)
						}
						locals[nameStr] = val
					} else {
						// Variable exists in stash but is undefined — show it
						locals[nameStr] = _undefined
					}
				}
			}
		}
	}

	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] GetLocalVariables: collected %d variables (legacy mode)\n", len(locals))
	}

	// Expose $exception when paused on an exception — Node.js parity.
	if dbg.exceptionBreakActive && dbg.lastException != nil {
		locals["$exception"] = dbg.lastException
	}

	// ── Promise unwrapping (legacy path) ────────────────────────────────
	func() {
		defer func() { recover() }()
		for k, v := range locals {
			if v != nil && IsPromise(v) {
				if unwrapped := UnwrapPromiseForDisplay(v); unwrapped != v {
					locals[k] = unwrapped
				}
			}
		}
	}()

	return locals, nil
}

func (dbg *Debugger) CaptureGlobalNames() {
	if dbg.globalsCaptured {
		return
	}
	names := make(map[string]bool)
	for s := dbg.vm.stash; s != nil; s = s.outer {
		if s.names != nil {
			for name := range s.names {
				nameStr := name.String()
				if isIdentifierLike(nameStr) && nameStr != "" {
					if s.outer == nil && globalBuiltinKeys[nameStr] {
						continue
					}
					names[nameStr] = true
				}
			}
		}
	}
	if dbg.vm.r != nil {
		if globalObj := dbg.vm.r.globalObject; globalObj != nil {
			for _, keyStr := range safeStringKeys(globalObj) {
				if isIdentifierLike(keyStr) && keyStr != "" &&
					!globalBuiltinKeys[keyStr] && !globalUnsafeKeys[keyStr] {
					names[keyStr] = true
				}
			}
		}
	}
	dbg.cachedGlobalNames = names
	dbg.globalsCaptured = true
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] CaptureGlobalNames: captured %d global names\n", len(names))
	}
}

func (dbg *Debugger) GetGlobalVariables() map[string]Value {
	globals := make(map[string]Value)
	if dbg.vm == nil {
		return globals
	}

	// ── Exception break: use saved throw-site state ──────────────────────
	// When paused on an exception, vm.prg/vm.stash may be unwound.
	// Use exceptionStash to walk the stash chain from the throw site.
	if dbg.exceptionBreakActive && dbg.exceptionStash != nil {
		stashToWalk := dbg.exceptionStash
		prgToUse := dbg.exceptionPrg
		skipLevel0 := prgToUse != nil && prgToUse.funcName != ""
		stashLevel := 0
		for s := stashToWalk; s != nil; s = s.outer {
			if (stashLevel > 0 || !skipLevel0) && s.names != nil {
				for name, idx := range s.names {
					nameStr := name.String()
					if !isIdentifierLike(nameStr) || nameStr == "" {
						continue
					}
					if _, exists := globals[nameStr]; exists {
						continue
					}
					if s.outer == nil && globalBuiltinKeys[nameStr] {
						continue
					}
				actualIdx := idx & uint32(maskIndex)
				isIndirect := (idx & maskIndirect) != 0
				if int(actualIdx) >= 0 && int(actualIdx) < len(s.values) {
					val := s.values[actualIdx]
					if val != nil && !isNullValue(val) {
						if isIndirect && !lifecycleFunctionKeys[nameStr] {
							val = dbg.resolveIndirectValue(val)
						}
						globals[nameStr] = val
					}
				}
			}
		}
		stashLevel++
	}
	// Also check the global object
	if dbg.vm.r != nil {
		if globalObj := dbg.vm.r.globalObject; globalObj != nil {
			for _, keyStr := range safeStringKeys(globalObj) {
				if !isIdentifierLike(keyStr) || keyStr == "" {
					continue
				}
				if _, exists := globals[keyStr]; exists {
					continue
				}
				if globalBuiltinKeys[keyStr] || globalUnsafeKeys[keyStr] {
					continue
				}
				keyUniStr := unistring.String(keyStr)
				if v := safeGetGlobalProperty(globalObj, keyUniStr); v != nil && !isNullValue(v) {
					globals[keyStr] = v
				}
			}
		}
	}
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] GetGlobalVariables: exception break — collected %d global variables from exception stash\n", len(globals))
	}
	return globals
}

	if dbg.vm.prg == nil {
		return globals
	}
	if !dbg.globalsCaptured && !dbg.initPhase {
		dbg.CaptureGlobalNames()
	}

	skipLevel0 := dbg.vm.prg.funcName != ""
	stashLevel := 0
	for s := dbg.vm.stash; s != nil; s = s.outer {
		if (stashLevel > 0 || !skipLevel0) && s.names != nil {
			for name, idx := range s.names {
				nameStr := name.String()
				if !isIdentifierLike(nameStr) || nameStr == "" {
					continue
				}
				if _, exists := globals[nameStr]; exists {
					continue
				}
				if s.outer == nil && globalBuiltinKeys[nameStr] {
					continue
				}
				if dbg.globalsCaptured && !dbg.cachedGlobalNames[nameStr] {
					continue
				}
				actualIdx := idx & uint32(maskIndex)
				isIndirect := (idx & maskIndirect) != 0
				if int(actualIdx) >= 0 && int(actualIdx) < len(s.values) {
					val := s.values[actualIdx]
					if val != nil && !isNullValue(val) {
						if isIndirect && !lifecycleFunctionKeys[nameStr] {
							val = dbg.resolveIndirectValue(val)
						}
						if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] GetGlobalVariables: captured %s from stash level %d (idx=%d)\n",
								nameStr, stashLevel, actualIdx)
						}
						globals[nameStr] = val
					}
				}
			}
		}
		stashLevel++
	}

	if dbg.vm.r != nil {
		if globalObj := dbg.vm.r.globalObject; globalObj != nil {
			for _, keyStr := range safeStringKeys(globalObj) {
				if !isIdentifierLike(keyStr) || keyStr == "" {
					continue
				}
				if _, exists := globals[keyStr]; exists {
					continue
				}
				if globalBuiltinKeys[keyStr] || globalUnsafeKeys[keyStr] {
					continue
				}
				if dbg.globalsCaptured && !dbg.cachedGlobalNames[keyStr] {
					continue
				}
				keyUniStr := unistring.String(keyStr)
				if v := safeGetGlobalProperty(globalObj, keyUniStr); v != nil && !isNullValue(v) {
					globals[keyStr] = v
				}
			}
		}
	}

	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] GetGlobalVariables: collected %d global variables\n", len(globals))
	}
	return globals
}

func (dbg *Debugger) GetAllStashVariablesQuiet() map[string]Value {
	savedLogging := dbg.enableDebugLogging
	dbg.enableDebugLogging = false
	defer func() { dbg.enableDebugLogging = savedLogging }()
	return dbg.GetAllStashVariables()
}

func (dbg *Debugger) GetAllStashVariables() map[string]Value {
	// PERF: Return cached result if VM state hasn't changed (same PC + program = same pause point).
	// During a single debugger pause, the IDE's MultiScopeEval calls this 20+ times
	// (once per variable hover/expansion). Each uncached call scans 25 module instances
	// and iterates 400+ variables — caching reduces this to a single scan per pause.
	//
	// CRITICAL: The cache is naturally invalidated when the VM resumes because vm.pc
	// changes on the next instruction. No explicit invalidation needed.
	//
	// NOTE: This was a major source of IDE slowness — "loading variables" would take
	// 5-10 seconds because GetAllStashVariables was called 20+ times × 400 vars each.
	if dbg.vm != nil && dbg.allStashVarsCache != nil &&
		dbg.allStashVarsCachePC == dbg.vm.pc && dbg.allStashVarsCachePrg == dbg.vm.prg {
		return dbg.allStashVarsCache
	}

	vars := make(map[string]Value)
	if dbg.vm == nil {
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] GetAllStashVariables: vm is nil\n")
		}
		return vars
	}

	stashLevel := 0
	for s := dbg.vm.stash; s != nil; s = s.outer {
		dbg.extractStashVars(s, vars, stashLevel, "vm.stash")
		stashLevel++
	}

	if dbg.vm.r != nil {
		globalStashPtr := &dbg.vm.r.global.stash
		if globalStashPtr != nil {
			dbg.extractStashVars(globalStashPtr, vars, stashLevel, "global.stash")
			stashLevel++
		}
	}

	if dbg.vm.r != nil && dbg.vm.r.modules != nil {
		moduleCount := 0
		for _, mi := range dbg.vm.r.modules {
			if stmi, ok := mi.(*SourceTextModuleInstance); ok && stmi.exportGetters != nil {
				stmi.exportGettersMu.RLock()
				for name, getter := range stmi.exportGetters {
					if _, exists := vars[name]; exists {
						continue
					}
					if !isIdentifierLike(name) {
						continue
					}
					if lifecycleFunctionKeys[name] {
						continue
					}
					val := dbg.safeCallGetter(getter)
					if val != nil && !isNullValue(val) {
						vars[name] = val
						// Per-variable capture logging commented out to reduce noise.
						// Produces hundreds of lines per pause for large modules.
						// if dbg.enableDebugLogging {
						// 	fmt.Printf("[DEBUGGER] GetAllStashVariables: captured %s from module (getter)\n", name)
						// }
					}
				}
				stmi.exportGettersMu.RUnlock()
				moduleCount++
			}
		}
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] GetAllStashVariables: checked %d module instances\n", moduleCount)
		}
	}

	if dbg.vm.r != nil {
		if globalObj := dbg.vm.r.globalObject; globalObj != nil {
			for _, keyStr := range safeStringKeys(globalObj) {
				if !isIdentifierLike(keyStr) || keyStr == "" {
					continue
				}
				if _, exists := vars[keyStr]; exists {
					continue
				}
				if globalBuiltinKeys[keyStr] || globalUnsafeKeys[keyStr] {
					continue
				}
				keyUniStr := unistring.String(keyStr)
				if v := safeGetGlobalProperty(globalObj, keyUniStr); v != nil && !isNullValue(v) {
					vars[keyStr] = v
				}
			}
		}
	}

	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] GetAllStashVariables: found %d variables across %d stash sources\n",
			len(vars), stashLevel)
	}

	// Cache the result for subsequent calls at the same pause point
	if dbg.vm != nil {
		dbg.allStashVarsCache = vars
		dbg.allStashVarsCachePC = dbg.vm.pc
		dbg.allStashVarsCachePrg = dbg.vm.prg
	}

	return vars
}

func (dbg *Debugger) extractStashVars(s *stash, vars map[string]Value, level int, source string) {
	if s == nil {
		return
	}
	// namesCount/valuesCount only used by commented-out per-stash logging below.
	// if dbg.enableDebugLogging {
	// 	namesCount := 0
	// 	if s.names != nil { namesCount = len(s.names) }
	// 	valuesCount := 0
	// 	if s.values != nil { valuesCount = len(s.values) }
	// 	fmt.Printf("[DEBUGGER] GetAllStashVariables: %s level %d - names=%d, values=%d, hasObj=%v\n",
	// 		source, level, namesCount, valuesCount, s.obj != nil)
	// }

	if s.names != nil {
		for name, idx := range s.names {
			nameStr := name.String()
			if !isIdentifierLike(nameStr) {
				continue
			}
			if _, exists := vars[nameStr]; exists {
				continue
			}
			if globalBuiltinKeys[nameStr] {
				continue
			}
			actualIdx := idx & uint32(maskIndex)
			if int(actualIdx) >= 0 && int(actualIdx) < len(s.values) {
				val := s.values[actualIdx]
				if val != nil && !isNullValue(val) {
					if (idx&maskIndirect) != 0 && !lifecycleFunctionKeys[nameStr] {
						val = dbg.resolveIndirectValue(val)
					}
					vars[nameStr] = val
					// Per-variable stash capture logging commented out.
					// if dbg.enableDebugLogging {
					// 	fmt.Printf("[DEBUGGER] GetAllStashVariables: captured %s from %s (idx=%d)\n",
					// 		nameStr, source, actualIdx)
					// }
				}
			}
		}
	}

	if s.obj != nil {
		for _, keyStr := range safeStringKeys(s.obj) {
			if !isIdentifierLike(keyStr) {
				continue
			}
			if globalBuiltinKeys[keyStr] || globalUnsafeKeys[keyStr] {
				continue
			}
			if _, exists := vars[keyStr]; !exists {
				keyUniStr := unistring.String(keyStr)
				if v := safeGetGlobalProperty(s.obj, keyUniStr); v != nil {
					vars[keyStr] = v
				}
			}
		}
	}
}

func (dbg *Debugger) getValue(varName string) (val Value, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("error getting value: %v", r)
		}
	}()

	// CRITICAL: Only allow variable resolution when the debugger is paused.
	// If the VM is running (active=false), accessing vm.stash/sb/pc races with
	// the executing goroutine and can cause nil pointer panics, wrong values,
	// or stack corruption that kills the VU init.
	// EXCEPTION 1: When the VM just returned from a nested debug loop (e.g., _ret
	// at the end of a constructor), active may be briefly false while the outer
	// loop hasn't broken yet. Allow access if the VM appears to be in a stable
	// state (stash and prg are valid).
	// EXCEPTION 2: When paused on an exception, the VM state may be unwound
	// (prg=nil, stash=nil, sb<0) but the exception stash is still valid.
	// Allow access — buildPausedVarSnapshot handles this via exceptionStash.
	if dbg.exceptionBreakActive && dbg.exceptionStash != nil {
		// Skip all VM state checks — use the exception snapshot path below
		goto resolveVar
	}
	if !dbg.active {
		if dbg.vm.prg == nil || dbg.vm.stash == nil {
			return nil, fmt.Errorf("cannot access variables: VM is not paused")
		}
		// VM state looks valid — allow access despite active=false
	}

	{
	isLifecycleEntry := dbg.vm.sb < 0 && dbg.vm.pc == 0
	if dbg.vm.sb < 0 && !isLifecycleEntry {
		return nil, fmt.Errorf("cannot access variables during context transition (vm.sb=%d)", dbg.vm.sb)
	}
	if dbg.vm.stash == nil && !isLifecycleEntry {
		return nil, fmt.Errorf("variable '%s' not accessible (no execution context)", varName)
	}
	}

resolveVar:

	// FAST PATH: resolve "this" directly.
	// Try stash FIRST — " this" (with space) in the stash is more reliable
	// than stack[sb] because it works for arrow functions (lexical this
	// captured from enclosing scope) and avoids stale stack values.
	if varName == "this" {
		// PERF: Direct map lookup using the known key " this" (thisBindingName)
		// instead of iterating all names and calling n.String() + TrimSpace().
		thisKey := unistring.String(thisBindingName)
		stashDepth := 0
		startStash := dbg.vm.stash
		if dbg.exceptionBreakActive && dbg.exceptionStash != nil {
			startStash = dbg.exceptionStash
		}
		for s := startStash; s != nil; s = s.outer {
			if s.names == nil {
				stashDepth++
				continue
			}
			if idx, found := s.names[thisKey]; found {
				actualIdx := int(idx & uint32(maskIndex))
				if s.values != nil && actualIdx < len(s.values) {
					v := s.values[actualIdx]
					if debugVM {
						fmt.Printf("[DEBUGGER-THIS] Found ' this' in stash depth=%d, idx=%d, value=%v (nil=%v, isNull=%v)\n",
							stashDepth, actualIdx, v, v == nil, v != nil && isNullValue(v))
					}
					if v != nil && !isNullValue(v) {
						return v, nil
					}
				} else if debugVM {
					fmt.Printf("[DEBUGGER-THIS] Found ' this' key in stash depth=%d but values array too small (idx=%d, len=%d)\n",
						stashDepth, actualIdx, len(s.values))
				}
			}
			stashDepth++
		}
		// Fall back to stack frame base — works for regular methods
		if dbg.vm.sb >= 0 && dbg.vm.sb < len(dbg.vm.stack) {
			v := dbg.vm.stack[dbg.vm.sb]
			if debugVM {
				fmt.Printf("[DEBUGGER-THIS] Stash lookup failed, trying stack[sb=%d]: value=%v (nil=%v)\n",
					dbg.vm.sb, v, v == nil)
			}
			if v != nil && !isNullValue(v) {
				if _, isUnresolved := v.(valueUnresolved); !isUnresolved {
					return v, nil
				}
			}
		} else if debugVM {
			fmt.Printf("[DEBUGGER-THIS] Stash lookup failed, sb=%d out of range (stack len=%d)\n",
				dbg.vm.sb, len(dbg.vm.stack))
		}
		if debugVM {
			fmt.Printf("[DEBUGGER-THIS] 'this' NOT resolved — falling through to general lookup\n")
		}
	}

	if retVal, found := dbg.returnValueCache[varName]; found {
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] getValue('%s'): Found in return value cache\n", varName)
		}
		return retVal, nil
	}

	if scopeVars, hasScope := dbg.scopeVariables[dbg.currentScopeDepth]; hasScope {
		if val, found := scopeVars[varName]; found {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] getValue('%s'): Found in scope variables (depth=%d)\n", varName, dbg.currentScopeDepth)
			}
			return val, nil
		}
	}

	// Check the paused var snapshot BEFORE debug symbols. The snapshot walks
	// the full stash chain and correctly resolves variables from all scope
	// levels. The debug symbols path only stores stashIdx without a level,
	// so outer-scope variables (e.g. stepDefinitions in a for-of loop) get
	// incorrectly resolved from the innermost stash instead of their actual
	// stash depth.
	snap := dbg.buildPausedVarSnapshot()
	if snapVal, found := snap[varName]; found {
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] getValue('%s'): Found in paused var snapshot\n", varName)
		}
		return snapVal, nil
	}

	name := unistring.String(varName)

	if dbg.vm.prg != nil && dbg.vm.prg.debugSymbols != nil {
		varLocs := dbg.vm.prg.debugSymbols.LookupVarsAtPC(dbg.vm.pc)
		for _, varLoc := range varLocs {
			// Match by name. For "this", also match " this" (sobek stores
			// the class this-binding with a leading space).
			nameMatch := varLoc.Name == varName ||
				(varName == "this" && strings.TrimSpace(varLoc.Name) == "this")
			if nameMatch {
				// Use getValueFromLocation which does name-based stash lookup
				val, err := dbg.getValueFromLocation(varLoc)
				if err == nil && val != nil && !isNullValue(val) {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] getValue('%s'): Found via getValueFromLocation (from debug symbols)\n", varName)
					}
					return val, nil
				}
				// Variable exists but is nil/undefined (const/let before
				// assignment, e.g. RHS threw). Return _undefined so hover
				// shows the variable instead of nothing.
				if err == nil && dbg.vm.debugMode {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] getValue('%s'): Found via debug symbols but uninitialized, returning undefined\n", varName)
					}
					return _undefined, nil
				}
			}
		}
	}

	stashLevel := 0
	stashStart := dbg.vm.stash
	if dbg.exceptionBreakActive && dbg.exceptionStash != nil {
		stashStart = dbg.exceptionStash
	}
	for s := stashStart; s != nil; s = s.outer {
		if s.names != nil {
			if idx, exists := s.names[name]; exists {
				actualIdx := idx & uint32(maskIndex)
				isIndirect := (idx & maskIndirect) != 0

				if isIndirect {
					if int(actualIdx) >= 0 && int(actualIdx) < len(s.values) {
						val := s.values[actualIdx]
						if val != nil && !isNullValue(val) {
							if lifecycleFunctionKeys[varName] {
								return val, nil
							}
							resolved := dbg.resolveIndirectValue(val)
							if dbg.enableDebugLogging {
								fmt.Printf("[DEBUGGER] getValue('%s'): Found indirect in stash level %d, idx %d (resolved)\n", varName, stashLevel, actualIdx)
							}
							return resolved, nil
						}
					}
			} else {
				// Read from the stash where the name was found FIRST.
				if int(actualIdx) >= 0 && int(actualIdx) < len(s.values) {
					val := s.values[actualIdx]
					if val != nil && !isNullValue(val) {
						if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] getValue('%s'): Found non-indirect in stash level %d, idx %d\n", varName, stashLevel, actualIdx)
						}
						return val, nil
					}
				}
				// Value is nil in the current stash — check parent stashes
				// (e.g., closure variable shadowed by an uninitialized let/const).
				for parent := s.outer; parent != nil; parent = parent.outer {
					if parent.names != nil {
						if parentRawIdx, exists := parent.names[name]; exists {
							parentActualIdx := parentRawIdx & 0x00FFFFFF
							if int(parentActualIdx) < len(parent.values) {
								val := parent.values[parentActualIdx]
								if val != nil {
									if dbg.enableDebugLogging {
										fmt.Printf("[DEBUGGER] getValue('%s'): Found non-indirect in parent stash, idx=%d\n", varName, parentActualIdx)
									}
									return val, nil
								}
							}
						}
					}
					if parent.obj != nil {
						if !globalUnsafeKeys[varName] {
							if v := safeGetGlobalProperty(parent.obj, name); v != nil {
								if dbg.enableDebugLogging {
									fmt.Printf("[DEBUGGER] getValue('%s'): Found in parent object\n", varName)
								}
								return v, nil
							}
						}
					}
				}
			}
				// Variable name exists in stash but value is nil/undefined
				// (const/let before assignment, e.g. RHS threw an exception).
				// Return _undefined so hover/variables show it instead of nothing.
				if dbg.vm.debugMode {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] getValue('%s'): Found in stash level %d but uninitialized, returning undefined\n", varName, stashLevel)
					}
					return _undefined, nil
				}
			}
		}

		if s.obj != nil {
			if !globalUnsafeKeys[varName] {
				if v := safeGetGlobalProperty(s.obj, name); v != nil {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] getValue('%s'): Found in object properties\n", varName)
					}
					return v, nil
				}
			}
		}
		stashLevel++
	}

	if dbg.vm.r != nil {
		globalStash := &dbg.vm.r.global.stash
		if globalStash != nil && globalStash.names != nil {
			if idx, exists := globalStash.names[name]; exists {
				actualIdx := idx & uint32(maskIndex)
				if int(actualIdx) >= 0 && int(actualIdx) < len(globalStash.values) {
					val := globalStash.values[actualIdx]
					if val != nil && !isNullValue(val) {
						if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] getValue('%s'): Found in global stash, idx=%d\n", varName, actualIdx)
						}
						return val, nil
					}
				}
			}
		}
	}

	if dbg.vm.r != nil && dbg.vm.r.modules != nil {
		for _, mi := range dbg.vm.r.modules {
			if stmi, ok := mi.(*SourceTextModuleInstance); ok && stmi.exportGetters != nil {
				stmi.exportGettersMu.RLock()
				getter, exists := stmi.exportGetters[varName]
				stmi.exportGettersMu.RUnlock()
				if exists {
					func() {
						defer func() {
							if r := recover(); r != nil {
								if dbg.enableDebugLogging {
									fmt.Printf("[DEBUGGER] getValue('%s'): module export getter panicked: %v\n", varName, r)
								}
							}
						}()
						v := getter()
						if v != nil && !isNullValue(v) {
							if dbg.enableDebugLogging {
								fmt.Printf("[DEBUGGER] getValue('%s'): Found via module export getter\n", varName)
							}
							val = v
						}
					}()
					if val != nil {
						return val, nil
					}
				}
			}
		}
	}

	if dbg.vm.r != nil && !globalUnsafeKeys[varName] {
		if globalObj := dbg.vm.r.globalObject; globalObj != nil {
			if v := safeGetGlobalProperty(globalObj, name); v != nil {
				if dbg.enableDebugLogging {
					fmt.Printf("[DEBUGGER] getValue('%s'): Found in global object\n", varName)
				}
				return v, nil
			}
		}
	}

	currentLine := dbg.Line()
	if varInfo := dbg.getSourceVarInfo(currentLine); varInfo != nil {
		if paramIdx, isParam := varInfo.params[varName]; isParam {
			pIdx := -(paramIdx + 1)
			stackPos := dbg.vm.sb + 1 + pIdx
			if stackPos >= dbg.vm.sb && stackPos < dbg.vm.sp && stackPos < len(dbg.vm.stack) {
				val := dbg.vm.stack[stackPos]
				if val != nil && !isNullValue(val) && !isFunctionValue(val) {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] getValue('%s'): Found as parameter at stack pos %d (fallback)\n", varName, stackPos)
					}
					return val, nil
				}
			}
		}
		if localIdx, isLocal := varInfo.locals[varName]; isLocal {
			declLine := varInfo.declLines[varName]
			if declLine <= currentLine {
				stackPos := dbg.vm.sb + 2 + localIdx
				if stackPos >= dbg.vm.sb && stackPos < dbg.vm.sp && stackPos < len(dbg.vm.stack) {
					val := dbg.vm.stack[stackPos]
					if val != nil && !isNullValue(val) && !isFunctionValue(val) {
						if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] getValue('%s'): Found as local at stack pos %d (fallback)\n", varName, stackPos)
						}
						return val, nil
					}
				}
			}
		}
	}

	if registry := GetGlobalRegistry(); registry != nil {
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] getValue('%s'): Trying global registry for cross-phase lookup\n", varName)
		}
		func() {
			defer func() {
				if r := recover(); r != nil {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] getValue('%s'): Registry lookup panicked: %v\n", varName, r)
					}
				}
			}()
			result, regErr := registry.MultiScopeEval(dbg.vm.r, varName)
			if regErr == nil && result != nil && !isNullValue(result) {
				if dbg.enableDebugLogging {
					fmt.Printf("[DEBUGGER] getValue('%s'): Found via global registry\n", varName)
				}
				val = result
				err = nil
			}
		}()
		if err == nil && val != nil {
			return val, nil
		}
	}

	// ── Source map name resolution (Node.js / Chrome DevTools parity) ──
	// If the variable wasn't found under its original name, the bundler may
	// have renamed it (e.g., "test" → "test2" due to import collision).
	// Use the source map to find the generated name and retry the lookup.
	// Only in debug mode — no runtime impact.
	if dbg.vm.debugMode {
		if genName := dbg.resolveOriginalName(varName); genName != "" {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] getValue('%s'): Source map rename detected → trying generated name '%s'\n", varName, genName)
			}
			// Try the paused var snapshot with the generated name.
			if snap := dbg.buildPausedVarSnapshot(); snap != nil {
				if snapVal, found := snap[genName]; found {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] getValue('%s'): Found via source map rename '%s' in snapshot\n", varName, genName)
					}
					return snapVal, nil
				}
			}
			// Try debug symbols with the generated name.
			if dbg.vm.prg != nil && dbg.vm.prg.debugSymbols != nil {
				genNameUni := unistring.String(genName)
				varLocs := dbg.vm.prg.debugSymbols.LookupVarsAtPC(dbg.vm.pc)
				for _, varLoc := range varLocs {
					if varLoc.Name == genName {
						v, e := dbg.getValueFromLocation(varLoc)
						if e == nil && v != nil && !isNullValue(v) {
							if dbg.enableDebugLogging {
								fmt.Printf("[DEBUGGER] getValue('%s'): Found via source map rename '%s' in debug symbols\n", varName, genName)
							}
							return v, nil
						}
					}
					_ = genNameUni // suppress unused warning
				}
			}
			// Try direct stash lookup with the generated name.
			genUni := unistring.String(genName)
			for s := dbg.vm.stash; s != nil; s = s.outer {
				if s.names == nil {
					continue
				}
				if idx, exists := s.names[genUni]; exists {
					actualIdx := idx & uint32(maskIndex)
					isIndirect := (idx & maskIndirect) != 0
					if int(actualIdx) < len(s.values) {
						v := s.values[actualIdx]
						if v != nil && !isNullValue(v) {
							if isIndirect && !lifecycleFunctionKeys[genName] {
								v = dbg.resolveIndirectValue(v)
							}
							if dbg.enableDebugLogging {
								fmt.Printf("[DEBUGGER] getValue('%s'): Found via source map rename '%s' in stash\n", varName, genName)
							}
							return v, nil
						}
					}
				}
			}
		}
	}

	return nil, fmt.Errorf("variable '%s' not found in any scope", varName)
}

// isNullValue returns true for nil, undefined, and null sobek values.
func isNullValue(v Value) bool {
	if v == nil {
		return true
	}
	if v == _undefined {
		return true
	}
	if IsUndefined(v) {
		return true
	}
	return false
}

// isJSNull returns true if v is JavaScript null (not undefined, not Go nil).
// Use this when you need to specifically detect JS null for display purposes.
func isJSNull(v Value) bool {
	return v == _null || IsNull(v)
}

// isFunctionValue returns true if v is a callable JS function.
func isFunctionValue(v Value) bool {
	if v == nil {
		return false
	}
	_, isFn := AssertFunction(v)
	return isFn
}

// SetVariable sets a variable's value in the current scope.
// Tries local scope first, then walks up to global scope.
// Used by the DAP setVariable request to modify variables from the IDE.
func (dbg *Debugger) SetVariable(name string, val Value) error {
	vm := dbg.vm
	if vm == nil {
		return fmt.Errorf("VM not available")
	}

	// Try setting in the current stash chain (locals first, then enclosing scopes)
	if vm.stash != nil {
		if dbg.setStashVariable(vm.stash, name, val) {
			return nil
		}
	}

	// Try setting as a global property
	rt := dbg.GetRuntime()
	if rt != nil {
		globalObj := rt.GlobalObject()
		if globalObj != nil {
			if prop := globalObj.self.getStr(unistring.NewFromString(name), nil); prop != nil {
				globalObj.self.setOwnStr(unistring.NewFromString(name), val, false)
				return nil
			}
		}
	}

	return fmt.Errorf("variable '%s' not found in any scope", name)
}

// setStashVariable walks the stash chain looking for a binding named `name`
// and sets it to val. Returns true if found and set.
func (dbg *Debugger) setStashVariable(s *stash, name string, val Value) bool {
	nameUni := unistring.NewFromString(name)
	for current := s; current != nil; current = current.outer {
		if current.names != nil {
			if idx, exists := current.names[nameUni]; exists {
				actualIdx := idx & uint32(maskIndex)
				if int(actualIdx) < len(current.values) {
					current.values[actualIdx] = val
					return true
				}
			}
		}
	}
	return false
}

// RequestPause requests the VM to pause at the next opportunity.
// Used by the DAP pause request to pause a running script.
func (dbg *Debugger) RequestPause() {
	dbg.mu.Lock()
	dbg.stepIn = true
	dbg.next = false
	dbg.continuing = false
	dbg.steppingFilename = "" // accept any file
	dbg.mu.Unlock()
}

// GetLastException returns the last exception message and stack trace.
// Used by the DAP exceptionInfo request.
func (dbg *Debugger) GetLastException() (message string, stack string) {
	vm := dbg.vm
	if vm == nil {
		return "", ""
	}
	if dbg.lastException != nil {
		if obj, ok := dbg.lastException.(*Object); ok {
			rt := dbg.GetRuntime()
			if rt != nil {
				if msgVal := obj.self.getStr(unistring.NewFromString("message"), nil); msgVal != nil {
					message = msgVal.String()
				}
				if stackVal := obj.self.getStr(unistring.NewFromString("stack"), nil); stackVal != nil {
					stack = stackVal.String()
				}
			}
			if message == "" {
				message = dbg.lastException.String()
			}
		} else {
			message = dbg.lastException.String()
		}
	}
	return message, stack
}

// SetExceptionBreakpoints configures which exception types cause the debugger to pause.
func (dbg *Debugger) SetExceptionBreakpoints(caught, uncaught bool) {
	dbg.mu.Lock()
	defer dbg.mu.Unlock()
	// Only log when values actually change — this is called on every DAP request
	// via getActiveDebugger(), so logging every call produces thousands of lines.
	changed := dbg.breakOnCaughtExceptions != caught || dbg.breakOnUncaughtExceptions != uncaught
	dbg.breakOnCaughtExceptions = caught
	dbg.breakOnUncaughtExceptions = uncaught
	if changed && dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] SetExceptionBreakpoints: caught=%v, uncaught=%v\n", caught, uncaught)
	}
}

// BreakOnException is called by the VM's handleThrow when an exception occurs.
// If the matching exception breakpoint is enabled, it pauses the VM.
//
// throwFile and throwLine provide the ORIGINAL throw location (captured before
// handleThrow unwinds the stack). If both are empty/zero, the method falls back
// to dbg.Filename()/dbg.Line() and then lastBreakpoint.
//
// Node.js debugger behaviour:
//   - With "All Exceptions" enabled → pause at the throw site for both caught and uncaught
//   - With "Uncaught Exceptions" only → pause only when no try/catch will handle it
//   - try/catch: the exception is paused at the throw line (NOT the catch handler)
//   - Variables pane shows all in-scope variables at the throw point
func (dbg *Debugger) BreakOnException(exceptionVal Value, caught bool, throwFile string, throwLine int) bool {
	if dbg == nil || dbg.vm == nil || !dbg.vm.debugMode || dbg.suppressDebugger {
		if debugActivate {
			fmt.Printf("[EXCEPTION-TRACE] BreakOnException: SKIPPED (nil=%v, vm=%v, debugMode=%v, suppress=%v)\n",
				dbg == nil, dbg != nil && dbg.vm == nil, dbg != nil && dbg.vm != nil && !dbg.vm.debugMode, dbg != nil && dbg.suppressDebugger)
		}
		return false
	}
	if dbg.inEvalContext {
		return false
	}
	if exceptionVal == nil {
		if debugActivate {
			fmt.Printf("[EXCEPTION-TRACE] BreakOnException: SKIPPED (exceptionVal is nil)\n")
		}
		return false
	}

	if debugActivate {
		fmt.Printf("[EXCEPTION-TRACE] BreakOnException CALLED: caught=%v, exception=%q, throwFile=%s, throwLine=%d, pendingAlreadySet=%v, exceptionWaitCh=%v, breakOnCaught=%v, breakOnUncaught=%v\n",
			caught, exceptionVal.String(), throwFile, throwLine, dbg.pendingUncaughtException != nil, dbg.exceptionWaitCh != nil, dbg.breakOnCaughtExceptions, dbg.breakOnUncaughtExceptions)
	}

	// ── Resolve the throw location ─────────────────────────────────────
	// Priority: 1) explicit throwFile/throwLine (caller captured before unwind)
	//           2) dbg.Filename()/Line() (may be wrong after stack unwind)
	//           3) lastBreakpoint (last known good user position)
	filename := throwFile
	line := throwLine
	if filename == "" || line <= 0 {
		filename = dbg.Filename()
		line = dbg.Line()
	}
	if filename == "" || line <= 0 {
		filename = dbg.lastBreakpoint.filename
		line = dbg.lastBreakpoint.line
		if debugActivate {
			fmt.Printf("[EXCEPTION-TRACE] BreakOnException: using lastBreakpoint fallback: %s:%d\n", filename, line)
		}
	}

	// Skip truly internal/native files — exception breakpoints must work in
	// ANY user file. This matches Node.js behaviour.
	if filename == "" || filename == "<native>" || filename == "<eval>" || filename == "<anonymous>" || filename == "<debugger-eval>" {
		if debugActivate {
			fmt.Printf("[EXCEPTION-TRACE] BreakOnException: SKIPPED internal file %q\n", filename)
		}
		return false
	}

	// ── Caught exceptions ──────────────────────────────────────────────
	if caught {
		if !dbg.breakOnCaughtExceptions {
			// Clear the pre-unwind stash saved by onThrowCaptureState so it
			// doesn't leak into a subsequent uncaught exception.
			dbg.exceptionStash = nil
			dbg.exceptionPrg = nil
			return false
		}

		dbg.lastException = exceptionVal
		dbg.exceptionBreakActive = true
		// Capture the stash chain at the throw site so that variable inspection
		// (hover, watch, debug console) can resolve locals even after handleThrow
		// unwinds vm.stash to the catch handler.
		// NOTE: Only set if onThrowCaptureState hasn't already saved the pre-unwind stash.
		if dbg.exceptionStash == nil {
			dbg.exceptionStash = dbg.vm.stash
		}

		if dbg.enableDebugLogging || debugActivate {
			fmt.Printf("[DEBUGGER] BreakOnException: caught exception=%q, pausing at throw site %s:%d\n",
				exceptionVal.String(), filename, line)
		}

		// Pause the VM at the THROW site — blocks until user issues Continue/Step in the IDE.
		// We pass false/false for step flags so activate() treats this as a fresh pause.
		dbg.activateWithStepState(ExceptionActivation, filename, line, false, false)

		dbg.exceptionBreakActive = false
		dbg.exceptionStash = nil
		dbg.exceptionPrg = nil
		return true
	}

	// ── Uncaught exceptions ────────────────────────────────────────────
	// Uncaught exceptions ALWAYS pause the debugger in debug mode.
	// An uncaught exception crashes the k6 iteration — the user must see it
	// regardless of the "Uncaught Exceptions" checkbox in the IDE.
	// This matches Node.js behaviour where uncaught exceptions always halt
	// execution and show the error. The breakOnUncaughtExceptions flag only
	// matters for the DAP "Uncaught Exceptions" filter visibility, but in k6
	// there is no recovery from an uncaught throw — the iteration is dead.

	// Guard: if pendingUncaughtException is already set, skip duplicate
	if dbg.pendingUncaughtException != nil {
		if debugActivate {
			fmt.Printf("[EXCEPTION-TRACE] BreakOnException: SKIPPED duplicate uncaught (pendingUncaughtException already set)\n")
		}
		return false
	}

	if debugActivate || debugContinue {
		fmt.Printf("[DEBUGGER] BreakOnException: VU=%d storing pending uncaught exception at %s:%d (next=%v, stepIn=%v, exception=%s)\n",
			dbg.vuID, filename, line, dbg.next, dbg.stepIn, exceptionVal.String())
	}

	dbg.lastException = exceptionVal
	// Capture the stash chain at the throw site so that when the pending
	// exception is delivered (and exceptionBreakActive is set), variable
	// inspection can still resolve locals from the throw context.
	// NOTE: Only set exceptionStash if onThrowCaptureState hasn't already
	// saved it (pre-unwind). By the time BreakOnException is called for
	// uncaught exceptions, handleThrow has already unwound vm.stash — the
	// pre-unwind stash saved in onThrowCaptureState is the correct one.
	if dbg.exceptionStash == nil {
		dbg.exceptionStash = dbg.vm.stash
	}
	dbg.pendingUncaughtException = &DebuggerActivation{
		Reason:        ExceptionActivation,
		Filename:      filename,
		Line:          line,
		Column:        dbg.Column(),
		Epoch:         globalDebugCoordinator.NextGlobalEpoch(),
		VUID:          dbg.vuID,
		ExceptionText: exceptionVal.String(),
	}
	dbg.exceptionWaitCh = make(chan struct{})

	if debugActivate {
		fmt.Printf("[EXCEPTION-TRACE] BreakOnException: STORED pendingUncaughtException at %s:%d, exceptionWaitCh created\n",
			filename, line)
	}
	return false
}


// RecordHttpCall adds a completed HTTP call to the debug log.
// Called by the k6 HTTP module after each request completes.
// Thread-safe — can be called from any goroutine during execution.
func (dbg *Debugger) RecordHttpCall(record HttpCallRecord) {
	dbg.httpCallLogMu.Lock()
	dbg.httpCallLog = append(dbg.httpCallLog, record)
	dbg.httpCallLogMu.Unlock()
}

// DrainHttpCallLog returns all recorded HTTP calls since the last drain and clears the log.
// Called by the DAP server on each pause to send accumulated calls to the IDE.
func (dbg *Debugger) DrainHttpCallLog() []HttpCallRecord {
	dbg.httpCallLogMu.Lock()
	calls := dbg.httpCallLog
	dbg.httpCallLog = nil
	dbg.httpCallLogMu.Unlock()
	return calls
}

// IsExceptionBreak returns true if the debugger is currently paused due to an exception.
func (dbg *Debugger) IsExceptionBreak() bool {
	return dbg.exceptionBreakActive
}

// SuppressDebuggerFlag sets/clears the suppressDebugger flag.
// When true, vm.debug() is a no-op — breakpoints, stepping, and exception
// breaks are all skipped. Used by the DAP layer during property enumeration
// (obj.Get(), obj.Keys()) to prevent re-entering the debugger from JS getters.
func (dbg *Debugger) SuppressDebuggerFlag(suppress bool) {
	if suppress {
		dbg.suppressDebugDepth++
		dbg.suppressDebugger = true
	} else {
		if dbg.suppressDebugDepth > 0 {
			dbg.suppressDebugDepth--
		}
		if dbg.suppressDebugDepth == 0 {
			dbg.suppressDebugger = false
		}
	}
}
