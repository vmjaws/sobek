package sobek

import (
	"bufio"
	"errors"
	"fmt"
	"os"
	"sort"
	"strings"
	"sync"
	"time"
	"unicode"

	"github.com/grafana/sobek/unistring"
)

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

func init() {
	if debugAll {
		debugActivate = true
		debugGlobalStep = true
		debugInit = true
		debugBreakpoint = true
		debugBP = true
		debugContinue = true
		debugVM = true
		debugCompiler = true
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

	pendingLifecycleStepIn bool
	waitForFunctionEntry   bool
	globalActivationEpoch  uint64
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
	globalDebugCoordinator.activationCh = make(chan chan DebuggerActivation, 1)
	globalDebugCoordinator.isInitialized = true
	globalDebugCoordinator.hasConnection = false
	globalDebugCoordinator.activeDbg = nil
	globalDebugCoordinator.globalStepNext = false
	globalDebugCoordinator.globalStepIn = false
	globalDebugCoordinator.globalSteppingFile = ""
	globalDebugCoordinator.globalStepTargetDepth = 0
	globalDebugCoordinator.pendingLifecycleStepIn = false
	globalDebugCoordinator.waitForFunctionEntry = false
	globalDebugCoordinator.globalActivationEpoch = 0
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
	globalDebugCoordinator.activationCh = make(chan chan DebuggerActivation, 1)
	globalDebugCoordinator.isInitialized = true
	globalDebugCoordinator.hasConnection = false
	globalDebugCoordinator.activeDbg = nil
	globalDebugCoordinator.globalStepNext = false
	globalDebugCoordinator.globalStepIn = false
	globalDebugCoordinator.globalSteppingFile = ""
	globalDebugCoordinator.globalStepTargetDepth = 0
	globalDebugCoordinator.pendingLifecycleStepIn = false
	globalDebugCoordinator.waitForFunctionEntry = false
	globalDebugCoordinator.globalActivationEpoch = 0
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
}

func (gdc *GlobalDebugCoordinator) HasGlobalStepState() bool {
	gdc.mu.RLock()
	defer gdc.mu.RUnlock()
	return gdc.globalStepNext || gdc.globalStepIn
}

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
	watchExprCounter   int
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

// GlobalBreakpointRegistry holds breakpoints shared across all debugger instances.
type GlobalBreakpointRegistry struct {
	mu            sync.RWMutex
	breakpoints   map[string][]int // normalized filename -> sorted line numbers
	breakpointIDs map[bpKey]int    // PERF: struct key avoids string alloc on lookup
	nextID        int
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
	git.mu.Lock()
	defer git.mu.Unlock()
	normalizedFilename := normalizeFilename(filename)

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

func (git *GlobalInitTracker) HasAnyInitCompleted() bool {
	git.mu.RLock()
	defer git.mu.RUnlock()
	return len(git.initCompleted) > 0
}

func (git *GlobalInitTracker) Reset() {
	git.mu.Lock()
	defer git.mu.Unlock()
	git.initCompleted = make(map[string]bool)
	git.initBreakpointSet = make(map[initBPKey]bool)
	git.initBreakpointsByFile = make(map[string]map[int]bool)
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
		return nil
	}

	return errors.New("breakpoint doesn't exist")
}

// HasBreakpoint checks for a breakpoint. Caller must pass a normalized filename.
// PERF: no string allocation, no normalization, just a lock + binary search.
// No defer — manual unlock is measurably faster in tight hot paths.
func (gbr *GlobalBreakpointRegistry) HasBreakpoint(normalizedFilename string, line int) bool {
	gbr.mu.RLock()
	lines := gbr.breakpoints[normalizedFilename]
	idx := sort.SearchInts(lines, line)
	found := idx < len(lines) && lines[idx] == line
	gbr.mu.RUnlock()
	return found
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

func (gbr *GlobalBreakpointRegistry) Count() int {
	gbr.mu.RLock()
	defer gbr.mu.RUnlock()
	return len(gbr.breakpoints)
}

func GetGlobalBreakpoints() *GlobalBreakpointRegistry {
	return globalBreakpoints
}

type Debugger struct {
	vm *vm

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
	next                bool
	stepIn              bool
	continuing          bool
	stepOverTargetDepth int
	stepOverStartLine   int
	steppingFilename    string
	enableDebugLogging  bool
	skipPhaseEntryBreak bool
	lifecycleTransition bool
	userCommandIssued   bool
	configuredCh        chan struct{}
	waitingForConfig    bool
	evalMutex           sync.Mutex
	hasConnection       bool

	initPhase    bool
	initFilename string

	watchExpressions []watchExpr

	// --- PERF: hot-path caches ---

	// cachedPrg is the last vm.prg pointer we computed filename/normFilename for.
	// When vm.prg == cachedPrg we skip all string work in breakpoint().
	cachedPrg      *Program
	cachedFilename string // raw src.Name()
	cachedNormFile string // normalizeFilename(cachedFilename), slice of cachedFilename or equal

	// PERF: Line() cache — avoids expensive src.Position(sourceOffset(pc)) on every instruction.
	// Invalidated when prg changes (in refreshFilenameCache) or when cachedPC != vm.pc.
	cachedPC   int
	cachedLine int

	// initComplete is a local monotonic copy of globalInitTracker.HasAnyInitCompleted().
	// It is only ever flipped from false→true, never backwards, so once true we stop
	// asking the global tracker entirely (eliminating an RLock per instruction).
	initComplete bool

	// hasLocalBPs / hasGlobalBPs are set/cleared by SetBreakpoint/ClearBreakpoint.
	// When both are false, breakpoint() returns immediately with no lock acquisitions.
	hasLocalBPs  bool
	hasGlobalBPs bool

	// pausedVarSnapshot is built lazily on the first eval call per pause and reused
	// for all subsequent evals during the same pause (e.g. multiple variable hovers).
	// Cleared by Continue()/Next()/StepIn() before resuming.
	pausedVarSnapshot     map[string]Value
	pausedVarSnapshotLine int

	// ---

	varDeclLines     map[string]int
	sourceVarCache   map[sourceVarCacheKey]*sourceVarInfo // PERF: composite key fixes correctness + re-enables cache
	globalVarCache   map[string]bool
	sourceCacheValid bool

	varValueCache     map[string]Value
	varValueCacheLine int

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

	pendingCh chan DebuggerActivation

	suppressDebugger bool
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
	}
	if debugActivate {
		if inheritConnection {
			fmt.Printf("[DEBUGGER] New debugger inherited global connection status: %v\n", inheritConnection)
		} else {
			fmt.Printf("[DEBUGGER] New debugger NOT inheriting connection (globalInitialized=%v, inheritConnection=%v)\n",
				globalInitialized, inheritConnection)
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
)

type DebuggerActivation struct {
	Reason   ActivationReason
	Filename string
	Line     int
	ID       int
	Epoch    uint64
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

// refreshFilenameCache updates the per-debugger filename caches when vm.prg changes.
// Called at the top of breakpoint() and Filename(). Cheap when prg hasn't changed.
func (dbg *Debugger) refreshFilenameCache() {
	if dbg.vm.prg == dbg.cachedPrg {
		return
	}
	dbg.cachedPrg = dbg.vm.prg
	dbg.cachedPC = -1 // invalidate Line() cache
	dbg.cachedLine = 0
	if dbg.vm.prg == nil || dbg.vm.prg.src == nil {
		dbg.cachedFilename = ""
		dbg.cachedNormFile = ""
		return
	}
	dbg.cachedFilename = dbg.vm.prg.src.Name()
	dbg.cachedNormFile = normalizeFilename(dbg.cachedFilename)
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
		fmt.Printf("[DEBUGGER-ACTIVATE-ENTRY] At %s:%d - savedStepIn=%v, savedNext=%v, savedLifecycleTransition=%v, reason=%v\n",
			filename, line, savedStepIn, savedNext, savedLifecycleTransition, reason)
	}

	if globalDebugCoordinator.IsInitialized() {
		globalDebugCoordinator.SetActiveDebugger(dbg)
	}

	dbg.active = true

	savedCallDepth := dbg.callStackDepth()

	epoch := globalDebugCoordinator.NextGlobalEpoch()

	var ch chan DebuggerActivation

	if debugActivate {
		fmt.Printf("[DEBUGGER-ACTIVATE] Waiting for Continue() at %s:%d (hasConnection=%v, lifecycleTransition=%v)\n",
			filename, line, dbg.HasConnection(), savedLifecycleTransition)
	}

	if savedLifecycleTransition {
		if debugActivate {
			fmt.Printf("[DEBUGGER-ACTIVATE] Lifecycle transition: waiting on both channels (preferring global coordinator)\n")
		}
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
					dbg.stepOverTargetDepth = localDepth
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
					dbg.stepOverTargetDepth = localDepth
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
			case <-time.After(5 * time.Second):
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
			}
		}
	} else {
		if debugActivate {
			fmt.Printf("[DEBUGGER-ACTIVATE] Non-lifecycle: waiting on both channels\n")
		}
		select {
		case ch = <-dbg.activationCh:
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Received from local channel (non-lifecycle)\n")
			}
			if !savedStepIn {
				globalNext, globalStepIn, globalSteppingFile, globalTargetDepth := globalDebugCoordinator.GetGlobalStepState()
				if globalNext || globalStepIn {
					if debugActivate {
						fmt.Printf("[DEBUGGER-ACTIVATE] Non-lifecycle local channel: applying global step state: next=%v, stepIn=%v, file=%s, targetDepth=%d\n",
							globalNext, globalStepIn, globalSteppingFile, globalTargetDepth)
					}
					dbg.next = globalNext
					dbg.stepIn = globalStepIn
					dbg.steppingFilename = globalSteppingFile
					localDepth := savedCallDepth
					if debugActivate {
						fmt.Printf("[DEBUGGER-ACTIVATE] ✅ Using LOCAL call depth=%d (global was=%d, line=%d)\n",
							localDepth, globalTargetDepth, line)
					}
					dbg.stepOverTargetDepth = localDepth
					dbg.stepOverStartLine = line
					dbg.userCommandIssued = true
					globalDebugCoordinator.ClearGlobalStepState()
				}
			} else if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Skipping global step state check (lifecycle stepIn entry, stale state from previous phase)\n")
			}
		case ch = <-globalDebugCoordinator.ActivationChannel():
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Received from global coordinator (non-lifecycle)\n")
			}
			if !savedStepIn {
				globalNext, globalStepIn, globalSteppingFile, globalTargetDepth := globalDebugCoordinator.GetGlobalStepState()
				if globalNext || globalStepIn {
					dbg.next = globalNext
					dbg.stepIn = globalStepIn
					dbg.steppingFilename = globalSteppingFile
					localDepth := savedCallDepth
					if debugActivate {
						fmt.Printf("[DEBUGGER-ACTIVATE] ✅ Using LOCAL call depth=%d (global was=%d, line=%d)\n",
							localDepth, globalTargetDepth, line)
					}
					dbg.stepOverTargetDepth = localDepth
					dbg.stepOverStartLine = line
					dbg.userCommandIssued = true
					if debugActivate {
						fmt.Printf("[DEBUGGER-ACTIVATE] Non-lifecycle global: applied global step state: next=%v, stepIn=%v, file=%s, targetDepth=%d (localDepth=%d)\n",
							globalNext, globalStepIn, globalSteppingFile, globalTargetDepth, localDepth)
					}
					globalDebugCoordinator.ClearGlobalStepState()
				}
			} else if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Skipping global step state check (lifecycle stepIn entry, stale state from previous phase)\n")
			}
		}
	}

	id := 0
	if debugActivate {
		channelWait := time.Since(activateStart)
		fmt.Printf("[DEBUGGER-ACTIVATE] Channel handshake completed in %dms at %s:%d\n",
			channelWait.Milliseconds(), filename, line)
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

	ch <- DebuggerActivation{
		Reason:   reason,
		Filename: filename,
		Line:     line,
		ID:       id,
		Epoch:    epoch,
	}
	<-ch

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
			dbg.stepOverTargetDepth = localDepth
			dbg.stepOverStartLine = line
			globalDebugCoordinator.ClearGlobalStepState()
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Applied user command from global state: next=%v, stepIn=%v, file=%s, globalDepth=%d, localDepth=%d, startLine=%d\n",
					globalNext, globalStepIn, globalSteppingFile, globalTargetDepth, localDepth, line)
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
		dbg.stepOverTargetDepth = savedCallDepth

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
			dbg.stepOverTargetDepth = savedCallDepth
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
			dbg.stepOverStartLine = line
			dbg.stepOverTargetDepth = savedCallDepth
			dbg.steppingFilename = filename
			if debugActivate {
				fmt.Printf("[DEBUGGER-ACTIVATE] Restored next=true, set stepOverStartLine=%d, targetDepth=%d\n", line, dbg.stepOverTargetDepth)
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
		fmt.Printf("[DEBUGGER-ACTIVATE] Total activate() time: %dms at %s:%d\n",
			totalActivate.Milliseconds(), filename, line)
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
	// Use select to check if the channel is already closed before closing.
	// A closed channel will immediately return on receive; an open one won't.
	select {
	case <-ch:
		// Channel was already closed (or had a buffered value drained — either
		// way, closing it again would panic). Do nothing.
		if debugContinue {
			fmt.Printf("[DEBUGGER-SAFE-CLOSE] Channel already closed, skipping\n")
		}
	default:
		close(ch)
	}
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
		fmt.Printf("[DEBUGGER-CONTINUE] Attempting to send continue signal (stepIn=%v, next=%v, lifecycleTransition=%v)\n",
			dbg.stepIn, dbg.next, dbg.lifecycleTransition)
	}

	// PERF: read global step state once at Continue() entry rather than re-reading
	// on every loop iteration. Re-read only after a timeout/transition.
	globalNext, globalStepIn, _, _ := globalDebugCoordinator.GetGlobalStepState()
	hasGlobalStepState := globalNext || globalStepIn

	localDead := dbg.vmExited
	if !localDead {
		select {
		case <-dbg.vmDoneCh:
			localDead = true
		default:
		}
	}
	if !localDead {
		activeDbg := globalDebugCoordinator.GetActiveDebugger()
		if activeDbg != nil {
			if activeDbg.vmExited {
				localDead = true
			} else if activeDbg != dbg {
				localDead = true
			}
		}
	}

	if debugContinue {
		fmt.Printf("[DEBUGGER-CONTINUE] Waiting for next activation: hasGlobalStepState=%v (globalNext=%v, globalStepIn=%v), localDead=%v\n",
			hasGlobalStepState, globalNext, globalStepIn, localDead)
	}

	// PERF: allocate timers once and Reset() on retry rather than creating a new
	// timer (and goroutine) on every loop iteration via time.After().
	retryTimer := time.NewTimer(200 * time.Millisecond)
	outerTimer := time.NewTimer(2 * time.Second)
	defer retryTimer.Stop()
	defer outerTimer.Stop()

	// stopTimer drains and resets a timer safely.
	stopTimer := func(t *time.Timer) {
		if !t.Stop() {
			select {
			case <-t.C:
			default:
			}
		}
	}

	waitForActivation := func(source string, skipVMDone bool) (DebuggerActivation, bool) {
		var waitStart time.Time
		if debugContinue {
			waitStart = time.Now()
		}

		stopTimer(retryTimer)
		retryTimer.Reset(200 * time.Millisecond)

		if skipVMDone {
			select {
			case activation := <-dbg.currentCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] Received activation from %s: %s:%d (wait=%dms, total=%dms)\n",
						source, activation.Filename, activation.Line,
						time.Since(waitStart).Milliseconds(), time.Since(continueStart).Milliseconds())
				}
				return activation, true
			case <-retryTimer.C:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] Retry timeout waiting for activation from %s (200ms, total=%dms)\n",
						source, time.Since(continueStart).Milliseconds())
				}
				return DebuggerActivation{}, false
			}
		}
		select {
		case activation := <-dbg.currentCh:
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] Received activation from %s: %s:%d (wait=%dms, total=%dms)\n",
					source, activation.Filename, activation.Line,
					time.Since(waitStart).Milliseconds(), time.Since(continueStart).Milliseconds())
			}
			return activation, true
		case <-dbg.vmDoneCh:
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] VM exited (vmDoneCh closed) while waiting on %s (%dms, total=%dms) - switching to global\n",
					source, time.Since(waitStart).Milliseconds(), time.Since(continueStart).Milliseconds())
			}
			select {
			case <-dbg.activationCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] Drained stale currentCh from local activation channel\n")
				}
			default:
			}
			return DebuggerActivation{}, false
		case <-retryTimer.C:
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] Retry timeout waiting for activation from %s (200ms, total=%dms)\n",
					source, time.Since(continueStart).Milliseconds())
			}
			select {
			case <-dbg.activationCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] Drained stale currentCh from local activation channel\n")
				}
			default:
			}
			return DebuggerActivation{}, false
		}
	}

	localTimedOut := localDead
	for {
		if localTimedOut {
			select {
			case <-globalDebugCoordinator.ActivationChannel():
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] Drained stale entry from global coordinator channel\n")
				}
			default:
			}
			globalDebugCoordinator.ActivationChannel() <- dbg.currentCh
			if debugContinue {
				fmt.Printf("[DEBUGGER-CONTINUE] Sent to global coordinator (local VM exited), waiting for activation\n")
			}
			if activation, ok := waitForActivation("global", true); ok {
				return activation
			}
			dbg.currentCh = make(chan DebuggerActivation)
		} else if hasGlobalStepState {
			stopTimer(outerTimer)
			outerTimer.Reset(2 * time.Second)
			select {
			case globalDebugCoordinator.ActivationChannel() <- dbg.currentCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] Sent to global coordinator (preferred due to global step state), waiting for activation\n")
				}
				if activation, ok := waitForActivation("global", false); ok {
					return activation
				}
				localTimedOut = true
				dbg.currentCh = make(chan DebuggerActivation)
				// re-read global state only after a transition
				globalNext, globalStepIn, _, _ = globalDebugCoordinator.GetGlobalStepState()
				hasGlobalStepState = globalNext || globalStepIn
			case dbg.activationCh <- dbg.currentCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] Sent to local channel (fallback), waiting for activation\n")
				}
				if activation, ok := waitForActivation("local", false); ok {
					return activation
				}
				localTimedOut = true
				dbg.currentCh = make(chan DebuggerActivation)
				globalNext, globalStepIn, _, _ = globalDebugCoordinator.GetGlobalStepState()
				hasGlobalStepState = globalNext || globalStepIn
			case <-dbg.vmDoneCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] VM exited (vmDoneCh) while waiting for receiver, switching to global-only\n")
				}
				localTimedOut = true
				globalNext, globalStepIn, _, _ = globalDebugCoordinator.GetGlobalStepState()
				hasGlobalStepState = globalNext || globalStepIn
			case <-outerTimer.C:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] ⚠️ Timeout waiting for receiver (hasGlobalStepState=%v), retrying...\n", hasGlobalStepState)
				}
				select {
				case <-dbg.vmDoneCh:
					localTimedOut = true
				default:
				}
				globalNext, globalStepIn, _, _ = globalDebugCoordinator.GetGlobalStepState()
				hasGlobalStepState = globalNext || globalStepIn
			}
		} else {
			stopTimer(outerTimer)
			outerTimer.Reset(2 * time.Second)
			select {
			case dbg.activationCh <- dbg.currentCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] Sent to local channel, waiting for activation\n")
				}
				if activation, ok := waitForActivation("local", false); ok {
					return activation
				}
				localTimedOut = true
				dbg.currentCh = make(chan DebuggerActivation)
				globalNext, globalStepIn, _, _ = globalDebugCoordinator.GetGlobalStepState()
				hasGlobalStepState = globalNext || globalStepIn
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] Local VM exited, switching to global-only mode (hasGlobalStepState=%v)\n", hasGlobalStepState)
				}
			case globalDebugCoordinator.ActivationChannel() <- dbg.currentCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] Sent to global coordinator, waiting for activation\n")
				}
				if activation, ok := waitForActivation("global", false); ok {
					return activation
				}
				dbg.currentCh = make(chan DebuggerActivation)
				globalNext, globalStepIn, _, _ = globalDebugCoordinator.GetGlobalStepState()
				hasGlobalStepState = globalNext || globalStepIn
			case <-dbg.vmDoneCh:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] VM exited (vmDoneCh) while waiting for receiver, switching to global-only\n")
				}
				localTimedOut = true
				globalNext, globalStepIn, _, _ = globalDebugCoordinator.GetGlobalStepState()
				hasGlobalStepState = globalNext || globalStepIn
			case <-outerTimer.C:
				if debugContinue {
					fmt.Printf("[DEBUGGER-CONTINUE] ⚠️ Timeout waiting for receiver (hasGlobalStepState=%v), checking global state...\n", hasGlobalStepState)
				}
				select {
				case <-dbg.vmDoneCh:
					localTimedOut = true
				default:
				}
				globalNext, globalStepIn, _, _ = globalDebugCoordinator.GetGlobalStepState()
				hasGlobalStepState = globalNext || globalStepIn
			}
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

func (dbg *Debugger) IsActive() bool {
	return dbg.active
}

// AddWatch registers a watch expression. Returns its ID.
func (dbg *Debugger) AddWatch(expression string) int {
	watchExprCounter++
	id := watchExprCounter
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

func (dbg *Debugger) GetActivationEpoch() uint64 {
	return globalDebugCoordinator.GetGlobalEpoch()
}

func (dbg *Debugger) Detach() {
	safeClose := func(ch chan DebuggerActivation) {
		if ch == nil {
			return
		}
		select {
		case <-ch:
			// Already closed
		default:
			close(ch)
		}
	}
	dbg.vm.debugger = nil
	dbg.vm.debugMode = false
	dbg.vm = nil
	dbg.active = false
	if dbg.pendingCh != nil {
		if dbg.pendingCh != dbg.currentCh {
			safeClose(dbg.pendingCh)
		}
		dbg.pendingCh = nil
	}
	if dbg.currentCh != nil {
		safeClose(dbg.currentCh)
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
	return
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

	if activeDbg != nil && activeDbg.vm != nil && activeDbg.vm.prg != nil {
		steppingFilename = activeDbg.Filename()
		targetDepth = activeDbg.lastBreakpoint.stackDepth
		startLine = activeDbg.Line()
		gotValidState = startLine >= 0 && steppingFilename != ""
		if debugContinue {
			fmt.Printf("[DEBUGGER-NEXT] Using active debugger state: file=%s, depth=%d, line=%d, valid=%v\n",
				steppingFilename, targetDepth, startLine, gotValidState)
		}
	}

	if !gotValidState && dbg.vm != nil && dbg.vm.prg != nil {
		steppingFilename = dbg.Filename()
		targetDepth = dbg.lastBreakpoint.stackDepth
		startLine = dbg.Line()
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
		dbg.stepOverStartLine = startLine
		dbg.steppingFilename = steppingFilename
	} else {
		dbg.stepOverTargetDepth = dbg.lastBreakpoint.stackDepth
		dbg.stepOverStartLine = 0
		dbg.steppingFilename = ""
		if debugContinue {
			fmt.Printf("[DEBUGGER-NEXT] ⚠️ No valid state, using safe defaults: targetDepth=%d, startLine=0\n",
				dbg.stepOverTargetDepth)
		}
	}

	if gotValidState {
		dbg.lastBreakpoint.pc = dbg.vm.pc
		dbg.lastBreakpoint.line = startLine
		dbg.lastBreakpoint.filename = steppingFilename
		dbg.lastBreakpoint.stackDepth = targetDepth
	}

	globalDebugCoordinator.SetGlobalStepState(true, false, steppingFilename, targetDepth)
	if debugContinue {
		fmt.Printf("[DEBUGGER-NEXT] After SetGlobalStepState: next=%v, stepIn=%v, steppingFilename=%s, targetDepth=%d\n",
			dbg.next, dbg.stepIn, steppingFilename, targetDepth)
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
	dbg.continuing = true
	dbg.userCommandIssued = true
	// Invalidate per-pause snapshot — we're resuming.
	dbg.pausedVarSnapshot = nil
	globalDebugCoordinator.ClearGlobalStepState()
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
	dbg.stepOverStartLine = 0
	dbg.steppingFilename = ""

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
	dbg.cachedPC = -1
	dbg.cachedLine = 0

	// VM exit state — reset for the new phase
	dbg.vmExited = false
	dbg.vmDoneCh = make(chan struct{})

	// Drain stale entries from the activation channel
	select {
	case <-dbg.activationCh:
	default:
	}
	dbg.pendingCh = nil
	dbg.currentCh = nil

	// NOTE: we intentionally do NOT touch:
	//   - initPhase / initFilename / initComplete  (init dedup must survive)
	//   - breakpoints / breakpointIDs / hasLocalBPs / hasGlobalBPs
	//   - hasConnection
	//   - initRuntime / setupData (may still be needed)
}

// ResetForNewRun clears all per-run step/phase state from a cached Debugger so it
// can be reused cleanly for a new k6 run without carrying over stale flags.
// It preserves the VM pointer, breakpoints, connection status, and channels.
func (dbg *Debugger) ResetForNewRun() {
	// Step / pause state
	dbg.next = false
	dbg.stepIn = false
	dbg.continuing = false
	dbg.lifecycleTransition = false
	dbg.userCommandIssued = false
	dbg.skipPhaseEntryBreak = false
	dbg.stepOverTargetDepth = 0
	dbg.stepOverStartLine = 0
	dbg.steppingFilename = ""

	// Breakpoint position cache
	dbg.lastBreakpoint.filename = ""
	dbg.lastBreakpoint.line = 0
	dbg.lastBreakpoint.pc = 0
	dbg.lastBreakpoint.stackDepth = 0
	dbg.lastDebugLine = -1
	dbg.lastLine = 0
	dbg.currentLine = 0

	// Init phase flags
	dbg.initPhase = false
	dbg.initFilename = ""
	dbg.initComplete = false

	// Conditional breakpoints
	dbg.conditionalBPs = nil

	// Variable / scope caches
	// PERF: set to nil instead of make() — nil map reads return zero value safely in Go.
	// Write paths lazy-init them when needed, avoiding allocations on reset.
	dbg.pausedVarSnapshot = nil
	dbg.pausedVarSnapshotLine = 0
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
	dbg.cachedPC = -1
	dbg.cachedLine = 0

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
	dbg.steppingFilename = ""
	dbg.lifecycleTransition = false
	dbg.pausedVarSnapshot = nil
	globalDebugCoordinator.ClearGlobalStepState()
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
	if dbg.vm.prg == nil || (!dbg.hasLocalBPs && !dbg.hasGlobalBPs) {
		return false
	}

	// PERF: skip all debugger work during getter evaluation (resolveIndirectValue/safeCallGetter).
	// Without this, variable inspection can trigger breakpoints and corrupt step state.
	if dbg.suppressDebugger {
		return false
	}

	// PERF: update cached filename only when prg changes (typically never mid-execution).
	dbg.refreshFilenameCache()
	normalizedFilename := dbg.cachedNormFile
	line := dbg.Line()

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
		globalInitTracker.mu.RLock()
		// FIXED: use composite key — normalizedFilename is already computed above
		hitGlobal := globalInitTracker.initBreakpointSet[initBPKey{normalizedFilename, line}]
		var hitFile bool
		if !hitGlobal {
			if fs := globalInitTracker.initBreakpointsByFile[normalizedFilename]; fs != nil {
				hitFile = fs[line]
			}
		}
		globalInitTracker.mu.RUnlock()
		if hitGlobal || hitFile {
			if debugInit {
				fmt.Printf("[BREAKPOINT-CHECK] Skipping init breakpoint at line %d in '%s' - already hit during init\n", line, normalizedFilename)
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
	if dbg.hasLocalBPs {
		dbg.breakpointMutex.RLock()
		lines := dbg.breakpoints[normalizedFilename]
		idx := sort.SearchInts(lines, line)
		found = idx < len(lines) && lines[idx] == line
		dbg.breakpointMutex.RUnlock()
	}

	// PERF: check global registry only if not found locally.
	// HasBreakpoint now takes an already-normalized filename — no alloc inside.
	if !found && dbg.hasGlobalBPs {
		found = globalBreakpoints.HasBreakpoint(normalizedFilename, line)
	}

	if found && dbg.initPhase {
		globalInitTracker.RecordInitBreakpoint(normalizedFilename, line)
	}

	if found && dbg.enableDebugLogging && isNewLine {
		willStop := true
		skipReason := ""
		if dbg.next {
			startLine := dbg.stepOverStartLine
			// PERF: inline callStackDepth — avoid function call overhead in hot path
			currentDepth := len(dbg.vm.callStack)
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
			fmt.Printf("[BREAKPOINT-CHECK] ✅✅ BREAKPOINT HIT at line %d in '%s' - will activate debugger\n", line, dbg.cachedFilename)
		} else {
			fmt.Printf("[BREAKPOINT-CHECK] ⚠️ BREAKPOINT at line %d in '%s' - WILL BE SKIPPED (%s)\n", line, dbg.cachedFilename, skipReason)
		}
	}

	return found
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
	source := dbg.vm.prg.src.Source()
	lines := strings.Split(source, "\n")
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
	if dbg.vm.pc == dbg.cachedPC && dbg.cachedLine != 0 {
		return dbg.cachedLine
	}
	dbg.cachedPC = dbg.vm.pc
	dbg.cachedLine = dbg.vm.prg.src.Position(dbg.vm.prg.sourceOffset(dbg.vm.pc)).Line
	return dbg.cachedLine
}

func (dbg *Debugger) Filename() string {
	dbg.refreshFilenameCache()
	return dbg.cachedFilename
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

	if activeDbg != nil && activeDbg.vm != nil && activeDbg.vm.prg != nil {
		steppingFilename = activeDbg.Filename()
		callDepth = activeDbg.lastBreakpoint.stackDepth
		startLine := activeDbg.Line()
		gotValidState = startLine >= 0 && steppingFilename != ""
		if debugContinue {
			fmt.Printf("[DEBUGGER-STEPIN] Using active debugger state: file=%s, depth=%d, line=%d, valid=%v\n",
				steppingFilename, callDepth, startLine, gotValidState)
		}
	}

	if !gotValidState && dbg.vm != nil && dbg.vm.prg != nil {
		steppingFilename = dbg.Filename()
		callDepth = dbg.lastBreakpoint.stackDepth
		startLine := dbg.Line()
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
		dbg.lastBreakpoint.pc = dbg.vm.pc
		dbg.lastBreakpoint.line = dbg.Line()
		dbg.lastBreakpoint.filename = steppingFilename
		dbg.lastBreakpoint.stackDepth = callDepth
	}

	if gotValidState {
		dbg.steppingFilename = steppingFilename
	} else {
		dbg.steppingFilename = ""
		if debugContinue {
			fmt.Printf("[DEBUGGER-STEPIN] ⚠️ No valid state, using empty steppingFilename\n")
		}
	}

	globalDebugCoordinator.SetGlobalStepState(false, true, steppingFilename, callDepth)
	if debugContinue {
		fmt.Printf("[DEBUGGER-STEPIN] After SetGlobalStepState: stepIn=%v, next=%v, steppingFilename=%s, callDepth=%d\n",
			dbg.stepIn, dbg.next, steppingFilename, callDepth)
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

func (dbg *Debugger) SetNext(v bool) {
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] SetNext: %v (was: %v)\n", v, dbg.next)
	}
	dbg.next = v
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
		fmt.Printf("[DEBUGGER] ResetVMExited: was=%v, setting to false\n", dbg.vmExited)
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
	dbg.stepOverStartLine = dbg.Line() // don't re-break on current line
	dbg.steppingFilename = steppingFilename

	globalDebugCoordinator.SetGlobalStepState(true, false, steppingFilename, targetDepth)
	if debugContinue {
		fmt.Printf("[DEBUGGER-STEPOUT] targetDepth=%d, steppingFilename=%s\n", targetDepth, steppingFilename)
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

	source := dbg.vm.prg.src.Source()
	lines := strings.Split(source, "\n")

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
		if !((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch == '_' || ch == '$' || ch == '.') {
			return false
		}
	}
	if s[0] == '.' || s[len(s)-1] == '.' || strings.Contains(s, "..") {
		return false
	}
	return true
}

func (dbg *Debugger) Evaluate(expr string) (Value, error) {
	if expr == "" {
		return nil, errors.New("nothing to evaluate")
	}

	if isSimpleIdentifier(expr) {
		val, err := dbg.getValue(expr)
		if err == nil && val != nil {
			if _, isUnresolved := val.(valueUnresolved); !isUnresolved {
				return val, nil
			}
		}
	}

	if isDotPropertyChain(expr) {
		parts := strings.Split(expr, ".")
		rootVal, err := dbg.getValue(parts[0])
		if err == nil && rootVal != nil {
			if _, isUnresolved := rootVal.(valueUnresolved); !isUnresolved {
				var result Value
				var evalErr error
				func() {
					defer func() {
						if r := recover(); r != nil {
							evalErr = fmt.Errorf("property access panicked: %v", r)
						}
					}()
					val := rootVal
					for _, prop := range parts[1:] {
						obj, ok := val.(*Object)
						if !ok {
							val = nil
							return
						}
						propVal := obj.Get(prop)
						if propVal == nil || propVal == _undefined {
							val = _undefined
							return
						}
						val = propVal
					}
					result = val
				}()
				if evalErr == nil && result != nil {
					return result, nil
				}
				if evalErr != nil {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] Evaluate('%s'): dot-chain root '%s' found but property access failed: %v\n", expr, parts[0], evalErr)
					}
					return nil, evalErr
				}
				return nil, fmt.Errorf("cannot access property '%s' on non-object value", expr)
			}
		}
	}

	return dbg.evaluateComplexExpression(expr)
}

// buildPausedVarSnapshot collects all accessible variables once per pause and caches them.
// Subsequent evals during the same pause reuse the snapshot without re-walking the stash.
func (dbg *Debugger) buildPausedVarSnapshot() map[string]Value {
	currentLine := dbg.Line()
	if dbg.pausedVarSnapshot != nil && dbg.pausedVarSnapshotLine == currentLine {
		return dbg.pausedVarSnapshot
	}

	snap := make(map[string]Value, 64)

	// Walk stash chain.
	stashLevel := 0
	for s := dbg.vm.stash; s != nil; s = s.outer {
		if s.names != nil {
			for name, idx := range s.names {
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
							val = dbg.resolveIndirectValue(val)
						}
						if isSimpleIdentifier(nameStr) {
							snap[nameStr] = val
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
				if snap[keyStr] != nil || !isSimpleIdentifier(keyStr) || globalBuiltinKeys[keyStr] || globalUnsafeKeys[keyStr] {
					continue
				}
				if v := safeGetGlobalProperty(globalObj, unistring.String(keyStr)); v != nil && !isNullValue(v) {
					snap[keyStr] = v
				}
			}
		}
	}

	dbg.pausedVarSnapshot = snap
	dbg.pausedVarSnapshotLine = currentLine
	return snap
}

func (dbg *Debugger) evaluateComplexExpression(expr string) (Value, error) {
	dbg.evalMutex.Lock()
	defer dbg.evalMutex.Unlock()

	registry := GetGlobalRegistry()
	if registry != nil {
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
			fmt.Printf("[DEBUGGER] Registry eval failed: %v, falling back to single-VM eval\n", err)
		}
	}

	if dbg.vm.sb < 0 || dbg.vm.stash == nil {
		return nil, fmt.Errorf("cannot evaluate: invalid execution state")
	}

	// PERF: use per-pause snapshot so we walk the stash chain only once per pause,
	// regardless of how many variables the user hovers over.
	varSnapshot := dbg.buildPausedVarSnapshot()

	varNames := make([]string, 0, len(varSnapshot))
	varValues := make([]Value, 0, len(varSnapshot))
	for name, val := range varSnapshot {
		varNames = append(varNames, name)
		varValues = append(varValues, val)
	}

	// Also add stack-based locals from debug symbols (not in stash snapshot).
	currentPC := dbg.vm.pc
	currentLine := dbg.Line()
	seen := make(map[string]bool, len(varSnapshot))
	for _, n := range varNames {
		seen[n] = true
	}

	if dbg.vm.prg != nil && dbg.vm.prg.debugSymbols != nil {
		if varLocs, exists := dbg.vm.prg.debugSymbols.scopeMap[currentPC]; exists {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] Found %d debug symbols at PC=%d (line %d)\n", len(varLocs), currentPC, currentLine)
			}
			for _, varLoc := range varLocs {
				if seen[varLoc.Name] {
					continue
				}
				val, err := dbg.getValueFromLocation(varLoc)
				if err == nil && val != nil && !isNullValue(val) {
					seen[varLoc.Name] = true
					varNames = append(varNames, varLoc.Name)
					varValues = append(varValues, val)
				}
			}
		}
	}

	if varInfo := dbg.getSourceVarInfo(currentLine); varInfo != nil {
		for paramName, paramIdx := range varInfo.params {
			if seen[paramName] {
				continue
			}
			pIdx := -(paramIdx + 1)
			stackPos := dbg.vm.sb + 1 + pIdx
			if stackPos >= dbg.vm.sb && stackPos < dbg.vm.sp && stackPos < len(dbg.vm.stack) {
				val := dbg.vm.stack[stackPos]
				if val != nil && !isNullValue(val) && !isFunctionValue(val) {
					seen[paramName] = true
					varNames = append(varNames, paramName)
					varValues = append(varValues, val)
				}
			}
		}
		for localName, localIdx := range varInfo.locals {
			if seen[localName] {
				continue
			}
			declLine := varInfo.declLines[localName]
			if declLine > currentLine {
				continue
			}
			stackPos := dbg.vm.sb + 2 + localIdx
			if stackPos >= dbg.vm.sb && stackPos < dbg.vm.sp && stackPos < len(dbg.vm.stack) {
				val := dbg.vm.stack[stackPos]
				if val != nil && !isNullValue(val) && !isFunctionValue(val) {
					seen[localName] = true
					varNames = append(varNames, localName)
					varValues = append(varValues, val)
				}
			}
		}
	}

	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] Evaluating '%s' with %d variables available\n", expr, len(varNames))
	}

	globalObj := dbg.vm.r.globalObject
	savedVars := make(map[string]Value)
	for i, name := range varNames {
		nameUni := unistring.String(name)
		if existingVal := safeGetGlobalProperty(globalObj, nameUni); existingVal != nil {
			savedVars[name] = existingVal
		}
		globalObj.self.setOwnStr(nameUni, varValues[i], false)
	}

	prog, compileErr := compile("<eval>", expr, false, true, nil, dbg.vm.debugMode, dbg.vm.r.parserOptions...)
	if compileErr != nil {
		for _, name := range varNames {
			nameUni := unistring.String(name)
			if savedVal, hadValue := savedVars[name]; hadValue {
				globalObj.self.setOwnStr(nameUni, savedVal, false)
			} else {
				globalObj.self.deleteStr(nameUni, false)
			}
		}
		return nil, fmt.Errorf("compilation error: %w", compileErr)
	}

	var result Value
	var evalErr error
	result, evalErr = dbg.vm.r.RunProgram(prog)
	if evalErr != nil {
		if exc, ok := evalErr.(*Exception); ok {
			evalErr = exc
		}
	}

	for _, name := range varNames {
		nameUni := unistring.String(name)
		if savedVal, hadValue := savedVars[name]; hadValue {
			globalObj.self.setOwnStr(nameUni, savedVal, false)
		} else {
			globalObj.self.deleteStr(nameUni, false)
		}
	}

	if evalErr != nil {
		return nil, fmt.Errorf("evaluation error: %w", evalErr)
	}
	return result, nil
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
	if varLocs, exists := dbg.vm.prg.debugSymbols.scopeMap[dbg.vm.pc]; exists {
		return varLocs
	}
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] debugVarLocations: no symbols at PC %d for program %s (funcName=%s), scopeMap has %d entries\n",
			dbg.vm.pc, dbg.vm.prg.src.Name(), dbg.vm.prg.funcName, len(dbg.vm.prg.debugSymbols.scopeMap))
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

	savedNext := dbg.next
	savedStepIn := dbg.stepIn
	savedContinuing := dbg.continuing
	savedStepOverTargetDepth := dbg.stepOverTargetDepth
	savedStepOverStartLine := dbg.stepOverStartLine
	savedSteppingFilename := dbg.steppingFilename
	savedActive := dbg.active
	savedLastBreakpoint := dbg.lastBreakpoint
	savedUserCommandIssued := dbg.userCommandIssued
	savedLifecycleTransition := dbg.lifecycleTransition

	dbg.suppressDebugger = true

	defer func() {
		dbg.suppressDebugger = false

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
		dbg.stepOverStartLine = savedStepOverStartLine
		dbg.steppingFilename = savedSteppingFilename
		dbg.active = savedActive
		dbg.lastBreakpoint = savedLastBreakpoint
		dbg.userCommandIssued = savedUserCommandIssued
		dbg.lifecycleTransition = savedLifecycleTransition

		// Also reset the prg cache since we restored vm.prg.
		dbg.cachedPrg = nil
	}()

	result = fn()
	return result
}

func (dbg *Debugger) resolveIndirectValue(rawVal Value) Value {
	if rawVal == nil || dbg.vm == nil || dbg.vm.r == nil {
		return rawVal
	}
	resolved := dbg.withSuppressedDebugger(func() Value {
		var f func(*vm) Value
		if err := dbg.vm.r.ExportTo(rawVal, &f); err == nil && f != nil {
			v := f(dbg.vm)
			if v != nil {
				return v
			}
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
		if dbg.vm.stash != nil {
			stashIdx := int(varLoc.StashIdx)
			if dbg.vm.stash.values != nil && stashIdx < len(dbg.vm.stash.values) {
				val := dbg.vm.stash.values[stashIdx]
				if val != nil && !isNullValue(val) {
					if dbg.vm.stash.names != nil {
						for name, idx := range dbg.vm.stash.names {
							actualIdx := idx & uint32(maskIndex)
							if int(actualIdx) == stashIdx && (idx&maskIndirect) != 0 {
								nameStr := name.String()
								if lifecycleFunctionKeys[nameStr] {
									break
								}
								val = dbg.resolveIndirectValue(val)
								break
							}
						}
					}
					return val, nil
				}
				if dbg.vm.debugMode {
					return _undefined, nil
				}
			}
		}
	} else {
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
	}
	return nil, fmt.Errorf("variable not found")
}

func (dbg *Debugger) GetLocalVariables() (map[string]Value, error) {
	locals := make(map[string]Value)

	if !dbg.active || dbg.vm.prg == nil {
		return locals, nil
	}

	if dbg.vm.sb < 0 {
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] GetLocalVariables: vm.sb=%d at PC=%d (function stash not yet pushed), returning empty locals\n", dbg.vm.sb, dbg.vm.pc)
		}
		return locals, nil
	}

	if dbg.vm.stash == nil {
		return locals, nil
	}

	if dbg.vm.debugMode && dbg.vm.prg.debugSymbols != nil {
		if dbg.vm.prg.funcName == "" {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] GetLocalVariables: at module-level code (funcName=''), returning empty locals (globals handled by GetGlobalVariables)\n")
			}
			return locals, nil
		}

		varLocs := dbg.debugVarLocations()
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] GetLocalVariables: using debug symbols, found %d variables at PC %d (funcName=%s)\n",
				len(varLocs), dbg.vm.pc, dbg.vm.prg.funcName)
		}

		for _, varLoc := range varLocs {
			if !isIdentifierLike(varLoc.Name) {
				continue
			}
			val, err := dbg.getValueFromLocation(varLoc)
			if err == nil && val != nil && !isNullValue(val) {
				locals[varLoc.Name] = val
			}
		}

		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] GetLocalVariables: collected %d function-local variables from debug symbols\n", len(locals))
		}
		return locals, nil
	}

	if dbg.vm.stash != nil && dbg.vm.stash.names != nil {
		for name, idx := range dbg.vm.stash.names {
			nameStr := name.String()
			if !isIdentifierLike(nameStr) || nameStr == "" {
				continue
			}
			actualIdx := idx & uint32(maskIndex)
			if int(actualIdx) >= 0 && int(actualIdx) < len(dbg.vm.stash.values) {
				val := dbg.vm.stash.values[actualIdx]
				if val != nil && !isNullValue(val) {
					if (idx&maskIndirect) != 0 && !lifecycleFunctionKeys[nameStr] {
						val = dbg.resolveIndirectValue(val)
					}
					locals[nameStr] = val
				}
			}
		}
	}

	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] GetLocalVariables: collected %d variables (legacy mode)\n", len(locals))
	}

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
	if dbg.vm == nil || dbg.vm.prg == nil {
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
				if int(actualIdx) >= 0 && int(actualIdx) < len(s.values) {
					val := s.values[actualIdx]
					if val != nil && !isNullValue(val) {
						if (idx&maskIndirect) != 0 && !lifecycleFunctionKeys[nameStr] {
							val = dbg.resolveIndirectValue(val)
						}
						globals[nameStr] = val
						if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] GetGlobalVariables: captured %s from stash level %d (idx=%d)\n",
								nameStr, stashLevel, actualIdx)
						}
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
				for name, getter := range stmi.exportGetters {
					if _, exists := vars[name]; exists {
						continue
					}
					if !isIdentifierLike(name) || globalBuiltinKeys[name] {
						continue
					}
					if lifecycleFunctionKeys[name] {
						continue
					}
					val := dbg.safeCallGetter(getter)
					if val != nil && !isNullValue(val) {
						vars[name] = val
						if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] GetAllStashVariables: captured %s from module (getter)\n", name)
						}
					}
				}
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
	return vars
}

func (dbg *Debugger) extractStashVars(s *stash, vars map[string]Value, level int, source string) {
	if s == nil {
		return
	}
	namesCount := 0
	if s.names != nil {
		namesCount = len(s.names)
	}
	valuesCount := 0
	if s.values != nil {
		valuesCount = len(s.values)
	}
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] GetAllStashVariables: %s level %d - names=%d, values=%d, hasObj=%v\n",
			source, level, namesCount, valuesCount, s.obj != nil)
	}

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
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] GetAllStashVariables: captured %s from %s (idx=%d)\n",
							nameStr, source, actualIdx)
					}
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

	isLifecycleEntry := dbg.vm.sb < 0 && dbg.vm.pc == 0
	if dbg.vm.sb < 0 && !isLifecycleEntry {
		return nil, fmt.Errorf("cannot access variables during context transition (vm.sb=%d)", dbg.vm.sb)
	}
	if dbg.vm.stash == nil && !isLifecycleEntry {
		return nil, fmt.Errorf("variable '%s' not accessible (no execution context)", varName)
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

	name := unistring.String(varName)

	if dbg.vm.prg != nil && dbg.vm.prg.debugSymbols != nil {
		if varLocs, exists := dbg.vm.prg.debugSymbols.scopeMap[dbg.vm.pc]; exists {
			for _, varLoc := range varLocs {
				if varLoc.Name == varName {
					if varLoc.InStash {
						if dbg.vm.stash != nil {
							stashIdx := int(varLoc.StashIdx)
							if dbg.vm.stash.values != nil && stashIdx < len(dbg.vm.stash.values) {
								val = dbg.vm.stash.values[stashIdx]
								if val != nil && !isNullValue(val) {
									if dbg.enableDebugLogging {
										fmt.Printf("[DEBUGGER] getValue('%s'): Found in stash level 0, idx %d (from debug symbols)\n",
											varName, stashIdx)
									}
									return val, nil
								}
							}
						}
					} else {
						var stackPos int
						if varLoc.IsParam || varLoc.StackIdx < 0 {
							argNum := -int(varLoc.StackIdx) - 1
							stackPos = dbg.vm.sb + 1 + argNum
						} else {
							stackPos = dbg.vm.sb + int(varLoc.StackIdx)
							if stackPos < dbg.vm.sb || stackPos >= dbg.vm.sp {
								if dbg.vm.args > 0 {
									stackPos = dbg.vm.sb + dbg.vm.args + int(varLoc.StackIdx)
								}
							}
						}
						if stackPos >= dbg.vm.sb && stackPos < dbg.vm.sp && stackPos >= 0 && stackPos < len(dbg.vm.stack) {
							val = dbg.vm.stack[stackPos]
							if val != nil && !isNullValue(val) && !isFunctionValue(val) {
								if dbg.enableDebugLogging {
									fmt.Printf("[DEBUGGER] getValue('%s'): Found on stack at pos %d (stackIdx=%d, isParam=%v, from debug symbols)\n",
										varName, stackPos, varLoc.StackIdx, varLoc.IsParam)
								}
								return val, nil
							}
						}
					}
				}
			}
		}
	}

	stashLevel := 0
	for s := dbg.vm.stash; s != nil; s = s.outer {
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
				if getter, exists := stmi.exportGetters[varName]; exists {
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

	return nil, fmt.Errorf("variable '%s' not found in any scope", varName)
}

func isNullValue(v Value) bool {
	if v == nil {
		return true
	}
	if _, isNull := v.(valueNull); isNull {
		return true
	}
	if _, isUndef := v.(valueUndefined); isUndef {
		return true
	}
	return false
}

func isFunctionValue(v Value) bool {
	if v == nil {
		return false
	}
	if obj, ok := v.(*Object); ok {
		_, isCallable := obj.self.assertCallable()
		return isCallable
	}
	return false
}

func (dbg *Debugger) GetCallStack() ([]StackFrame, error) {
	frames := make([]StackFrame, 0, len(dbg.vm.callStack)+1)

	topFrame := StackFrame{
		Index:    0,
		pc:       dbg.vm.pc,
		funcName: "",
		File:     dbg.Filename(),
		Line:     dbg.Line(),
	}
	if dbg.vm.prg != nil {
		topFrame.prg = dbg.vm.prg
		topFrame.funcName = dbg.vm.prg.funcName
		if topFrame.funcName == "" {
			topFrame.funcName = "<module>"
		}
	}
	frames = append(frames, topFrame)

	for i := len(dbg.vm.callStack) - 1; i >= 0; i-- {
		frame := dbg.vm.callStack[i]
		frameInfo := StackFrame{
			Index:    len(frames),
			pc:       frame.pc,
			funcName: "unknown",
		}

		if frame.prg != nil {
			frameInfo.prg = frame.prg
			if frame.prg.funcName != "" {
				frameInfo.funcName = frame.prg.funcName
			} else {
				frameInfo.funcName = "<anonymous>"
			}
			if frame.prg.src != nil {
				pos := frame.prg.src.Position(frame.prg.sourceOffset(frame.pc))
				frameInfo.File = frame.prg.src.Name()
				frameInfo.Line = pos.Line
			} else {
				frameInfo.File = "<unknown>"
				frameInfo.Line = 0
			}
		} else {
			frameInfo.funcName = "<native>"
			frameInfo.File = "<native>"
			frameInfo.Line = 0
		}

		frames = append(frames, frameInfo)
	}

	return frames, nil
}

func (dbg *Debugger) SetInitRuntime(rt *Runtime) {
	dbg.initRuntime = rt
}

func (dbg *Debugger) SetSetupData(data Value) {
	dbg.setupData = data
}
