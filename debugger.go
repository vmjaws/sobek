package sobek

import (
	"bufio"
	"errors"
	"fmt"
	"sort"
	"strconv"
	"strings"
	"sync"
	"unicode"

	"github.com/grafana/sobek/unistring"
)

type Debugger struct {
	vm *vm

	currentLine     int
	lastLine        int
	breakpoints     map[string][]int
	breakpointMutex sync.RWMutex
	breakpointIDs   map[string]int
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
	next              bool
	stepIn            bool
	continuing        bool
	stepOverTargetDepth int  // Depth where step-over operation started
	enableDebugLogging bool
	configuredCh      chan struct{}
	waitingForConfig  bool
	evalMutex         sync.Mutex

	// Performance caches
	varDeclLines      map[string]int
	sourceVarCache    map[int]*sourceVarInfo // Cache keyed by line number
	globalVarCache    map[string]bool
	sourceCacheValid  bool

	// Variable value cache - stores captured return values
	varValueCache     map[string]Value // Cache keyed by "filename:line:varName"
	varValueCacheLine int              // Current line where cache is valid

	// Function call tracking
	functionCallStack    []FunctionCall
	pendingReturnValues map[int]Value // keyed by stack depth
	returnValueCache    map[string]Value // keyed by "funcName:line"

	// Scope tracking
	currentScopeDepth   int
	scopeVariables     map[int]map[string]Value // depth -> variables
	
	// Cross-VM variable access
	initRuntime       *Runtime  // Reference to init VM for global variable access
	setupData         Value     // Setup function return value
}



type sourceVarInfo struct {
	params     map[string]int  // paramName -> negative index
	locals     map[string]int  // varName -> positive index
	declLines  map[string]int  // varName -> declaration line
	numParams  int
}

func newDebugger(vm *vm) *Debugger {
	dbg := &Debugger{
		vm:                 vm,
		activationCh:       make(chan chan DebuggerActivation),
		active:             false,
		breakpoints:        make(map[string][]int),
		breakpointIDs:      make(map[string]int),
		lastLine:           0,
		configuredCh:       make(chan struct{}),
		waitingForConfig:   true,
		varDeclLines:       make(map[string]int),
		sourceVarCache:     make(map[int]*sourceVarInfo),
		globalVarCache:     make(map[string]bool),
		sourceCacheValid:   false,
		continuing:         false,
		enableDebugLogging: true, // ENABLED by default to help diagnose stack issues
		varValueCache:      make(map[string]Value),
		varValueCacheLine:  -1,
	}
	return dbg
}

type ActivationReason string

const (
	ProgramStartActivation      ActivationReason = "start"
	DebuggerStatementActivation ActivationReason = "debugger"
	BreakpointActivation        ActivationReason = "breakpoint"
)

type DebuggerActivation struct {
	Reason   ActivationReason
	Filename string
	Line     int
	ID       int
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

// isIdentifierLike reports whether the name can be used as a JavaScript identifier.
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

func (dbg *Debugger) activate(reason ActivationReason, filename string, line int) {
	dbg.active = true
	ch := <-dbg.activationCh

	id := 0
	if reason != DebuggerStatementActivation {
		dbg.breakpointMutex.RLock()
		id = dbg.breakpointIDs[filename+":"+strconv.Itoa(line)]
		dbg.breakpointMutex.RUnlock()
	}

	ch <- DebuggerActivation{
		Reason:   reason,
		Filename: filename,
		Line:     line,
		ID:       id,
	}
	<-ch
	dbg.active = false
}

func (dbg *Debugger) Continue() DebuggerActivation {
	if dbg.currentCh != nil {
		close(dbg.currentCh)
	}
	dbg.currentCh = make(chan DebuggerActivation)
	dbg.activationCh <- dbg.currentCh
	activation := <-dbg.currentCh
	return activation
}

func (dbg *Debugger) SetConfigured() {
	if dbg.waitingForConfig {
		dbg.waitingForConfig = false
		close(dbg.configuredCh)
	}
}

func (dbg *Debugger) EnableDebugLogging() {
	dbg.enableDebugLogging = true
}

func (dbg *Debugger) DisableDebugLogging() {
	dbg.enableDebugLogging = false
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

func (dbg *Debugger) Detach() {
	dbg.vm.debugger = nil
	dbg.vm.debugMode = false
	dbg.vm = nil
	dbg.active = false
	if dbg.currentCh != nil {
		close(dbg.currentCh)
		dbg.currentCh = nil
	}
}

func (dbg *Debugger) SetBreakpoint(filename string, line int) (id int, err error) {
	idx := sort.SearchInts(dbg.breakpoints[filename], line)
	if idx < len(dbg.breakpoints[filename]) && dbg.breakpoints[filename][idx] == line {
		err = errors.New("breakpoint exists")
	} else {
		dbg.breakpoints[filename] = append(dbg.breakpoints[filename], line)
		if len(dbg.breakpoints[filename]) > 1 {
			sort.Ints(dbg.breakpoints[filename])
		}
		dbg.breakpointMutex.Lock()
		id = dbg.breakPointCount
		dbg.breakPointCount++
		dbg.breakpointIDs[filename+":"+strconv.Itoa(line)] = id
		dbg.breakpointMutex.Unlock()
	}
	return
}

func (dbg *Debugger) ClearBreakpoint(filename string, line int) (err error) {
	if len(dbg.breakpoints[filename]) == 0 {
		return errors.New("no breakpoints")
	}

	idx := sort.SearchInts(dbg.breakpoints[filename], line)
	if idx < len(dbg.breakpoints[filename]) && dbg.breakpoints[filename][idx] == line {
		dbg.breakpoints[filename] = append(dbg.breakpoints[filename][:idx], dbg.breakpoints[filename][idx+1:]...)
		if len(dbg.breakpoints[filename]) == 0 {
			delete(dbg.breakpoints, filename)
		}
	} else {
		err = errors.New("breakpoint doesn't exist")
	}
	return
}

func (dbg *Debugger) Breakpoints() (map[string][]int, error) {
	if len(dbg.breakpoints) == 0 {
		return nil, errors.New("no breakpoints")
	}
	return dbg.breakpoints, nil
}

func (dbg *Debugger) Next() error {
	dbg.next = true
	dbg.continuing = false
	dbg.stepOverTargetDepth = dbg.callStackDepth()  // Capture the depth where we START step-over
	dbg.lastBreakpoint.pc = dbg.vm.pc
	dbg.lastBreakpoint.line = dbg.Line()
	dbg.lastBreakpoint.stackDepth = dbg.callStackDepth()

	if dbg.currentCh != nil {
		close(dbg.currentCh)
		dbg.currentCh = nil
	}
	return nil
}

func (dbg *Debugger) ClearStepFlags() {
	dbg.lastBreakpoint.pc = dbg.vm.pc
	dbg.lastBreakpoint.line = dbg.Line()
	dbg.lastBreakpoint.filename = dbg.Filename()
	dbg.lastBreakpoint.stackDepth = dbg.callStackDepth()
	dbg.next = false
	dbg.stepIn = false
	dbg.continuing = true
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

func (dbg *Debugger) breakpoint() bool {
	if dbg.vm.prg == nil {
		return false
	}
	filename := dbg.Filename()
	line := dbg.Line()

	idx := sort.SearchInts(dbg.breakpoints[filename], line)
	return idx < len(dbg.breakpoints[filename]) && dbg.breakpoints[filename][idx] == line
}

func (dbg *Debugger) getLastLine() int {
	if dbg.lastLine >= 0 {
		return dbg.lastLine
	}
	return dbg.Line()
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
	return dbg.vm.prg.src.Position(dbg.vm.prg.sourceOffset(dbg.vm.pc)).Line
}

func (dbg *Debugger) Filename() string {
	if dbg.vm.prg == nil || dbg.vm.prg.src == nil {
		return ""
	}
	return dbg.vm.prg.src.Name()
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
	dbg.stepIn = true
	dbg.continuing = false
	dbg.lastBreakpoint.pc = dbg.vm.pc
	dbg.lastBreakpoint.line = dbg.Line()
	dbg.lastBreakpoint.stackDepth = dbg.callStackDepth()

	if dbg.currentCh != nil {
		close(dbg.currentCh)
		dbg.currentCh = nil
	}
	return nil
}

func (dbg *Debugger) List() ([]string, error) {
	if dbg.vm.prg == nil || dbg.vm.prg.src == nil {
		return nil, errors.New("no program source available")
	}
	return stringToLines(dbg.vm.prg.src.Source())
}

// OPTIMIZED: Cache source parsing results
func (dbg *Debugger) getSourceVarInfo(functionStartLine int) *sourceVarInfo {
	// CRITICAL FIX: Disable cache because it incorrectly caches variables visible at one line
	// and reuses that cache at later lines, missing newly declared variables
	// The cache is keyed only by functionStartLine, but should include currentLine too
	// For now, we disable caching to ensure correctness
	// if info, exists := dbg.sourceVarCache[functionStartLine]; exists && dbg.sourceCacheValid {
	// 	return info
	// }

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
	currentLine := dbg.Line()

	if currentLine < 0 || currentLine > len(lines) {
		return info
	}

	// Find function start
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
					if strings.Contains(trimmed, "function") {
						functionStart = i
						functionLine = trimmed
						goto foundFunction
					}
				}
			}
		}
	}

foundFunction:
	if functionStart < 0 {
		return info
	}

	// Extract parameters
	if openParen := strings.Index(functionLine, "("); openParen >= 0 {
		if closeParen := strings.Index(functionLine[openParen:], ")"); closeParen >= 0 {
			paramsStr := functionLine[openParen+1 : openParen+closeParen]
			if strings.TrimSpace(paramsStr) != "" {
				params := strings.Split(paramsStr, ",")
				for _, param := range params {
					paramName := strings.TrimSpace(param)
					if colonIdx := strings.Index(paramName, ":"); colonIdx >= 0 {
						paramName = strings.TrimSpace(paramName[:colonIdx])
					}
					if eqIdx := strings.Index(paramName, "="); eqIdx >= 0 {
						paramName = strings.TrimSpace(paramName[:eqIdx])
					}
					if paramName != "" && isSimpleIdentifier(paramName) &&
						!strings.Contains(paramName, "{") && !strings.Contains(paramName, "[") {
						info.params[paramName] = -(len(info.params) + 1)
						info.numParams++
					}
				}
			}
		}
	}

	// Scan for local variables
	// CRITICAL FIX: Scan UP TO AND INCLUDING the current line to detect variables declared on the current line
	// Convert currentLine from 1-based to 0-based for array indexing
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
				// Look for the keyword at the START of the trimmed line
				if !strings.HasPrefix(trimmed, keyword) {
					continue
				}

				rest := trimmed[len(keyword):]
				rest = strings.TrimSpace(rest)

				// Extract just the variable name (stop at =, ;, ,, :, or whitespace)
				varName := ""
				for _, ch := range rest {
					if ch == ' ' || ch == '=' || ch == ';' || ch == ',' || ch == ':' || ch == '\t' {
						break
					}
					varName += string(ch)
				}
				varName = strings.TrimSpace(varName)

				// Only process if it's a valid identifier and doesn't already exist
				if varName != "" && isSimpleIdentifier(varName) {
					if _, exists := info.locals[varName]; !exists {
						info.locals[varName] = localVarCount
						localVarCount++
						info.declLines[varName] = i + 1

						if dbg.enableDebugLogging {
							fmt.Printf("[PARSER] Found variable '%s' at line %d (index %d)\n", varName, i+1, localVarCount-1)
						}
					}
					// Only process the first keyword match per line
					break
				}
			}
		}
	}

	dbg.sourceVarCache[functionStart] = info
	dbg.sourceCacheValid = true
	return info
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

	return dbg.evaluateComplexExpression(expr)
}

func (dbg *Debugger) evaluateComplexExpression(expr string) (Value, error) {
	dbg.evalMutex.Lock()
	defer dbg.evalMutex.Unlock()

	// Try using the global registry for multi-scope eval first with panic recovery
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
		
		// If registry eval fails, fall back to single-VM eval
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] Registry eval failed: %v, falling back to single-VM eval\n", err)
		}
	}

	// FALLBACK: Single-VM eval
	if dbg.vm.sb < 0 || dbg.vm.stash == nil {
		return nil, fmt.Errorf("cannot evaluate: invalid execution state")
	}

	// STRATEGY: Collect ALL accessible variables from stash + stack
	varNames := make([]string, 0, 64)
	varValues := make([]Value, 0, 64)
	seen := make(map[string]bool)

	// 1. Walk stash chain for variables in scope
	stashLevel := 0
	for s := dbg.vm.stash; s != nil; s = s.outer {
		if s.names != nil {
			for name, idx := range s.names {
				nameStr := name.String()
				if seen[nameStr] || globalBuiltinKeys[nameStr] {
					continue
				}

				actualIdx := idx & uint32(maskIndex)
				isIndirect := (idx & maskIndirect) != 0

				var val Value
				var found bool

				if isIndirect {
					// Indirect: stored in THIS stash's values
					nonIndirectCount := 0
					for _, otherIdx := range s.names {
						otherActualIdx := otherIdx & uint32(maskIndex)
						otherIsIndirect := (otherIdx & maskIndirect) != 0
						if !otherIsIndirect && otherActualIdx < actualIdx {
							nonIndirectCount++
						}
					}
					adjustedIdx := int(actualIdx) - nonIndirectCount
					if adjustedIdx >= 0 && adjustedIdx < len(s.values) {
						val = s.values[adjustedIdx]
						found = (val != nil && !isNullValue(val))
					}
				} else {
					// Non-indirect: look in parent stash
					for parent := s.outer; parent != nil; parent = parent.outer {
						if parent.names != nil {
							if parentIdx, exists := parent.names[name]; exists {
								parentActualIdx := parentIdx & 0x00FFFFFF
								if int(parentActualIdx) < len(parent.values) {
									val = parent.values[parentActualIdx]
									found = (val != nil && !isNullValue(val))
									break
								}
							}
						}
						if !found && parent.obj != nil {
							if v := parent.obj.self.getStr(name, nil); v != nil {
								val = v
								found = true
								break
							}
						}
					}
				}

				if found && isSimpleIdentifier(nameStr) {
					seen[nameStr] = true
					varNames = append(varNames, nameStr)
					varValues = append(varValues, val)
				}
			}
		}

		// Check object properties
		if s.obj != nil {
			iter := s.obj.self.iterateStringKeys()
			for {
				item, next := iter()
				if next == nil {
					break
				}
				iter = next

				keyStr := item.name.String()
				if !seen[keyStr] && isSimpleIdentifier(keyStr) && !globalBuiltinKeys[keyStr] {
					seen[keyStr] = true
					if item.value != nil && !isNullValue(item.value) {
						varNames = append(varNames, keyStr)
						varValues = append(varValues, item.value)
					}
				}
			}
		}
		stashLevel++
	}

	// 2. Add stack-based local variables using debug symbols (more accurate than source parsing)
	currentPC := dbg.vm.pc
	currentLine := dbg.Line()
	
	// First try to use debug symbols if available
	if dbg.vm.prg != nil && dbg.vm.prg.debugSymbols != nil {
		if varLocs, exists := dbg.vm.prg.debugSymbols.scopeMap[currentPC]; exists {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] Found %d debug symbols at PC=%d (line %d)\n", len(varLocs), currentPC, currentLine)
			}
			for _, varLoc := range varLocs {
				if seen[varLoc.Name] {
					continue
				}
				
				var val Value
				var found bool
				
				if varLoc.InStash {
					// Variable is in stash - find it in stash chain
					if dbg.vm.stash != nil {
						stashIdx := int(varLoc.StashIdx)
						stashLevel := 0
						for s := dbg.vm.stash; s != nil && stashLevel <= 2; s = s.outer {
							if s.values != nil {
								if dbg.enableDebugLogging && stashLevel == 0 {
									fmt.Printf("[DEBUGGER] Checking stash level %d for '%s' (stashIdx=%d, stashValuesLen=%d)\n",
										stashLevel, varLoc.Name, stashIdx, len(s.values))
								}
								if stashIdx < len(s.values) {
									val = s.values[stashIdx]
									if val != nil && !isNullValue(val) {
										found = true
										if dbg.enableDebugLogging {
											fmt.Printf("[DEBUGGER] Found stash variable '%s' at stash level %d, idx %d\n", 
												varLoc.Name, stashLevel, stashIdx)
										}
										break
									} else {
										if dbg.enableDebugLogging && stashLevel == 0 {
											fmt.Printf("[DEBUGGER] Stash variable '%s' at idx %d is nil/invalid (val=%v)\n",
												varLoc.Name, stashIdx, val)
										}
									}
								} else {
									if dbg.enableDebugLogging && stashLevel == 0 {
										fmt.Printf("[DEBUGGER] Stash idx %d out of range for '%s' (len=%d)\n",
											stashIdx, varLoc.Name, len(s.values))
									}
								}
							}
							stashLevel++
						}
					} else {
						if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] No stash available for variable '%s'\n", varLoc.Name)
						}
					}
				} else {
					// Variable is on stack
					// StackIdx from debug symbols is relative to stackOffset which accounts for args
					// If it's negative, it's an argument, otherwise it's a local
					var stackPos int
					if varLoc.IsParam {
						// Argument: StackIdx is negative, use sb + 1 + (-StackIdx - 1) = sb - StackIdx
						stackPos = dbg.vm.sb - int(varLoc.StackIdx)
					} else {
						// Local variable: StackIdx is already relative to stackOffset
						// Need to check if args are in stash or on stack
						// If args are in stash, locals start at sb+1, otherwise at sb+args+1
						// For now, try both possibilities
						stackPos = dbg.vm.sb + int(varLoc.StackIdx)
						// Also try with args offset if the first doesn't work
						if stackPos < dbg.vm.sb || stackPos >= dbg.vm.sp {
							// Try with args offset
							if dbg.vm.args > 0 {
								stackPos = dbg.vm.sb + dbg.vm.args + int(varLoc.StackIdx)
							}
						}
					}
					
					if stackPos >= dbg.vm.sb && stackPos < dbg.vm.sp && stackPos >= 0 && stackPos < len(dbg.vm.stack) {
						val = dbg.vm.stack[stackPos]
						if val != nil && !isNullValue(val) && !isFunctionValue(val) {
							found = true
							if dbg.enableDebugLogging {
								fmt.Printf("[DEBUGGER] Found stack variable '%s' at stack pos %d (sb=%d, sp=%d, stackIdx=%d, isParam=%v)\n", 
									varLoc.Name, stackPos, dbg.vm.sb, dbg.vm.sp, varLoc.StackIdx, varLoc.IsParam)
							}
						} else {
							if dbg.enableDebugLogging {
								fmt.Printf("[DEBUGGER] Stack variable '%s' at pos %d is nil/invalid (val=%v)\n",
									varLoc.Name, stackPos, val)
							}
						}
					} else {
						if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] Stack variable '%s' out of range: stackPos=%d, sb=%d, sp=%d, stackLen=%d, stackIdx=%d\n",
								varLoc.Name, stackPos, dbg.vm.sb, dbg.vm.sp, len(dbg.vm.stack), varLoc.StackIdx)
						}
					}
				}
				
				if found {
					seen[varLoc.Name] = true
					varNames = append(varNames, varLoc.Name)
					varValues = append(varValues, val)
				}
			}
		} else {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] No debug symbols found at PC=%d, falling back to source parsing\n", currentPC)
			}
		}
	}
	
	// Fallback to source parsing if debug symbols don't have the variable
	if varInfo := dbg.getSourceVarInfo(currentLine); varInfo != nil {
		// Add parameters from stack
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
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] Found parameter '%s' via source parsing at stack pos %d\n", paramName, stackPos)
					}
				}
			}
		}

		// Add local variables from stack
		for localName, localIdx := range varInfo.locals {
			if seen[localName] {
				continue
			}

			// Check if this variable has been declared yet
			declLine := varInfo.declLines[localName]
			if declLine > currentLine {
				if dbg.enableDebugLogging {
					fmt.Printf("[DEBUGGER] Skipping '%s': declared at line %d, current line %d\n", localName, declLine, currentLine)
				}
				continue // Not yet declared
			}

			stackPos := dbg.vm.sb + 2 + localIdx
			if stackPos >= dbg.vm.sb && stackPos < dbg.vm.sp && stackPos < len(dbg.vm.stack) {
				val := dbg.vm.stack[stackPos]
				if val != nil && !isNullValue(val) && !isFunctionValue(val) {
					seen[localName] = true
					varNames = append(varNames, localName)
					varValues = append(varValues, val)
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] Found local '%s' via source parsing at stack pos %d (localIdx=%d)\n", 
							localName, stackPos, localIdx)
					}
				} else {
					if dbg.enableDebugLogging {
						fmt.Printf("[DEBUGGER] Local '%s' at stack pos %d is nil or invalid (val=%v)\n", 
							localName, stackPos, val)
					}
				}
			} else {
				if dbg.enableDebugLogging {
					fmt.Printf("[DEBUGGER] Local '%s' stack pos %d out of range (sb=%d, sp=%d, len=%d)\n",
						localName, stackPos, dbg.vm.sb, dbg.vm.sp, len(dbg.vm.stack))
				}
			}
		}
	}

	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] Evaluating '%s' with %d variables available\n", expr, len(varNames))
	}

	// 3. Inject all variables into global scope for evaluation
	globalObj := dbg.vm.r.globalObject
	savedVars := make(map[string]Value)

	for i, name := range varNames {
		nameUni := unistring.String(name)
		if existingVal := globalObj.self.getStr(nameUni, nil); existingVal != nil {
			savedVars[name] = existingVal
		}
		globalObj.self.setOwnStr(nameUni, varValues[i], false)
	}

	// 4. Compile and evaluate expression with FRESH context (not evalVm)
	// CRITICAL: Pass nil as evalVm because:
	// - evalVm makes the compiler try to resolve variables from the STASH CHAIN at compile time
	// - But in debug mode, stash state is complex and may not be stable
	// - Instead, we've already injected all variables into the GLOBAL OBJECT
	// - So the compiler should resolve variables from global scope, not stash
	// IMPORTANT: Use dbg.vm.debugMode to ensure debug symbols are generated for eval
	prog, compileErr := compile("<eval>", expr, false, true, nil, dbg.vm.debugMode, dbg.vm.r.parserOptions...)
	if compileErr != nil {
		// Restore global scope before returning error
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

	// Run the compiled program using the Runtime's RunProgram method
	// This ensures proper context handling and exception management
	var result Value
	var evalErr error

	result, evalErr = dbg.vm.r.RunProgram(prog)
	if evalErr != nil {
		// Check if it's an exception and unwrap it
		if exc, ok := evalErr.(*Exception); ok {
			evalErr = exc
		}
	}

	// 5. Restore global scope
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

	// Create cache key
	cacheKey := fmt.Sprintf("%s:%d:__return_%s", filename, currentLine, varName)

	// Store in cache
	dbg.varValueCache[cacheKey] = value
	dbg.varValueCacheLine = currentLine

	// Also cache under the variable name if we can find its declaration
	if varInfo := dbg.getSourceVarInfo(currentLine); varInfo != nil {
		if _, isLocal := varInfo.locals[varName]; isLocal {
			declLine := varInfo.declLines[varName]
			localCacheKey := fmt.Sprintf("%s:%d:%s", filename, declLine, varName)
			dbg.varValueCache[localCacheKey] = value
		}
	}
}

func (dbg *Debugger) GetLocalVariables() (map[string]Value, error) {
	locals := make(map[string]Value)

	if !dbg.active || dbg.vm.prg == nil {
		return locals, nil
	}

	if dbg.vm.sb < 0 {
		return locals, nil
	}

	if dbg.vm.stash == nil {
		return locals, nil
	}

	// In debug mode, variables are in stash with different scopes
	// Stash level 0 = current function scope (locals + inherited globals)
	// Stash level 1+ = outer scopes (module scope, global scope)

	stashLevel := 0
	stashCount := 0
	for s := dbg.vm.stash; s != nil; s = s.outer {
		stashCount++
		if s.names != nil {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] GetLocalVariables: processing stash level %d with %d variables\n", 
					stashLevel, len(s.names))
			}
			for name, idx := range s.names {
				nameStr := name.String()

				// Ignore stash entries that cannot be valid identifiers (e.g., folder paths).
				if !isIdentifierLike(nameStr) {
					continue
				}

				// Skip if already found in inner scope
				if _, exists := locals[nameStr]; exists {
					continue
				}

				// Skip global builtins at outermost level
				if s.outer == nil && globalBuiltinKeys[nameStr] {
					continue
				}

				actualIdx := idx & uint32(maskIndex)
				isIndirect := (idx & maskIndirect) != 0

				var val Value
				var found bool

				if isIndirect {
					// Indirect variable: stored in THIS stash's values array
					// The actualIdx is the direct index into s.values
					if int(actualIdx) >= 0 && int(actualIdx) < len(s.values) {
						val = s.values[actualIdx]
						// Skip nil values (uninitialized TDZ variables)
						if val != nil && !isNullValue(val) {
							found = true
						}
					}
				} else {
					// Non-indirect variable: look in PARENT stash chain
					nameUni := unistring.String(nameStr)
					for parent := s.outer; parent != nil; parent = parent.outer {
						if parent.names != nil {
							if parentRawIdx, exists := parent.names[nameUni]; exists {
								parentActualIdx := parentRawIdx & 0x00FFFFFF
								if int(parentActualIdx) < len(parent.values) {
									val = parent.values[parentActualIdx]
									if val != nil {
										found = true
										break
									}
								}
							}
						}

						if !found && parent.obj != nil {
							if v := parent.obj.self.getStr(nameUni, nil); v != nil {
								val = v
								found = true
								break
							}
						}
					}
				}

				if found {
					// Determine if this is a function-local or global variable
					// Function locals are in stash level 0, globals are in outer levels
					if stashLevel == 0 {
						// Function-local variable
						locals["__stack_"+nameStr] = val
					} else {
						// Global/module-level variable
						locals[nameStr] = val
					}
				}
			}
		}

		// Also check the stash's object for additional properties
		if s.obj != nil {
			for item, next := s.obj.self.iterateStringKeys()(); next != nil; item, next = next() {
				keyStr := item.name.String()
				if !isIdentifierLike(keyStr) {
					continue
				}
				if _, exists := locals[keyStr]; !exists {
					keyUniStr := unistring.String(keyStr)
					if v := s.obj.self.getStr(keyUniStr, nil); v != nil {
						// Object properties are always global-ish
						locals[keyStr] = v
					}
				}
			}
		}

		stashLevel++
	}
	
	if dbg.enableDebugLogging {
		fmt.Printf("[DEBUGGER] GetLocalVariables: processed %d stash levels, found %d variables\n", 
			stashCount, len(locals))
	}

	return locals, nil
}

func (dbg *Debugger) getValue(varName string) (val Value, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("error getting value: %v", r)
		}
	}()

	if dbg.vm.sb < 0 {
		return nil, fmt.Errorf("cannot access variables during context transition (vm.sb=%d)", dbg.vm.sb)
	}

	if dbg.vm.stash == nil {
		return nil, fmt.Errorf("variable '%s' not accessible (no execution context)", varName)
	}

	// First, try to find in current function's return value cache
	if retVal, found := dbg.returnValueCache[varName]; found {
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] getValue('%s'): Found in return value cache\n", varName)
		}
		return retVal, nil
	}

	// Then, try to find in scope variables
	if scopeVars, hasScope := dbg.scopeVariables[dbg.currentScopeDepth]; hasScope {
		if val, found := scopeVars[varName]; found {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] getValue('%s'): Found in scope variables (depth=%d)\n", varName, dbg.currentScopeDepth)
			}
			return val, nil
		}
	}

	// STRATEGY: Use debug symbols first (most accurate), then stash, then stack analysis
	name := unistring.String(varName)
	
	// 0. First try debug symbols - they have the exact location
	if dbg.vm.prg != nil && dbg.vm.prg.debugSymbols != nil {
		if varLocs, exists := dbg.vm.prg.debugSymbols.scopeMap[dbg.vm.pc]; exists {
			for _, varLoc := range varLocs {
				if varLoc.Name == varName {
					var val Value
					//var found bool
					
					if varLoc.InStash {
						// Variable is in stash - find it in stash chain
						if dbg.vm.stash != nil {
							stashIdx := int(varLoc.StashIdx)
							stashLevel := 0
							for s := dbg.vm.stash; s != nil && stashLevel <= 2; s = s.outer {
								if s.values != nil {
									if stashIdx < len(s.values) {
										val = s.values[stashIdx]
										if val != nil && !isNullValue(val) {
											if dbg.enableDebugLogging {
												fmt.Printf("[DEBUGGER] getValue('%s'): Found in stash level %d, idx %d (from debug symbols)\n", 
													varName, stashLevel, stashIdx)
											}
											return val, nil
										} else {
											if dbg.enableDebugLogging && stashLevel == 0 {
												fmt.Printf("[DEBUGGER] getValue('%s'): Stash idx %d is nil/invalid (val=%v)\n",
													varName, stashIdx, val)
											}
										}
									} else {
										if dbg.enableDebugLogging && stashLevel == 0 {
											fmt.Printf("[DEBUGGER] getValue('%s'): Stash idx %d out of range (len=%d)\n",
												varName, stashIdx, len(s.values))
										}
									}
								}
								stashLevel++
							}
						} else {
							if dbg.enableDebugLogging {
								fmt.Printf("[DEBUGGER] getValue('%s'): No stash available\n", varName)
							}
						}
					} else {
						// Variable is on stack
						// StackIdx from debug symbols: negative for args, positive for locals
						var stackPos int
						if varLoc.IsParam || varLoc.StackIdx < 0 {
							// Argument: StackIdx is negative like -(i+1)
							argNum := -int(varLoc.StackIdx) - 1
							stackPos = dbg.vm.sb + 1 + argNum
						} else {
							// Local variable: try both positions (args in stash vs on stack)
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
							} else {
								if dbg.enableDebugLogging {
									fmt.Printf("[DEBUGGER] getValue('%s'): Stack pos %d exists but val is nil/invalid (val=%v, type=%T)\n",
										varName, stackPos, val, val)
								}
							}
						} else {
							if dbg.enableDebugLogging {
								fmt.Printf("[DEBUGGER] getValue('%s'): Stack pos %d out of range (sb=%d, sp=%d, len=%d, stackIdx=%d, isParam=%v, args=%d)\n",
									varName, stackPos, dbg.vm.sb, dbg.vm.sp, len(dbg.vm.stack), varLoc.StackIdx, varLoc.IsParam, dbg.vm.args)
							}
						}
					}
				}
			}
		} else {
			if dbg.enableDebugLogging {
				fmt.Printf("[DEBUGGER] getValue('%s'): No debug symbols at PC=%d\n", varName, dbg.vm.pc)
			}
		}
	} else {
		if dbg.enableDebugLogging {
			if dbg.vm.prg == nil {
				fmt.Printf("[DEBUGGER] getValue('%s'): No program available\n", varName)
			} else if dbg.vm.prg.debugSymbols == nil {
				fmt.Printf("[DEBUGGER] getValue('%s'): WARNING - No debug symbols available! (debugMode=%v)\n", 
					varName, dbg.vm.debugMode)
			}
		}
	}

	// 1. Check stash chain - this is the most reliable source
	stashLevel := 0
	for s := dbg.vm.stash; s != nil; s = s.outer {
		// Check names map
		if s.names != nil {
			if idx, exists := s.names[name]; exists {
				actualIdx := idx & uint32(maskIndex)
				isIndirect := (idx & maskIndirect) != 0

				if isIndirect {
					// Indirect variable: stored in THIS stash's values array
					// The actualIdx is the direct index into s.values for indirect variables
					if int(actualIdx) >= 0 && int(actualIdx) < len(s.values) {
						val := s.values[actualIdx]
						// Skip nil values (uninitialized TDZ variables)
						if val != nil && !isNullValue(val) {
							if dbg.enableDebugLogging {
								fmt.Printf("[DEBUGGER] getValue('%s'): Found indirect in stash level %d, idx=%d\n", varName, stashLevel, actualIdx)
							}
							return val, nil
						} else if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] getValue('%s'): Indirect variable at idx %d is nil/uninitialized (TDZ)\n", varName, actualIdx)
						}
					} else {
						if dbg.enableDebugLogging {
							fmt.Printf("[DEBUGGER] getValue('%s'): Indirect idx %d out of range (len=%d) at stash level %d\n", 
								varName, actualIdx, len(s.values), stashLevel)
						}
					}
				} else {
					// Non-indirect variable: look in parent stash chain
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
							if v := parent.obj.self.getStr(name, nil); v != nil {
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

		// Check object properties
		if s.obj != nil {
			if v := s.obj.self.getStr(name, nil); v != nil {
				if dbg.enableDebugLogging {
					fmt.Printf("[DEBUGGER] getValue('%s'): Found in object properties\n", varName)
				}
				return v, nil
			}
		}

		stashLevel++
	}

	// 2. Check global builtins
	if globalBuiltinKeys[varName] {
		if globalObj := dbg.vm.r.globalObject; globalObj != nil {
			if v := globalObj.self.getStr(name, nil); v != nil {
				if dbg.enableDebugLogging {
					fmt.Printf("[DEBUGGER] getValue('%s'): Found in global builtins\n", varName)
				}
				return v, nil
			}
		}
	}

	// 3. Try stack-based lookup using source analysis (for locals not yet in stash)
	currentLine := dbg.Line()
	if varInfo := dbg.getSourceVarInfo(currentLine); varInfo != nil {
		// Check parameters first
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

		// Check local variables
		if localIdx, isLocal := varInfo.locals[varName]; isLocal {
			// Verify variable has been declared
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

	// 4. FALLBACK: Try global registry for cross-phase variables
	if registry := GetGlobalRegistry(); registry != nil {
		// Try to find variable in init stash or other phases
		if dbg.enableDebugLogging {
			fmt.Printf("[DEBUGGER] getValue('%s'): Trying global registry for cross-phase lookup\n", varName)
		}
		
		// Use a simple eval through the registry with panic recovery
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

// Helper function to check if a value is null or undefined
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

// Helper function to check if a value is a function object
func isFunctionValue(v Value) bool {
	if v == nil {
		return false
	}
	// Check if it's a function/callable object
	if obj, ok := v.(*Object); ok {
		_, isCallable := obj.self.assertCallable()
		return isCallable
	}
	return false
}



func (dbg *Debugger) GetCallStack() ([]StackFrame, error) {
	frames := make([]StackFrame, 0, len(dbg.vm.callStack))

	for i, frame := range dbg.vm.callStack {
		frameInfo := StackFrame{
			Index:    i,
			pc:       frame.pc,
			funcName: "unknown",
			File:     dbg.Filename(),
			Line:     dbg.Line(),
		}

		// Try to get function name
		if frame.prg != nil && frame.prg.funcName != "" {
			frameInfo.funcName = frame.prg.funcName
		}

		frames = append(frames, frameInfo)
	}

	return frames, nil
}

// SetInitRuntime stores a reference to the init VM for cross-VM variable access
func (dbg *Debugger) SetInitRuntime(rt *Runtime) {
	dbg.initRuntime = rt
}

// SetSetupData stores the return value from setup() for access in VU/teardown
func (dbg *Debugger) SetSetupData(data Value) {
	dbg.setupData = data
}
