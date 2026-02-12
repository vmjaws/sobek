package sobek

import (
	"fmt"
	"sort"
	"sync"
	"unicode"

	"github.com/grafana/sobek/unistring"
)

// DebuggerRegistry is a global singleton that tracks all VM instances and their stashes
// across k6's lifecycle boundaries (init, setup, VU, teardown)
type DebuggerRegistry struct {
	mu sync.RWMutex

	// VMs registered by phase
	initVM      *Runtime
	setupVM     *Runtime
	vuVMs       map[uint64]*Runtime // keyed by VU ID
	teardownVM  *Runtime
	handleSummaryVM  *Runtime

	// Stash data extracted from each phase
	initStash      map[string]Value  // Variables from init context
	setupData      Value             // Return value from setup()
	globalVars     map[string]Value  // Global object snapshot

	// Phase tracking
	currentPhase   string

	// Debug logging
	enableLogging  bool
}

var (
	globalRegistry     *DebuggerRegistry
	globalRegistryOnce sync.Once
)

// GetGlobalRegistry returns the singleton debugger registry
func GetGlobalRegistry() *DebuggerRegistry {
	globalRegistryOnce.Do(func() {
		globalRegistry = &DebuggerRegistry{
			vuVMs:         make(map[uint64]*Runtime),
			initStash:     make(map[string]Value),
			globalVars:    make(map[string]Value),
			enableLogging: true,
		}
	})
	return globalRegistry
}

// Phase constants
const (
	PhaseInit     = "init"
	PhaseSetup    = "setup"
	PhaseVU       = "vu"
	PhaseTeardown = "teardown"
	PhaseHandleSummary = "handleSummary"
)

// RegisterVM registers a VM for a specific phase
func (dr *DebuggerRegistry) RegisterVM(phase string, vuID uint64, rt *Runtime) {
	dr.mu.Lock()
	defer dr.mu.Unlock()

	if dr.enableLogging {
		fmt.Printf("[REGISTRY] Registering VM for phase=%s, vuID=%d\n", phase, vuID)
	}

	dr.currentPhase = phase

	switch phase {
	case PhaseInit:
		dr.initVM = rt
		dr.extractInitStash(rt)
	case PhaseSetup:
		dr.setupVM = rt
	case PhaseVU:
		dr.vuVMs[vuID] = rt
	case PhaseTeardown:
		dr.teardownVM = rt
	case PhaseHandleSummary:
		dr.handleSummaryVM = rt
	}
}

// extractInitStash extracts closure variables from the init phase stash
// These are variables that VU functions will reference but are allocated in init
func (dr *DebuggerRegistry) extractInitStash(rt *Runtime) {
	if rt == nil {
		if dr.enableLogging {
			fmt.Printf("[REGISTRY] extractInitStash: runtime is nil\n")
		}
		return
	}

	// Get debugger to access stash safely
	dbg := rt.GetDebugger()
	if dbg == nil {
		if dr.enableLogging {
			fmt.Printf("[REGISTRY] extractInitStash: no debugger attached\n")
		}
		return
	}

	// Extract variables using debugger's GetLocalVariables which safely accesses stash
	vars, err := dbg.GetLocalVariables()
	if err != nil {
		if dr.enableLogging {
			fmt.Printf("[REGISTRY] extractInitStash: GetLocalVariables failed: %v\n", err)
		}
		return
	}

	// Store all init variables
	for name, value := range vars {
		dr.initStash[name] = value
	}

	// Also capture global object variables
	dr.extractGlobalVariables(rt)

	if dr.enableLogging {
		fmt.Printf("[REGISTRY] Extracted %d init stash variables, %d global variables\n",
			len(dr.initStash), len(dr.globalVars))
	}
}


// extractGlobalVariables captures variables from the global object
func (dr *DebuggerRegistry) extractGlobalVariables(rt *Runtime) {
	globalObj := rt.GlobalObject()
	if globalObj == nil {
		return
	}

	// Global variables are already captured via stash extraction
	// This function is kept for potential future enhancements
	// where we might need to iterate global object properties directly
}

// SetSetupData stores the return value from setup() function
func (dr *DebuggerRegistry) SetSetupData(data Value) {
	dr.mu.Lock()
	defer dr.mu.Unlock()

	dr.setupData = data

	if dr.enableLogging {
		fmt.Printf("[REGISTRY] Stored setup data: %v\n", data)
	}
}


// isBuiltinGlobal checks if a name is a built-in JavaScript global
func isBuiltinGlobal(name string) bool {
	builtins := map[string]bool{
		"Object": true, "Array": true, "String": true, "Number": true, "Boolean": true,
		"Function": true, "Error": true, "EvalError": true, "RangeError": true,
		"ReferenceError": true, "SyntaxError": true, "TypeError": true, "URIError": true,
		"Date": true, "RegExp": true, "Math": true, "JSON": true,
		"parseInt": true, "parseFloat": true, "isNaN": true, "isFinite": true,
		"decodeURI": true, "decodeURIComponent": true, "encodeURI": true, "encodeURIComponent": true,
		"escape": true, "unescape": true, "eval": true,
		"undefined": true, "NaN": true, "Infinity": true,
		"Promise": true, "Proxy": true, "Reflect": true,
		"Symbol": true, "Map": true, "Set": true, "WeakMap": true, "WeakSet": true,
		"ArrayBuffer": true, "DataView": true, "Int8Array": true, "Uint8Array": true,
		"Uint8ClampedArray": true, "Int16Array": true, "Uint16Array": true,
		"Int32Array": true, "Uint32Array": true, "Float32Array": true, "Float64Array": true,
		"console": true, "globalThis": true,
	}
	return builtins[name]
}

// MultiScopeEval evaluates an expression by searching across all registered VMs
// This solves the cross-VM variable resolution problem
func (dr *DebuggerRegistry) MultiScopeEval(currentVM *Runtime, expr string) (Value, error) {
	dr.mu.RLock()
	defer dr.mu.RUnlock()

	if dr.enableLogging {
		fmt.Printf("[REGISTRY] MultiScopeEval: expr=%s, phase=%s\n", expr, dr.currentPhase)
	}

	// Collect variables from all sources
	varMap := make(map[string]Value)

	// 1. Get ALL globals from init VM (if available)
	if dr.initVM != nil {
		globalObj := dr.initVM.GlobalObject()
		if globalObj != nil {
			// Try to extract ALL properties from global object with safety checks
			func() {
				defer func() {
					if r := recover(); r != nil {
						// Silently recover from panics during property iteration
						if dr.enableLogging {
							fmt.Printf("[REGISTRY] MultiScopeEval: recovered from panic during global iteration: %v\n", r)
						}
					}
				}()
				
				for item, next := globalObj.self.iterateStringKeys()(); next != nil; item, next = next() {
					keyStr := item.name.String()
					
					// Skip built-in globals and module-related identifiers
					if isBuiltinGlobal(keyStr) || keyStr == "module" || keyStr == "exports" {
						continue
					}
					
					// Safely get the property value with panic recovery
					func() {
						defer func() {
							if r := recover(); r != nil {
								// Skip properties that cause errors
								if dr.enableLogging {
									fmt.Printf("[REGISTRY] MultiScopeEval: skipping property '%s' due to error: %v\n", keyStr, r)
								}
							}
						}()
						
						nameUni := unistring.String(keyStr)
						if val := globalObj.self.getStr(nameUni, nil); val != nil && !isNullValue(val) {
							varMap[keyStr] = val
							if dr.enableLogging {
								fmt.Printf("[REGISTRY] MultiScopeEval: extracted init global '%s'\n", keyStr)
							}
						}
					}()
				}
			}()
		}
		
		// Also extract from init VM's stash if debugger is available
		if dbg := dr.initVM.GetDebugger(); dbg != nil {
			if locals, err := dbg.GetLocalVariables(); err == nil {
				for name, value := range locals {
					// Skip nil or uninitialized values
					if value == nil || isNullValue(value) {
						continue
					}
					
					// Strip __stack_ prefix if present
					actualName := name
					if len(name) > 8 && name[:8] == "__stack_" {
						actualName = name[8:]
					}
					// Don't overwrite if already have it
					if _, exists := varMap[actualName]; !exists {
						varMap[actualName] = value
						if dr.enableLogging {
							fmt.Printf("[REGISTRY] MultiScopeEval: extracted init stash var '%s'\n", actualName)
						}
					}
				}
			}
		}
	}

	// 2. Setup data (if in VU or teardown phase)
	if dr.currentPhase == PhaseVU || dr.currentPhase == PhaseTeardown || dr.currentPhase == PhaseHandleSummary {
		if dr.setupData != nil {
			varMap["data"] = dr.setupData
		}
	}

	// 3. Current VM variables (locals override everything)
	if currentVM != nil {
		dbg := currentVM.GetDebugger()
		if dbg != nil {
			locals, err := dbg.GetLocalVariables()
			if err == nil {
				for name, value := range locals {
					// Skip nil or uninitialized values to avoid TDZ errors
					if value == nil || isNullValue(value) {
						if dr.enableLogging {
							fmt.Printf("[REGISTRY] MultiScopeEval: skipping nil/uninitialized var '%s'\n", name)
						}
						continue
					}
					
					// Local variables are prefixed with __stack_ - strip the prefix
					if len(name) > 8 && name[:8] == "__stack_" {
						actualName := name[8:] // Strip the __stack_ prefix
						varMap[actualName] = value
					} else {
						// Global variables have no prefix
						varMap[name] = value
					}
				}
			}
		}
	}

	if dr.enableLogging {
		fmt.Printf("[REGISTRY] MultiScopeEval: collected %d variables\n", len(varMap))
		for name := range varMap {
			fmt.Printf("[REGISTRY]   - %s\n", name)
		}
	}

	// Use current VM to evaluate with injected variables
	if currentVM == nil {
		return nil, fmt.Errorf("no current VM available for evaluation")
	}

	return dr.evaluateWithVariables(currentVM, expr, varMap)
}

// isValidIdentifier checks if a string is a valid JavaScript identifier
func isValidIdentifier(name string) bool {
	if name == "" {
		return false
	}
	// Disallow a handful of reserved keywords that would break parameter lists.
	switch name {
	case "let", "const", "var", "function", "class", "import", "export":
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

// evaluateWithVariables evaluates expression in the given VM with variables injected
func (dr *DebuggerRegistry) evaluateWithVariables(rt *Runtime, expr string, vars map[string]Value) (Value, error) {
	// Instead of injecting into global scope (which causes TDZ issues with let/const),
	// we wrap the expression in a function that accepts the variables as parameters
	// This avoids "Lexical declaration for an unbound name" compiler errors

	// Filter, deduplicate, and order parameter names to avoid invalid/duplicate identifiers.
	paramSeen := make(map[string]struct{})
	paramNames := make([]string, 0, len(vars))
	for name := range vars {
		if !isValidIdentifier(name) {
			continue
		}
		if _, exists := paramSeen[name]; exists {
			continue
		}
		paramSeen[name] = struct{}{}
		paramNames = append(paramNames, name)
	}
	sort.Strings(paramNames)

	// If nothing survived filtering, evaluate directly.
	if len(paramNames) == 0 {
		// No variables to inject, evaluate directly
		var result Value
		var evalErr error
		
		func() {
			defer func() {
				if r := recover(); r != nil {
					evalErr = fmt.Errorf("evaluation panicked: %v", r)
				}
			}()
			
			prog, compileErr := compile("<eval>", expr, false, true, nil, false, rt.parserOptions...)
			if compileErr != nil {
				evalErr = fmt.Errorf("compilation error: %w", compileErr)
				return
			}

			result, evalErr = rt.RunProgram(prog)
			if evalErr != nil {
				if exc, ok := evalErr.(*Exception); ok {
					evalErr = exc
				}
			}
		}()
		
		return result, evalErr
	}
	
	// Build a wrapper function that declares all variables as parameters
	// This creates a proper scope without TDZ issues
	var paramValues []Value
	for _, name := range paramNames {
		paramValues = append(paramValues, vars[name])
	}

	// Create wrapper: (function(var1, var2, ...) { return EXPR; })(val1, val2, ...)
	wrapperCode := "(function(" + paramNames[0]
	for i := 1; i < len(paramNames); i++ {
		wrapperCode += ", " + paramNames[i]
	}
	wrapperCode += ") { return (" + expr + "); })"
	
	var result Value
	var evalErr error
	
	func() {
		defer func() {
			if r := recover(); r != nil {
				evalErr = fmt.Errorf("evaluation panicked: %v", r)
			}
		}()
		
		// Compile the wrapper function
		prog, compileErr := compile("<eval>", wrapperCode, false, true, nil, false, rt.parserOptions...)
		if compileErr != nil {
			evalErr = fmt.Errorf("compilation error: %w", compileErr)
			return
		}

		// Run to get the function
		wrapperFn, runErr := rt.RunProgram(prog)
		if runErr != nil {
			if exc, ok := runErr.(*Exception); ok {
				evalErr = exc
			} else {
				evalErr = fmt.Errorf("wrapper evaluation error: %w", runErr)
			}
			return
		}
		
		// Call the function with the variable values
		fnObj, ok := wrapperFn.(*Object)
		if !ok {
			evalErr = fmt.Errorf("wrapper is not a function")
			return
		}
		
		callable, ok := fnObj.self.assertCallable()
		if !ok {
			evalErr = fmt.Errorf("wrapper is not callable")
			return
		}
		
		result = callable(FunctionCall{
			This:      rt.GlobalObject(),
			Arguments: paramValues,
		})
		
		// callable panics on exceptions; they are recovered in the outer defer above
	}()

	return result, evalErr
}

// GetPhase returns the current execution phase
func (dr *DebuggerRegistry) GetPhase() string {
	dr.mu.RLock()
	defer dr.mu.RUnlock()
	return dr.currentPhase
}

// Reset clears all registry data (useful for testing)
func (dr *DebuggerRegistry) Reset() {
	dr.mu.Lock()
	defer dr.mu.Unlock()

	dr.initVM = nil
	dr.setupVM = nil
	dr.vuVMs = make(map[uint64]*Runtime)
	dr.teardownVM = nil
	dr.handleSummaryVM = nil
	dr.initStash = make(map[string]Value)
	dr.globalVars = make(map[string]Value)
	dr.setupData = nil
	dr.currentPhase = ""
}
