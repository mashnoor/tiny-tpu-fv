
## 1. System Architecture

### 1.1 High-Level Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        LLM-Deadlock Detection Framework                     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────┐    ┌──────────────────────┐    ┌─────────────────────┐   │
│  │   RTL       │    │  Structural          │    │  Pattern            │   │
│  │   Input     │───▶│  Analysis            │───▶│  Recognition        │   │
│  │  (.sv files)│    │  (AST + DAG)         │    │  (LLM + Vector DB)  │   │
│  └─────────────┘    └──────────────────────┘    └─────────────────────┘   │
│                                                          │                  │
│                                                          ▼                  │
│  ┌─────────────┐    ┌──────────────────────┐    ┌─────────────────────┐   │
│  │  Generated  │    │  Context             │    │  Assertion          │   │
│  │  Assertions │◀───│  Accumulation        │◀───│  Generation         │   │
│  │  (.sv)      │    │  (Resource Lock)     │    │  (LLM)              │   │
│  └─────────────┘    └──────────────────────┘    └─────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```



## 2. Step 1: RTL Pre-processing and AST Extraction


- Parse SystemVerilog files to extract structural information
- Identify modules, ports, signals, and their relationships
- Extract Finite State Machines (FSMs) 

### 2.2 AST Representation

```python
@dataclass
class SVModule:
    name: str
    ports: List[SVPort]
    signals: List[SVSignal]
    instances: List[ModuleInstance]
    always_blocks: List[AlwaysBlock]
    fsms: List[FSM] 
    interfaces: List[HandshakeInterface]  

@dataclass
class FSM:
    name: str
    state_variable: str
    states: List[State]
    transitions: List[Transition]
    is_wait_state: Dict[str, bool]  

```

### Tools for AST Extraction

**Custom parser** using tree-sitter 

### 2.4 FSM Extraction Algorithm

```
For each always_ff block:
    1. Identify state register (updated on clock edge)
    2. Extract state encoding (case statement, if-else chain)
    3. Build state transition graph
    4. Detect terminal states (no outgoing transitions)
    5. Mark "wait" states (states with conditional wait on signals)
```

---

## Structural Breakdown with Resource Dependency Graph

### 3.1 Data Structures

#### 3.1.1 Core Graph Structure

```python


class NodeType(Enum):
    MODULE = "module"
    FIFO = "fifo"
    ARBITER = "arbiter"
    FSM = "fsm"
    STATE = "state"
    HANDSHAKE = "handshake"
    RESOURCE = "resource"  

class EdgeType(Enum):
    DATA_FLOW = "data_flow"
    CONTROL_FLOW = "control_flow"
    REQUEST_GRANT = "request_grant"
    VALID_READY = "valid_ready"
    CREDIT = "credit"
    DEPENDENCY = "dependency"

@dataclass
class GraphNode:
    id: str
    type: NodeType
    name: str
    attributes: Dict[str, any] = field(default_factory=dict)
    is_terminal: bool = False
    is_wait_state: bool = False

@dataclass
class GraphEdge:
    source: str 
    destination: str 
    type: EdgeType
    signals: List[str] = field(default_factory=list)
    is_cycle_causing: bool = False

@dataclass
class ResourceDependencyGraph:

    nodes: Dict[str, GraphNode] = field(default_factory=dict)
    edges: Dict[str, List[GraphEdge]] = field(default_factory=dict)
    adjacency_list: Dict[str, Set[str]] = field(default_factory=dict)
    reverse_adjacency: Dict[str, Set[str]] = field(default_factory=dict)

    cycles: List[List[str]] = field(default_factory=list)

    hierarchy_levels: Dict[str, int] = field(default_factory=dict)

    topological_order: List[str] = field(default_factory=list)
```

#### Context Accumulation 

```python
@dataclass
class ResourceLock:
    resource_id: str
    locked_by: Optional[str] 
    lock_type: str 
    waiting_queue: List[str] 
    grant_signal: str  

@dataclass
class DeadlockContext:
    resource_locks: Dict[str, ResourceLock] = field(default_factory=dict)
    pending_requests: Dict[str, List[str]] = field(default_factory=dict)
    analyzed_modules: Set[str] = field(default_factory=set)
    deadlock_patterns: List[DeadlockPattern] = field(default_factory=list)

@dataclass
class DeadlockPattern:
    pattern_type: str 
    involved_modules: List[str]
    involved_resources: List[str]
    cycle_path: List[str]
    confidence: float
```

### Graph Construction Algorithm

```
Input: AST from Step 1
Output: ResourceDependencyGraph

1. Create nodes for:
   - Each module instance
   - Each FSM state
   - Each handshake interface (valid/ready, req/grant)
   - Each shared resource (memory, bus, FIFO)

2. Create edges for:
   - Data flow: module output → module input
   - Control flow: FSM state transitions
   - Request paths: request → arbiter → grant
   - Valid/Ready: valid → ready acknowledgment

3. Build adjacency lists:
   - Forward: which nodes this node affects
   - Reverse: which nodes affect this node

4. Compute hierarchy levels (BFS from top-level)

5. Detect cycles:
   - Use Tarjan's SCC algorithm
   - Mark edges that participate in cycles
   - Each potential cycle is a deadlock candidate
```

### 3.3 Cycle Detection for Deadlocks

```python
def detect_deadlock_cycles(rdg: ResourceDependencyGraph) -> List[List[str]]:
    """
    Find cycles in the resource dependency graph.
    Unlike LLM-IFT (which uses DAG), deadlocks require cycle detection.
    """
    cycles = []

    # Tarjan's Strongly Connected Components
    def dfs(node: str, visited: Set, rec_stack: List, path: List):
        visited.add(node)
        rec_stack.append(node)

        for neighbor in rdg.adjacency_list.get(node, []):
            if neighbor not in visited:
                dfs(neighbor, visited, rec_stack, path + [neighbor])
            elif neighbor in rec_stack:
                # Found a cycle
                cycle_start = rec_stack.index(neighbor)
                cycle = rec_stack[cycle_start:] + [neighbor]
                cycles.append(cycle)

        rec_stack.pop()

    for node in rdg.nodes:
        if node not in visited:
            dfs(node, set(), [], [])

    return cycles
```

---

### Deadlock Pattern Categories

| Pattern | Description | Detection Signature |
|---------|-------------|---------------------|
| **Circular Wait** | Cycle in resource allocation graph | Module A waits for B, B waits for A |
| **Hold and Wait** | Holding resources while waiting for others | Has lock + pending request |
| **Signal Stuck** | Control signal never de-asserts | Signal stays high indefinitely |
| **Credit Starvation** | Credit counter reaches zero | Credits exhausted, no replenishment |
| **FIFO Full/Empty** | Buffer stuck in full or empty state | Pointer stalls, backpressure |
| **Terminal State Lock** | FSM stuck in non-wait terminal state | No outgoing transitions |
| **Handshake Mismatch** | Valid without ready, or ready without valid | Protocol violation |

### Two Vector Databases

#### Vector DB 1: Code Pattern Database

```python
@dataclass
class CodePattern:
    pattern_id: str
    pattern_type: str  
    code_snippet: str  
    embedding: List[float] 
    description: str
    assertion_template: str 
    language: str = "systemverilog"

]
```

#### 4.2.2 Vector DB 2: Module Context Database

```python
@dataclass
class ModuleContext:
    module_name: str
    embedding: List[float]  
    interface_summary: str
    fsm_summary: str
    deadlock_risk_score: float
    previously_generated_assertions: List[str]

```

### 4.3 Vector DB Usage

1. **Pattern Matching**:
   - Embed code fragments from AST
   - Query against Code Pattern DB
   - Find similar deadlock patterns

2. **Context Retrieval**:
   - When analyzing module, query similar modules
   - Retrieve their deadlock risks and assertions
   - Use as few-shot examples for LLM

3. **Embedding Model**:
   - Use code-specific embeddings (CodeBERT, GraphCodeBERT)
   - Or fine-tune embeddings on SystemVerilog corpus

### LLM Prompting Strategy

#### Divide and Conquer (from LLM-IFT)

```python
def analyze_module_for_deadlock(
    module: SVModule,
    rdg: ResourceDependencyGraph,
    context: DeadlockContext,
    similar_patterns: List[CodePattern]
) -> ModuleDeadlockAnalysis:

    # 1. Get ancestor modules (like LLM-IFT's P(Mi))
    ancestors = get_ancestors(module.name, rdg)

    # 2. Get dependent modules
    descendants = get_descendants(module.name, rdg)

    # 3. Build prompt
    prompt = f"""
    You are analyzing a hardware module for deadlock patterns.

    Module: {module.name}
    Ancestors (modules that affect this): {ancestors}
    Descendants (modules affected by this): {descendants}

    Similar Deadlock Patterns Found:
    {format_patterns(similar_patterns)}

    Module Code:
    {module.code}

    FSM Information:
    {format_fsms(module.fsms)}

    Handshake Interfaces:
    {format_interfaces(module.interfaces)}

    Current Resource Lock State:
    {format_lock_state(context.resource_locks)}

    Task: Identify potential deadlock patterns in this module.
    For each pattern, specify:
    1. Pattern type
    2. Involved signals
    3. Cycle path (if circular wait)
    4. SVA assertion to detect it

    Output JSON format:
    {{
        "deadlock_patterns": [
            {{
                "type": "circular_wait" | "signal_stuck" | "credit_starvation" | ...,
                "signals": ["sig1", "sig2"],
                "description": "...",
                "assertion": "// SVA code here",
                "confidence": 0.0-1.0
            }}
        ],
        "resource_updates": {{
            "locked_resources": ["res1"],
            "waiting_for": ["res2"]
        }}
    }}
    """
```

#### 4.4.2 System Prompt for Deadlock Detection

```python
SYSTEM_PROMPT = """
You are an expert hardware verification engineer specializing in deadlock detection.

Deadlock Patterns to Identify:
1. **Circular Wait**: Module A waits for B, B waits for A
2. **Hold and Wait**: Holding resource while waiting for another
3. **Signal Stuck**: Control signal (valid, ready, grant) stuck high/low
4. **Credit Starvation**: Credit counter exhausted, never replenished
5. **Terminal State Lock**: FSM stuck in non-wait state
6. **FIFO Deadlock**: Pointer stuck, full/empty flags incorrect
7. **Handshake Mismatch**: Valid/ready or request/grant protocol violation

For each deadlock pattern, generate SystemVerilog assertions following:
- Use `property` for reusable patterns
- Use `assert property` for checking
- Include `disable iff (rst)` for reset handling
- Use `##[1:N]` for bounded liveness (eventually)
- Use `|->` for implication, `|=>` for next-cycle implication

Example assertion template:
```systemverilog
property signal_must_deassert(clk, rst, signal, bound):
    @(posedge clk) disable iff (rst)
    signal |-> ##[1:bound] !signal;
endproperty
```

Always output valid JSON structure.
"""
```

---

## Response Integration and SVA Generation

### 5.1 Integration Algorithm

```python
def integrate_deadlock_analysis(
    module_analyses: List[ModuleDeadlockAnalysis],
    rdg: ResourceDependencyGraph,
    context: DeadlockContext
) -> DeadlockReport:


    # 1. Aggregate all deadlock patterns
    all_patterns = []
    for analysis in module_analyses:
        all_patterns.extend(analysis.deadlock_patterns)

    # 2. Detect cross-module cycles
    cross_module_cycles = detect_inter_module_cycles(rdg, context)

    # 3. For each cycle, generate liveness property
    liveness_assertions = []
    for cycle in cross_module_cycles:
        liveness_assertions.append(generate_liveness_property(cycle))

    # 4. Generate per-module assertions
    per_module_assertions = {}
    for analysis in module_analyses:
        per_module_assertions[analysis.module_name] = [
            pattern.assertion for pattern in analysis.deadlock_patterns
        ]

    # 5. Generate final LLM prompt for cross-cutting concerns
    global_prompt = f"""
    Synthesize the following deadlock analysis into a comprehensive report.

    Detected Cycles (Cross-module deadlocks):
    {format_cycles(cross_module_cycles)}

    Per-module Deadlock Patterns:
    {format_module_patterns(all_patterns)}

    Generate:
    1. Liveness properties for each cycle
    2. Fairness constraints
    3. Cover properties to hit deadlock states
    4. Assume properties for environment constraints

    Output JSON format:
    {{
        "has_deadlock": true/false,
        "deadlock_paths": [...],
        "liveness_properties": ["// SVA code"],
        "fairness_properties": ["// SVA code"],
        "cover_properties": ["// SVA code"],
        "assume_properties": ["// SVA code"]
    }}
    """

    final_analysis = llm_call(global_prompt)

    return DeadlockReport(
        has_deadlock=final_analysis["has_deadlock"],
        deadlock_paths=final_analysis["deadlock_paths"],
        assertions=AssertionBundle(
            liveness=final_analysis["liveness_properties"],
            fairness=final_analysis["fairness_properties"],
            cover=final_analysis["cover_properties"],
            assume=final_analysis["assume_properties"]
        ),
        per_module=per_module_assertions
    )
```
