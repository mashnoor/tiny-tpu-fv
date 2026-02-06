# LLM-Deadlock: LLM-Guided Hardware Deadlock Detection
---

## High-Level Flow

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                      LLM-Deadlock Framework                                  │
├──────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌──────────────┐    ┌───────────────────┐    ┌──────────────────────────┐  │
│  │  RTL Input   │    │  Resource          │    │  LLM Engine              │  │
│  │  (.sv files) │───▶│  Dependency Graph  │───▶│  + Vector DB             │  │
│  │  AST Parse   │    │  + Cycle Detection │    │  (per-module analysis)   │  │
│  └──────────────┘    └───────────────────┘    └──────────────────────────┘  │
│     Step 1               Step 2                      Step 3                  │
│                                                        │                     │
│                                                        ▼                     │
│                          ┌───────────────────────────────────────────────┐   │
│                          │  SVA Assertion Generation                     │   │
│                          │  (Liveness + Safety + Fairness + Cover)       │   │
│                          └───────────────────────────────────────────────┘   │
│                                        Step 4                                │
└──────────────────────────────────────────────────────────────────────────────┘
```

### Four Steps

| Step | Name                          | What It Does                                                       |
|------|-------------------------------|--------------------------------------------------------------------|
| 1    | RTL Pre-processing            | Parse SystemVerilog AST, extract modules, FSMs, handshake signals  |
| 2    | Resource Dependency Graph     | Build graph with cycle detection (Tarjan's SCC), not just a DAG    |
| 3    | LLM Engine + Vector DB        | Per-module deadlock analysis in topological order, pattern matching |
| 4    | SVA Assertion Generation      | Generate liveness/safety/fairness/cover SVA properties             |

---

## Step 1: RTL Pre-processing & AST Extraction

```
┌────────────────┐         ┌────────────────────────────────────────┐
│  SystemVerilog │         │  Extracted:                            │
│  Design Files  │────────▶│  - Module definitions + hierarchy      │
│  (.sv)         │  tree-  │  - Handshake interfaces (valid/ready,  │
│                │  sitter │    req/ack, credit-based)              │
└────────────────┘         │  - FSM state machines                  │
                           │  - Shared resources (memory, bus)      │
                           └────────────────────────────────────────┘
```

### Parser: tree-sitter with SystemVerilog Grammar

```
tree-sitter AST
     │
     ├── module_declaration ──▶ SVModule
     │     ├── port_declaration ──▶ SVPort
     │     ├── net_declaration / data_declaration ──▶ SVSignal
     │     ├── always_construct ──▶ AlwaysBlock
     │     │     └── case_statement ──▶ FSM detection
     │     └── module_instantiation ──▶ ModuleInstance
     │
     └── Walk tree, pattern-match on node types
```

### Key Extraction Targets

```
1. Handshake Interfaces
   ─────────────────────
   Pattern-match port names:
     valid + ready  →  ValidReadyInterface
     req   + ack    →  ReqAckInterface
     req   + grant  →  ReqGrantInterface
     credit_*       →  CreditInterface

2. FSMs
   ────
   Detect in always_ff blocks:
     case(state) → state variable found
     Extract states from case items
     Extract transitions from next-state assignments
     Mark "wait" states (conditional on external signals)
     Mark terminal states (no outgoing transitions)

3. Shared Resources
   ─────────────────
   Memory arrays:  reg [W-1:0] name [0:D-1]
   Multiple writers to same signal/memory
   Arbiter patterns: priority encoders, round-robin
```

### AST Data Structures

```python
@dataclass
class SVPort:
    name: str
    direction: str            # "input" | "output" | "inout"
    width: int
    is_handshake: bool
    handshake_role: str       # "valid" | "ready" | "req" | "ack" | "grant" | "credit" | None

@dataclass
class SVSignal:
    name: str
    width: int
    is_memory: bool           # True if array (e.g. reg [7:0] mem [0:127])
    memory_depth: int
    writers: List[str]        # list of always blocks / modules that write to this

@dataclass
class FSMState:
    name: str
    encoding: int
    is_wait_state: bool       # blocked on external signal
    is_terminal: bool         # no outgoing transitions
    wait_signals: List[str]   # signals this state waits on

@dataclass
class FSMTransition:
    from_state: str
    to_state: str
    condition: str            # transition guard expression

@dataclass
class FSM:
    state_variable: str
    states: List[FSMState]
    transitions: List[FSMTransition]

@dataclass
class HandshakeInterface:
    type: str                 # "valid_ready" | "req_ack" | "req_grant" | "credit"
    sender_signal: str        # e.g. "valid", "req"
    receiver_signal: str      # e.g. "ready", "ack", "grant"
    data_signals: List[str]

@dataclass
class ModuleInstance:
    module_name: str
    instance_name: str
    port_connections: Dict[str, str]   # formal → actual

@dataclass
class SVModule:
    name: str
    ports: List[SVPort]
    signals: List[SVSignal]
    instances: List[ModuleInstance]
    always_blocks: List[str]           # raw code blocks
    fsms: List[FSM]
    interfaces: List[HandshakeInterface]
    shared_resources: List[SVSignal]   # signals with multiple writers
```

### FSM Extraction Algorithm

```
For each always_ff / always @(posedge clk) block:
  1. Find case statement → candidate state variable
  2. For each case item:
     a. Extract state name/encoding
     b. Find next-state assignment → transition edge
     c. Check if transition is guarded by external signal → wait state
     d. Check if no next-state assignment → terminal state
  3. Build directed state transition graph
  4. Detect:
     - Terminal states (no outgoing edges)
     - Wait states (outgoing edge gated by signal from another module)
     - Self-loops (state stays unless condition met)
```

---

## Step 2: Resource Dependency Graph + Cycle Detection


```
   Module A ──(valid)──▶ Module B
      ▲                     │
      │                     │
   (ready)              (valid)
      │                     │
      └──── Module C ◀──────┘

   Cycle: A → B → C → A  (potential deadlock)
```

### Graph Data Structures

```python
class NodeType(Enum):
    MODULE     = "module"
    FSM_STATE  = "fsm_state"
    HANDSHAKE  = "handshake"
    RESOURCE   = "resource"       # shared memory, bus
    FIFO       = "fifo"
    ARBITER    = "arbiter"

class EdgeType(Enum):
    VALID_READY    = "valid_ready"
    REQ_ACK        = "req_ack"
    REQ_GRANT      = "req_grant"
    CREDIT         = "credit"
    DATA_FLOW      = "data_flow"
    CONTROL_FLOW   = "control_flow"
    RESOURCE_LOCK  = "resource_lock"

@dataclass
class GraphNode:
    id: str
    type: NodeType
    name: str
    module: str                    # parent module name
    attributes: Dict[str, Any]
    is_blocking: bool = False      # can this node stall?

@dataclass
class GraphEdge:
    source: str
    destination: str
    type: EdgeType
    signals: List[str]             # signals involved in this edge
    can_block: bool = False        # can this edge cause backpressure?

@dataclass
class ResourceDependencyGraph:
    nodes: Dict[str, GraphNode]
    edges: List[GraphEdge]

    # Adjacency
    adj: Dict[str, Set[str]]              # forward adjacency
    rev_adj: Dict[str, Set[str]]          # reverse adjacency

    # Cycle detection results
    sccs: List[Set[str]]                  # strongly connected components
    cycles: List[List[str]]               # enumerated cycles within SCCs

    # For non-cyclic portions
    topological_order: List[str]          # topo sort of condensation DAG
```

### Graph Construction

```
Input:  List[SVModule] from Step 1
Output: ResourceDependencyGraph

1. Create nodes:
   - One node per module instance
   - One node per FSM state (within each module)
   - One node per shared resource (multi-writer signals/memories)
   - One node per handshake endpoint

2. Create edges:
   - For each handshake interface pair:
       sender.valid ──(VALID_READY, can_block=True)──▶ receiver
       receiver.ready ──(VALID_READY)──▶ sender
   - For each req/ack pair:
       requester ──(REQ_ACK, can_block=True)──▶ responder
   - For each shared resource:
       each writer ──(RESOURCE_LOCK, can_block=True)──▶ resource
       resource ──(RESOURCE_LOCK)──▶ each writer   (grant path)
   - For FSM transitions:
       state_A ──(CONTROL_FLOW)──▶ state_B
   - For data flow between modules:
       output port ──(DATA_FLOW)──▶ connected input port

3. Build adjacency lists (forward + reverse)
```

### Cycle Detection: Tarjan's SCC + Cycle Enumeration

```
Phase 1: Tarjan's Strongly Connected Components
─────────────────────────────────────────────────
  - Find all SCCs in the RDG
  - Any SCC with |nodes| > 1 is a potential deadlock zone
  - Single-node SCCs with self-loops also qualify

Phase 2: Cycle Enumeration (Johnson's Algorithm)
─────────────────────────────────────────────────
  - Within each non-trivial SCC, enumerate all elementary cycles
  - Each cycle = candidate deadlock path
  - Filter: keep only cycles where ALL edges have can_block=True

Phase 3: Condensation DAG
─────────────────────────
  - Contract each SCC into a single super-node
  - Resulting graph is a DAG
  - Topological sort this DAG → processing order for Step 3
```

```
Example:

  Original RDG:           Condensation DAG:
  A ⇄ B → C ⇄ D          [SCC1: {A,B}] → [SCC2: {C,D}] → [E]
             ↓
             E

  SCC1 = {A, B}  ← deadlock candidate
  SCC2 = {C, D}  ← deadlock candidate
  Topo order: SCC1, SCC2, E
```

---

## Step 3: LLM Engine + Vector DB

### Vector DB Architecture

Two databases populated from a curated corpus of known deadlock patterns.

```
┌────────────────────────────────────┐    ┌────────────────────────────────────┐
│  DB 1: Code Pattern Database       │    │  DB 2: Module Context Database     │
├────────────────────────────────────┤    ├────────────────────────────────────┤
│                                    │    │                                    │
│  pattern_id: str                   │    │  module_name: str                  │
│  pattern_type: str                 │    │  embedding: vector                 │
│    "circular_wait"                 │    │  interface_summary: str            │
│    "signal_stuck"                  │    │  fsm_summary: str                  │
│    "credit_starvation"             │    │  deadlock_risk_score: float        │
│    "fifo_deadlock"                 │    │  generated_assertions: List[str]   │
│    "handshake_mismatch"            │    │                                    │
│    "terminal_state"                │    │  Populated during analysis:        │
│  code_snippet: str                 │    │  each analyzed module stored here  │
│  embedding: vector                 │    │  for cross-module context lookup   │
│  assertion_template: str           │    │                                    │
│                                    │    │                                    │
│  Embedding model:                  │    │                                    │
│  CodeBERT / GraphCodeBERT          │    │                                    │
└────────────────────────────────────┘    └────────────────────────────────────┘
```

### Deadlock Pattern Categories

| Pattern               | What To Look For                                  |
|-----------------------|---------------------------------------------------|
| **Circular Wait**     | Cycle in resource dependency graph                |
| **Hold and Wait**     | Module holds resource while requesting another    |
| **Signal Stuck**      | valid/ready/grant stuck high or low indefinitely  |
| **Credit Starvation** | Credit counter hits zero, no replenishment path   |
| **FIFO Deadlock**     | Buffer full + writer blocked + reader also blocked|
| **Terminal State**    | FSM reaches state with no exit transition          |
| **Handshake Mismatch**| valid asserted but ready never comes (or reverse) |

### Per-Module LLM Analysis (Divide and Conquer)

Process modules in topological order of the condensation DAG. For SCCs (potential deadlock zones), analyze all modules in the SCC together.

```
┌──────────────────────────────────────────────────────────────────┐
│  For each module / SCC (in topological order):                    │
│                                                                   │
│  ┌──────────────────┐                                             │
│  │  LLM Input:      │                                             │
│  │  - Module code    │                                             │
│  │  - FSMs           │                                             │
│  │  - Handshakes     │                                             │
│  │  - Shared resources│                                            │
│  │  - RDG subgraph   │                                             │
│  │  - Cycles found   │                                             │
│  │  - Similar patterns│  ◀── Vector DB query                      │
│  │  - Accumulated C  │  ◀── context from prior modules            │
│  └────────┬─────────┘                                             │
│           │                                                       │
│           ▼                                                       │
│  ┌──────────────────┐                                             │
│  │  LLM Output:     │                                             │
│  │  - Deadlock       │                                             │
│  │    patterns found │                                             │
│  │  - SVA assertions │                                             │
│  │  - Resource lock  │                                             │
│  │    state updates  │                                             │
│  └────────┬─────────┘                                             │
│           │                                                       │
│           ▼                                                       │
│  ┌──────────────────┐                                             │
│  │  Accumulated     │                                             │
│  │  Context (C)     │  C = C ∪ Θ(Mi)                              │
│  │  + store in DB2  │  (carries forward to next module)           │
│  └──────────────────┘                                             │
└──────────────────────────────────────────────────────────────────┘
```

### Context Accumulation Data Structures

```python
@dataclass
class ResourceLock:
    resource_id: str
    locked_by: Optional[str]      # module holding this resource
    lock_type: str                # "exclusive" | "shared"
    waiting_queue: List[str]      # modules waiting for this resource
    grant_signal: str

@dataclass
class DeadlockPattern:
    pattern_type: str             # from pattern categories table
    involved_modules: List[str]
    involved_signals: List[str]
    cycle_path: List[str]         # empty if not circular wait
    assertion: str                # generated SVA
    confidence: float

@dataclass
class DeadlockContext:
    resource_locks: Dict[str, ResourceLock]
    pending_requests: Dict[str, List[str]]    # module → resources it waits for
    analyzed_modules: Set[str]
    patterns_found: List[DeadlockPattern]
```

### LLM Prompt Structure

```python
prompt = f"""
Analyze this hardware module for deadlock patterns.

Module: {module.name}
Code:
{module_code}

FSMs: {fsm_info}
Handshake Interfaces: {handshake_info}
Shared Resources: {shared_resource_info}

Cycles detected in dependency graph involving this module:
{cycles}

Similar known patterns (from vector DB):
{similar_patterns}

Context from previously analyzed modules:
{accumulated_context}

For each deadlock pattern found, output:
1. Pattern type
2. Involved signals
3. SVA assertion to detect/prevent it

Output format (JSON):
{{
  "patterns": [
    {{
      "type": "...",
      "signals": ["..."],
      "description": "...",
      "sva": "property ... endproperty\\nassert property (...);",
      "confidence": 0.0-1.0
    }}
  ],
  "resource_updates": {{
    "locks_held": ["..."],
    "waiting_for": ["..."]
  }}
}}
"""
```


```
  .sv files
     │
     ▼
 ┌─────────┐     ┌──────────┐     ┌──────────┐     ┌──────────┐
 │ Step 1   │     │ Step 2   │     │ Step 3   │     │ Step 4   │
 │          │     │          │     │          │     │          │
 │ tree-    │────▶│ Build    │────▶│ LLM per  │────▶│ Emit     │
 │ sitter   │     │ RDG      │     │ module   │     │ .sv file │
 │ AST      │     │ Tarjan   │     │ + VecDB  │     │ with SVA │
 │ parse    │     │ SCC      │     │ context  │     │ asserts  │
 │          │     │ cycles   │     │ accumul. │     │          │
 └─────────┘     └──────────┘     └──────────┘     └──────────┘
     │                │                │                │
     ▼                ▼                ▼                ▼
  SVModule         RDG with        DeadlockContext   assertions.sv
  FSM              cycles          + patterns
  Handshake        condensation    + assertions
  SharedRes        DAG
```
