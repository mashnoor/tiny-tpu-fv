# LLM-IFT
---


### High-Level Flow

```
┌──────────────────────────────────────────────────────────────────────────┐
│                          LLM-IFT Framework                               │
├──────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌──────────────┐    ┌──────────────────┐    ┌───────────────────────┐  │
│  │  RTL Input   │    │  DAG + Topo Sort │    │  Module-wise LLM      │  │
│  │  (Verilog)   │───▶│  (Adjacency List)│───▶│  IFT Analysis         │  │
│  │              │    │                  │    │  (Gate + Net level)   │  │
│  └──────────────┘    └──────────────────┘    └───────────────────────┘  │
│     Step 1               Step 2                      Step 3             │
│                                                        │                │
│                                                        ▼                │
│                          ┌──────────────────────────────────────────┐   │
│                          │  Response Integration                    │   │
│                          │  (End-to-End Leakage Path + JSON Report) │   │
│                          └──────────────────────────────────────────┘   │
│                                        Step 4                           │
└──────────────────────────────────────────────────────────────────────────┘
```

### Four Steps at a Glance

| Step | Name                        | What It Does                                              |
|------|-----------------------------|-----------------------------------------------------------|
| 1    | RTL Pre-processing          | Parse Verilog, extract module hierarchy (master-slave)     |
| 2    | Divide and Conquer          | Build DAG, adjacency list, topological sort of modules     |
| 3    | LLM Engine                  | Prompt LLM per module (in topo order), accumulate context  |
| 4    | Response Integration        | Final LLM pass to find end-to-end leakage paths           |

---

## Step 1: RTL Pre-processing

```
┌────────────────┐         ┌────────────────────────────────┐
│  Verilog RTL   │         │  Parsed Output:                │
│  Design Files  │────────▶│  - Module definitions          │
│                │         │  - Hierarchical relationships   │
└────────────────┘         │  - Master-slave (topo) order    │
                           └────────────────────────────────┘
```

- Parse RTL files to extract module definitions and their relationships
- Structure the module hierarchy so parent-child dependencies are captured
- Operates at RTL level (classified as RTLIFT)

---

## Step 2: Divide and Conquer (Structural Breakdown)

```
Modules: {M1, M2, ..., Mn}

      M1 ──▶ M3 ──▶ M5
              ▲
      M2 ─────┘      │
                      ▼
              M4 ──▶ M6

    DAG G = (Modules, Dependency Edges)
```

Steps performed:
```
1. Build DAG from module hierarchy
     - Nodes  = modules
     - Edges  = inter-module dependencies (Mi depends on Mj)

2. Construct adjacency list
     - A(Mi) = list of modules that Mi feeds into

3. Topological sort
     - Produces ordered sequence: σ = [Ms1, Ms2, ..., Msn]
     - Guarantees: all dependencies resolved before a module is processed

4. Assign hierarchy levels
     - Each module gets a depth level relative to security asset origin
```

---

## Step 3: LLM Engine (Prompting)

This is the core analysis step. Each module is fed to the LLM sequentially in topological order, building on accumulated context from prior modules.

```
┌─────────────────────────────────────────────────────────────┐
│  For each module Mi (in topological order):                  │
│                                                              │
│  ┌──────────────┐                                            │
│  │  Inputs to   │  - Verilog code of Mi                      │
│  │  LLM Prompt  │  - Ancestor modules (who feeds into Mi)    │
│  │              │  - Adjacency list (dependencies)           │
│  │              │  - IFT techniques (gate-level, net-level)  │
│  │              │  - Accumulated context from prior modules  │
│  └──────┬───────┘                                            │
│         │                                                    │
│         ▼                                                    │
│  ┌──────────────┐                                            │
│  │  LLM Output  │  - Sensitive data sources (Si)             │
│  │  per Module  │  - Assets influenced by data flow (Oi)     │
│  │  Θ(Mi)       │  - Logical transformations (Ψi)            │
│  │              │  - Internal/external flow paths (Λi)       │
│  └──────┬───────┘                                            │
│         │                                                    │
│         ▼                                                    │
│  ┌──────────────┐                                            │
│  │  Accumulated │  C = C ∪ Θ(Mi)                             │
│  │  Context (C) │  (carries forward to next module)          │
│  └──────────────┘                                            │
└─────────────────────────────────────────────────────────────┘
```

Key idea: each module's analysis benefits from all prior module findings, enabling cross-module flow tracking.

---

## Step 4: Response Integration

After all modules are analyzed, a final LLM pass consolidates everything.

```
┌──────────────────┐    ┌──────────────────┐    ┌───────────────────────┐
│  Accumulated     │    │  Final LLM Pass  │    │  Structured JSON      │
│  Context (C)     │───▶│  (Global check)  │───▶│  Report (Ω)           │
│  + Module List   │    │                  │    │                       │
│  + Adjacency     │    │  Is there an     │    │  - Vulnerability? Y/N │
│  + IFT Context   │    │  end-to-end      │    │  - Vulnerable modules │
└──────────────────┘    │  leakage path?   │    │  - Leakage path       │
                        └──────────────────┘    │  - Leakage type       │
                                                │  - Explanation        │
                                                └───────────────────────┘
```

If leakage is detected, the report includes the full propagation path:

```
Leakage Path:  M_source → M_intermediate1 → M_intermediate2 → M_sink (output)
```
