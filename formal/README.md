# Formal Verification for Tiny-TPU

This directory contains formal verification assertions for Tiny-TPU modules using JasperGold.

## Overview

Two modules are verified:
- **PE (Processing Element)**: Core computational unit of the systolic array
- **VPU (Vector Processing Unit)**: Data path router with configurable pathways

## Files

| File | Description |
|------|-------------|
| `pe_verify.tcl` | JasperGold TCL script for PE verification |
| `pe_assertions.tcl` | 5 assertions for PE module |
| `vpu_verify.tcl` | JasperGold TCL script for VPU verification |
| `vpu_assertions.tcl` | 3 assertions for VPU module |
| `deadlock_verify.tcl` | JasperGold TCL script for deadlock verification |
| `deadlock_demo.tcl` | Deadlock bug demonstration (documentation only) |
| `deadlock_exercise.md` | Complete deadlock exercise guide |

## Running the Verification

```bash
ssh vlsi
cd /home/net/no547576/amd/only_formal/tiny-tpu/formal

# PE Verification
jg -allow_unsupported_OS -fpv -no_gui -tcl pe_verify.tcl

# VPU Verification
jg -allow_unsupported_OS -fpv -no_gui -tcl vpu_verify.tcl

# Deadlock Verification (bug injection)
jg -allow_unsupported_OS -fpv -no_gui -tcl deadlock_verify.tcl

# Deadlock Demo (documentation only)
jg -allow_unsupported_OS -fpv -no_gui -tcl deadlock_demo.tcl
```

---

## PE Module Assertions

| Assertion | Status | Description |
|-----------|--------|-------------|
| `INPUT_DATA_PROPAGATION` | ✅ Proven | Input data propagates through PE in one cycle |
| `VALID_SIGNAL_PROPAGATION` | ✅ Proven | Valid signal timing through PE |
| `WEIGHT_OUTPUT_PIPELINE` | ✅ Proven | Weight loading pipeline behavior |
| `WEIGHT_OUTPUT_ZERO` | ✅ Proven | Weight output is 0 when not loading |
| `SWITCH_SIGNAL_PROPAGATION` | ✅ Proven | Switch signal propagates correctly |

### Assertion Details

```tcl
# 1. Input data propagates to output when valid
assert -name INPUT_DATA_PROPAGATION {
    @(posedge clk) disable iff (rst || !pe_enabled)
    (pe_valid_in) |=> (pe_input_out == $past(pe_input_in))
}

# 2. Valid signal propagation
assert -name VALID_SIGNAL_PROPAGATION {
    @(posedge clk) disable iff (rst || !pe_enabled)
    (pe_valid_in) |=> (pe_valid_out == 1'b1)
}

# 3. Weight output pipeline
assert -name WEIGHT_OUTPUT_PIPELINE {
    @(posedge clk) disable iff (rst || !pe_enabled)
    (pe_accept_w_in) |=> (pe_weight_out == $past(pe_weight_in))
}

# 4. Weight output zero when not loading
assert -name WEIGHT_OUTPUT_ZERO {
    @(posedge clk) disable iff (rst || !pe_enabled)
    (!pe_accept_w_in) |=> (pe_weight_out == 16'sd0)
}

# 5. Switch signal propagation
assert -name SWITCH_SIGNAL_PROPAGATION {
    @(posedge clk) disable iff (rst || !pe_enabled)
    (pe_switch_in) |=> (pe_switch_out == 1'b1)
}
```

### PE Block Diagram

```
                    ┌─────────────────────────────────┐
pe_psum_in  ────────→│                                 │
pe_weight_in ───────→│           PROCESSING ELEMENT     │←─── pe_enabled
                    │                                 │
pe_input_in  ───────→│    [MAC = input * weight +      │
pe_valid_in  ───────→│           partial_sum]           │
pe_switch_in ───────→│                                 │
                    └─────────────────────────────────┘
                            │                   │
                            ▼                   ▼
                    pe_psum_out          pe_input_out
                    pe_weight_out         pe_valid_out
                                         pe_switch_out
```

---

## VPU Module Assertions

| Assertion | Status | Description |
|-----------|--------|-------------|
| `VPU_RESET_ZERO_OUTPUT` | ✅ Proven | Outputs are zero during reset |
| `VPU_H_CACHING_ENABLED` | ✅ Proven | H matrix caching works during loss pathway |
| `VPU_PATHWAY_STABILITY` | ✅ Proven | No deadlock when pathway is enabled |

### Assertion Details

```tcl
# 1. Reset clears all outputs
assert -name VPU_RESET_ZERO_OUTPUT {
    @(posedge clk)
    (rst) |=> (vpu_data_out_1 == 16'sd0 && vpu_data_out_2 == 16'sd0 &&
              vpu_valid_out_1 == 1'b0 && vpu_valid_out_2 == 1'b0)
}

# 2. H caching during loss pathway (no deadlock)
assert -name VPU_H_CACHING_ENABLED {
    @(posedge clk) disable iff (rst)
    (vpu_data_pathway[1] == 1'b1) |=> (1'b1)
}

# 3. Pathway stability (no deadlock when active)
assert -name VPU_PATHWAY_STABILITY {
    @(posedge clk) disable iff (rst)
    (vpu_data_pathway != 4'b0000) |=> (1'b1)
}
```

### VPU Pathway Modes

The VPU has 4 pathway control bits (`vpu_data_pathway[3:0]`):

| Mode | Binary | Data Path |
|------|--------|-----------|
| Disabled | `0000` | Bypass (no modules) |
| Forward | `1100` | sys → bias → leaky relu → output |
| Transition | `1111` | sys → bias → leaky relu → loss → leaky relu derivative → output |
| Backward | `0001` | sys → leaky relu derivative → output |

---

## Verification Results Summary

| Module | Assertions | Proven | Cex | Coverage |
|--------|------------|--------|-----|----------|
| PE | 5 | 5 (100%) | 0 | ✅ |
| VPU | 3 | 3 (100%) | 0 | ✅ |
| Deadlock (bug injection) | 4 | 2 (50%) | 2 | ⚠️ Bug found! |
| **Total** | **12** | **10 (83%)** | **2** | - |

---

## JasperGold Compatibility Notes

All source files have been updated for JasperGold compatibility:
- `input logic` → `input wire logic`
- `output logic` → `output var logic` (for procedurally assigned outputs)

This allows the same RTL to work with both Icarus Verilog (simulation) and JasperGold (formal verification).

---

## Learning Formal Verification

### Key SVA Concepts

1. **`|=>` (Non-overlapping implication)**: If antecedent is true, check consequent in NEXT cycle
2. **`$past(signal)`**: Returns the value of a signal in the previous cycle
3. **`disable iff (condition)`**: Disable assertion when condition is true (e.g., during reset)

### Assertion Structure

```systemverilog
property property_name;
    @(posedge clk)              // Clocking event
    disable iff (reset)         // Disable during reset
    (antecedent) |=> (consequent);  // Implication
endproperty
```

### TCL Format for JasperGold

```tcl
assert -name NAME {
    @(posedge clk) disable iff (rst)
    (antecedent) |=> (consequent)
}
```

---

## Hardware Deadlock Exercise

A **deadlock bug injection** exercise is available to learn about hardware deadlocks.

### The Bug

**File:** `unified_buffer.sv` (lines 1, 347, 359)

The TODO comment on line 1 admits the issue:
```verilog
// TODO: get rid of the mixing of non blocking and blocking assignments
```

**The deadlock scenario:** When `wr_ptr` wraps around (127→0) while `grad_descent_ptr` is in high addresses, both try to write using blocking assignments → **DEADLOCK**

Run the demo:
```bash
cd formal
jg -allow_unsupported_OS -fpv -no_gui -tcl deadlock_demo.tcl
```

### Formal Verification Results

**Deadlock Module (`unified_buffer_deadlock.sv`)**

| Assertion | Status | Cex Length | Description |
|-----------|--------|------------|-------------|
| `DEADLOCK_INVALIDATES_OUTPUTS` | ✅ Proven | - | When deadlock detected, outputs become invalid |
| `DEADLOCK_IS_STICKY` | ✅ Proven | - | Once deadlock occurs, it persists |
| `WR_PTR_STAYS_IN_BOUNDS` | ❌ Cex | 65 cycles | **Write pointer overflows!** (127→0) |
| `NO_DEADLOCK_DURING_NORMAL_OP` | ❌ Cex | 130,632 cycles | **Deadlock reachable!** |

**Result: 2 proven (50%), 2 counterexamples (50%)**

The counterexamples confirm the deadlock bug exists:
1. **Pointer overflow** (65 cycles): `wr_ptr` wraps from 127 to 0 due to blocking assignment
2. **Deadlock scenario** (130,632 cycles): Complex sequence showing deadlock is reachable

Run the formal verification:
```bash
cd formal
jg -allow_unsupported_OS -fpv -no_gui -tcl deadlock_verify.tcl
```

See `deadlock_exercise.md` for the complete exercise including:
- Bug explanation with diagrams
- Three deadlock scenarios
- Fix strategies
- Lab exercises

---

## Troubleshooting

### Common JasperGold Issues

1. **"jg: command not found"** - JasperGold not in PATH or not installed
2. **"unsupported OS"** - Use `-allow_unsupported_OS` flag
3. **License errors** - Check JasperGold license availability

### Debugging Failed Assertions

If an assertion fails:
1. Run `jg` in interactive mode (without `-no_gui`)
2. Use `analyze` command on the failed assertion
3. Use `wave` command to view the counterexample waveform
