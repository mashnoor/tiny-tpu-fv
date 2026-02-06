# Formal Verification for Tiny-TPU

This directory contains formal verification assertions for the Tiny-TPU Processing Element (PE) module using JasperGold.

## Overview

The PE (Processing Element) is the core computational unit of the systolic array that performs multiply-accumulate operations. This formal verification setup verifies key properties of the PE.

## Files

| File | Description |
|------|-------------|
| `../src/pe_assertions.sv` | SystemVerilog assertions for the PE module |
| `pe_verify.tcl` | JasperGold TCL script for running formal verification |
| `run_fv.sh` | Shell script wrapper to run verification |

## The 3 Main Assertions

### 1. INPUT_DATA_PROPAGATION
**Property:** When `pe_valid_in` is asserted, the input data (`pe_input_in`) propagates to `pe_input_out` on the next cycle.

**Purpose:** Verifies the forward data path through the PE array. This ensures that input activations flow correctly from west to east through the systolic array.

```systemverilog
property input_data_propagation;
    @(posedge clk)
    disable iff (rst || !pe_enabled)
    (pe_valid_in) |=> (pe_input_out == $past(pe_input_in));
endproperty
```

### 2. VALID_SIGNAL_PROPAGATION
**Property:** The valid signal propagates from input to output with exactly one cycle delay through the enabled PE.

**Purpose:** Verifies the handshake protocol timing. In a systolic array, valid signals must propagate in lockstep with data to ensure correct operation.

```systemverilog
property valid_signal_propagation;
    @(posedge clk)
    disable iff (rst || !pe_enabled)
    (pe_valid_in) |=> (pe_valid_out == 1'b1);
endproperty
```

### 3. WEIGHT_OUTPUT_PIPELINE
**Property:** When `pe_accept_w_in` is asserted, the weight appears at `pe_weight_out` on the next cycle.

**Purpose:** Verifies the weight loading pipeline stage. Weights are loaded from north to south through the array before computation begins.

```systemverilog
property weight_output_pipeline;
    @(posedge clk)
    disable iff (rst || !pe_enabled)
    (pe_accept_w_in) |=> (pe_weight_out == $past(pe_weight_in));
endproperty
```

## Running the Verification

### On the vlsi server:

```bash
ssh vlsi
cd /home/net/no547576/amd/only_formal/tiny-tpu/formal
jg -batch -source pe_verify.tcl
```

Or using the shell script:

```bash
cd /home/net/no547576/amd/only_formal/tiny-tpu/formal
bash run_fv.sh
```

## Expected Output

The script will:
1. Compile the PE module and fixed-point arithmetic module
2. Bind the assertions to the PE module
3. Prove each assertion
4. Generate a coverage report
5. Create `pe_verification_report.rpt` with detailed results

## Module Under Test

### PE (Processing Element) Block Diagram

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
                            │                   │
                            ▼                   ▼
                    pe_psum_out          pe_input_out
                    pe_weight_out         pe_valid_out
                                         pe_switch_out
```

### Key Signals

| Direction | Signal | Description |
|-----------|--------|-------------|
| Input | `pe_input_in` | Input activation from west |
| Input | `pe_weight_in` | Weight from north |
| Input | `pe_psum_in` | Partial sum from north |
| Input | `pe_valid_in` | Valid signal for input data |
| Input | `pe_switch_in` | Switch weight registers |
| Input | `pe_enabled` | Enable this PE |
| Output | `pe_psum_out` | Partial sum to south |
| Output | `pe_weight_out` | Weight to south |
| Output | `pe_input_out` | Input to east |
| Output | `pe_valid_out` | Valid signal to east |

## Learning Formal Verification

### Key Concepts Used

1. **SVA (SystemVerilog Assertions)**: Declarative way to specify design properties
2. **`|=>` (Non-overlapping implication)**: If antecedent is true, check consequent in NEXT cycle
3. **`$past()`**: Returns the value of a signal in the previous cycle
4. **`disable iff`**: Disable assertion when condition is true (e.g., during reset)
5. **`bind`**: Attach assertions to a module without modifying the source

### Assertion Structure

```systemverilog
property property_name;
    @(posedge clk)              // Clocking event
    disable iff (reset)         // Disable during reset
    (antecedent) |=> (consequent);  // Implication
endproperty

ASSERTION_NAME: assert property (property_name)
    else $error("Message with %d values", signal);
```

## Troubleshooting

### Common JasperGold Issues

1. **"jg: command not found"** - JasperGold is not in PATH or not installed on this server
2. **License errors** - Check that JasperGold license is available
3. **Compilation errors** - Verify all source files are present and paths are correct

### Debugging Failed Assertions

If an assertion fails, JasperGold can generate a counterexample waveform:
1. Run `jg` in interactive mode (without `-batch`)
2. Use `analyze` command on the failed assertion
3. Use `wave` command to view the counterexample
