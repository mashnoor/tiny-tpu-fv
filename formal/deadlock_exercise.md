# Hardware Deadlock Bug Injection Exercise

## Overview

This exercise demonstrates a **critical deadlock vulnerability** in the Unified Buffer that can cause the entire TPU to hang. The bug is intentionally injected to help you learn about hardware deadlock patterns.

---

## The Bug Scenario

### Deadlock Type: **Resource Competition with Blocking Assignments**

### What Happens

```
┌─────────────────────────────────────────────────────────────┐
│                                                            │
│  wr_ptr = 127 (near buffer end)                               │
│  grad_descent_ptr = 121 (in "danger zone")                       │
│                                                            │
│  ┌─────────────────────────────────────────────────────────┐  │
│  │ VPU tries to write gradient                              │  │
│  │ Regular writes also happening                             │  │
│  │                                                         │  │
│  │ wr_ptr++ wraps to 0                                      │  │
│  │ grad_descent_ptr++ continues                            │  │
│  │                                                         │  │
│  │ DEADLOCK! Both try to access overlapping addresses         │  │
│  │ Blocking assignment causes indefinite wait                │  │
│  └─────────────────────────────────────────────────────────┘  │
│                                                            │
│  System HANGS - No valid data available                     │
└─────────────────────────────────────────────────────────────┘
```

---

## Code Analysis

### The Buggy Code (Lines 347, 359 in unified_buffer.sv)

```systemverilog
// Inside always_ff @(posedge clk)
// REGULAR WRITE PATH
for (int i = SYSTOLIC_ARRAY_WIDTH-1; i >= 0; i--) begin
    if (ub_wr_valid_in[i]) begin
        ub_memory[wr_ptr] <= ub_wr_data_in[i];
        wr_ptr = wr_ptr + 1;    // ← BUGGY: Blocking assignment!
    end
end

// GRADIENT DESCENT WRITE PATH
if (grad_bias_or_weight) begin
    for (int i = SYSTOLIC_ARRAY_WIDTH-1; i >= 0; i--) begin
        if (grad_descent_done_out[i]) begin
            ub_memory[grad_descent_ptr] <= value_updated_out[i];
            grad_descent_ptr = grad_descent_ptr + 1;  // ← BUGGY: Blocking assignment!
        end
    end
end
```

### Why This Deadlocks Occurs

| Step | Condition | Result |
|------|-----------|--------|
| 1 | `wr_ptr = 127` (max value) | Next write will cause wrap |
| 2 | `grad_descent_ptr = 125` | In "danger zone" (last 8 locations) |
| 3 | Both writes happen in same cycle | Both try to update blocking assignments |
| 4 | No arbitration between the two paths | Race condition on shared resource |
| 5 | Blocking assignments wait for each other | **DEADLOCK** - neither completes |

---

## The Bug Injection File

**File:** `src/unified_buffer_deadlock.sv`

This module contains the intentional deadlock bug with three scenarios:

### Scenario 1: Wrap-Around Collision
```systemverilog
if ((wr_ptr == UNIFIED_BUFFER_WIDTH - 1) && (grad_descent_ptr > UNIFIED_BUFFER_WIDTH - 8)) begin
    deadlock_detected <= 1'b1;  // Signal the deadlock condition
end
```

### Scenario 2: Direct Pointer Collision
```systemverilog
if ((wr_ptr == grad_descent_ptr) && deadlock_detected) begin
    wr_ptr <= wr_ptr;  // Self-blocking! The assignment can never complete
end
```

### Scenario 3: No Wrap-Around Protection
```verilog
// No check: wr_ptr can wrap without checking if memory is "full"
wr_ptr = wr_ptr + 1;  // Can overflow: 127 + 1 = 0 (wraps around)
```

---

## Running Formal Verification on the Buggy Module

### Create verification script to detect deadlock:

```tcl
# formal/deadlock_verify.tcl

analyze -sv ../src/fixedpoint.sv
analyze -sv ../src/unified_buffer_deadlock.sv

elaborate -top unified_buffer_deadlock

clock clk
reset rst

# Assertion 1: Deadlock should NOT be set during normal operation
assert -name NO_DEADLOCK_DURING_NORMAL_OP {
    @(posedge clk) disable iff (rst)
    (wr_ptr < 16'd127) |=> (deadlock_detected == 1'b0)
}

# Assertion 2: When deadlock is detected, outputs become invalid
assert -name DEADLOCK_INVALIDATES_OUTPUTS {
    @(posedge clk) disable iff (rst)
    (deadlock_detected) |=> (ub_rd_input_valid_out_0 == 1'b0)
}

# Assertion 3: Write pointer should never exceed bounds
assert -name WR_PTR_NO_OVERFLOW {
    @(posedge clk) disable iff (rst)
    (wr_ptr <= 16'd127)
}

prove -all
exit
```

### Command to run:
```bash
cd formal
jg -allow_unsupported_OS -fpv -no_gui -tcl deadlock_verify.tcl
```

---

## Lab Exercise: Detect and Fix the Deadlock

### Part 1: Reproduce the Bug
1. Run formal verification on `unified_buffer_deadlock.sv`
2. Observe which assertions fail
3. Use JasperGold's waveform viewer to see the deadlock sequence

### Part 2: Fix the Bug
1. Replace blocking assignments with non-blocking (`<=`)
2. Add proper mutual exclusion between write paths
3. Add buffer full/empty indicators

### Part 3: Verify the Fix
1. Run FV again on the fixed module
2. All assertions should pass
3. Compare proof results

---

## Key Learning Points

### Deadlock Patterns in Hardware

| Pattern | Description | Example |
|---------|-------------|---------|
| **Resource Competition** | Multiple writers to same resource | Two pointers updating same memory location |
| **Circular Wait** | A waits for B, B waits for A | `wr_ptr` and `grad_descent_ptr` deadlock |
| **Blocking Assignment** | Can cause indefinite waits in clocked blocks | `wr_ptr = wr_ptr + 1` in `always_ff` |
| **No Arbitration** | No mechanism to resolve conflicts | No mutex or priority encoder |

### Prevention Techniques

1. **Use non-blocking assignments** (`<=`) in clocked blocks
2. **Add mutex/arbiter** for shared resources
3. **Implement handshake protocols** (request/grant or valid/ready)
4. **Add buffer state indicators** (full/empty flags)
5. **Separate read/write clock domains** when possible

---

## Exercise Questions

1. Why does `wr_ptr = wr_ptr + 1` inside `always_ff` create a deadlock risk?
2. What happens when both `ub_wr_valid_in[i]` and `grad_descent_done_out[i]` are high?
3. How can the `grad_descent_ptr` overlap with `wr_ptr` cause data corruption?
4. Why is there no protection when `wr_ptr` wraps around?
5. What would be a proper fix for this deadlock?
