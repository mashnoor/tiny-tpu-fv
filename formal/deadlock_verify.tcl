# =============================================================================
# JasperGold Formal Verification Script for Deadlock Detection
# This script verifies that the buggy unified_buffer module exhibits deadlock
# Usage: cd formal && jg -allow_unsupported_OS -fpv -no_gui -tcl deadlock_verify.tcl
# =============================================================================

puts "\n=========================================="
puts "Deadlock Detection Formal Verification"
puts "==========================================\n"

# =========================================================================
# Design Analysis
# =========================================================================
puts "Analyzing design files..."

analyze -sv ../src/fixedpoint.sv
analyze -sv ../src/unified_buffer_deadlock.sv

# =========================================================================
# Elaboration
# =========================================================================
puts "Elaborating design..."

elaborate -top unified_buffer_deadlock

# =========================================================================
# Clock and Reset
# =========================================================================
puts "Setting up clock and reset..."
clock clk
reset rst

# =========================================================================
# Load Deadlock Detection Assertions
# =========================================================================

puts "\n=========================================="
puts "Adding Deadlock Detection Assertions"
puts "==========================================\n"

# Assertion 1: Under normal operation (wr_ptr < 127), deadlock should not occur
assert -name NO_DEADLOCK_DURING_NORMAL_OP {
    @(posedge clk) disable iff (rst)
    (wr_ptr < 16'd127) |=> (deadlock_detected == 1'b0)
}

# Assertion 2: When deadlock is detected, valid outputs should be suppressed
assert -name DEADLOCK_INVALIDATES_OUTPUTS {
    @(posedge clk) disable iff (rst)
    (deadlock_detected) |=> (ub_rd_input_valid_out_0 == 1'b0 && ub_rd_input_valid_out_1 == 1'b0)
}

# Assertion 3: Write pointer should stay within bounds when not in deadlock
assert -name WR_PTR_STAYS_IN_BOUNDS {
    @(posedge clk) disable iff (rst || deadlock_detected)
    (wr_ptr <= 16'd127)
}

# Assertion 4: Once deadlock occurs, it should persist (liveness property - checking system doesn't magically recover)
assert -name DEADLOCK_IS_STICKY {
    @(posedge clk) disable iff (rst)
    (deadlock_detected) |=> (deadlock_detected == 1'b1)
}

# =========================================================================
# Prove Assertions
# =========================================================================

puts "\n=========================================="
puts "Proving Deadlock Detection Assertions"
puts "==========================================\n"

prove -all

exit
