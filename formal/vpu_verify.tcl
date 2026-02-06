# =============================================================================
# JasperGold Formal Verification Script for VPU Module
# Usage: cd formal && jg -allow_unsupported_OS -fpv -no_gui -tcl vpu_verify.tcl
# =============================================================================

puts "\n=========================================="
puts "Formal Verification of VPU Module"
puts "==========================================\n"

# =========================================================================
# Design Analysis
# =========================================================================
puts "Analyzing design files..."

analyze -sv ../src/fixedpoint.sv
analyze -sv ../src/bias_child.sv
analyze -sv ../src/bias_parent.sv
analyze -sv ../src/leaky_relu_child.sv
analyze -sv ../src/leaky_relu_parent.sv
analyze -sv ../src/leaky_relu_derivative_child.sv
analyze -sv ../src/leaky_relu_derivative_parent.sv
analyze -sv ../src/loss_child.sv
analyze -sv ../src/loss_parent.sv
analyze -sv ../src/vpu.sv

# =========================================================================
# Elaboration
# =========================================================================
puts "Elaborating design..."

elaborate -top vpu

# =========================================================================
# Clock and Reset
# =========================================================================
puts "Setting up clock and reset..."
clock clk
reset rst

# =========================================================================
# Load assertions
# =========================================================================
puts "\nAdding assertions..."
source vpu_assertions.tcl

# =========================================================================
# Prove Assertions
# =========================================================================
puts "\n=========================================="
puts "Proving Assertions"
puts "==========================================\n"

prove -all

exit
