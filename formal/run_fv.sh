#!/bin/bash
# =============================================================================
# Formal Verification Script for PE Module using JasperGold
# Usage: cd formal && ./run_fv.sh
# Or: ssh vlsi "cd /home/net/no547576/amd/only_formal/tiny-tpu/formal && bash run_fv.sh"
# =============================================================================

set -e

echo "=========================================="
echo "Formal Verification of PE Module"
echo "Tiny-TPU Project"
echo "=========================================="
echo ""

# Run JasperGold in batch mode with the verification script
jg -batch -source pe_verify.tcl

echo ""
echo "=========================================="
echo "Verification complete!"
echo "Check pe_verification_report.rpt for results."
echo "=========================================="
