`timescale 1ns/1ps
`default_nettype none

// =============================================================================
// DEADLOCK BUG INJECTION MODULE
// =============================================================================
// This module demonstrates a critical deadlock vulnerability that can occur
// when the unified buffer's write pointer (wr_ptr) wraps around and overwrites
// data that is still being read by the systolic array or VPU.
//
// DEADLOCK SCENARIO:
// 1. wr_ptr reaches UNIFIED_BUFFER_WIDTH (128) and wraps to 0
// 2. Simultaneously, a read operation is in progress from an address
//    that is about to be overwritten
// 3. The gradient descent write logic AND the regular write path both use wr_ptr
// 4. This creates a race condition where:
//    - wr_ptr gets stuck in an inconsistent state
//    - The reader gets corrupted data
//    - The system hangs waiting for data that was overwritten
//
// ROOT CAUSE: The blocking assignment wr_ptr = wr_ptr + 1 in the clocked block
// creates a race condition when multiple processes try to update it
// simultaneously with the wrap-around condition.
// =============================================================================

module unified_buffer_deadlock #(
    parameter UNIFIED_BUFFER_WIDTH = 128,
    parameter SYSTOLIC_ARRAY_WIDTH = 2
)(
    input wire logic clk,
    input wire logic rst,

    // Write ports from VPU to UB
    input wire logic [15:0] ub_wr_data_in_0,
    input wire logic [15:0] ub_wr_data_in_1,
    input wire logic ub_wr_valid_in_0,
    input wire logic ub_wr_valid_in_1,

    // Write ports from host to UB (for loading in parameters)
    input wire logic [15:0] ub_wr_host_data_in_0,
    input wire logic [15:0] ub_wr_host_data_in_1,
    input wire logic ub_wr_host_valid_in_0,
    input wire logic ub_wr_host_valid_in_1,

    // Read instruction input from instruction memory
    input wire logic ub_rd_start_in,
    input wire logic ub_rd_transpose,
    input wire logic [8:0] ub_ptr_select,
    input wire logic [15:0] ub_rd_addr_in,
    input wire logic [15:0] ub_rd_row_size,
    input wire logic [15:0] ub_rd_col_size,

    // Learning rate input
    input wire logic [15:0] learning_rate_in,

    // Gradient descent write enable (for deadlock scenario)
    input wire logic grad_descent_enable,
    input wire logic [15:0] grad_descent_data_in,

    // Read ports from UB to left side of systolic array
    output var logic [15:0] ub_rd_input_data_out_0,
    output var logic [15:0] ub_rd_input_data_out_1,
    output var logic ub_rd_input_valid_out_0,
    output var logic ub_rd_input_valid_out_1,

    // Read ports from UB to top of systolic array
    output var logic [15:0] ub_rd_weight_data_out_0,
    output var logic [15:0] ub_rd_weight_data_out_1,
    output var logic ub_rd_weight_valid_out_0,
    output var logic ub_rd_weight_valid_out_1,

    // Read ports from UB to bias modules in VPU
    output var logic [15:0] ub_rd_bias_data_out_0,
    output var logic [15:0] ub_rd_bias_data_out_1,

    // Read ports from UB to loss modules (Y matrices) in VPU
    output var logic [15:0] ub_rd_Y_data_out_0,
    output var logic [15:0] ub_rd_Y_data_out_1,

    // Read ports from UB to activation derivative modules (H matrices) in VPU
    output var logic [15:0] ub_rd_H_data_out_0,
    output var logic [15:0] ub_rd_H_data_out_1,

    // Outputs to send number of columns to systolic array
    output var logic [15:0] ub_rd_col_size_out,
    output var logic ub_rd_col_size_valid_out,

    // Deadlock detection output
    output var logic deadlock_detected
);

    logic [15:0] ub_memory [0:UNIFIED_BUFFER_WIDTH-1];

    logic [15:0] wr_ptr;
    logic [15:0] grad_descent_ptr;

    // Deadlock trigger: when wr_ptr is close to wrapping and gradient writes are active
    logic [15:0] wr_ptr_shadow;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            // Reset all pointers and outputs
            wr_ptr <= 16'd0;
            wr_ptr_shadow <= 16'd0;
            grad_descent_ptr <= 16'd0;
            deadlock_detected <= 1'b0;

            // Reset read pointers and valid signals
            ub_rd_input_data_out_0 <= 16'd0;
            ub_rd_input_data_out_1 <= 16'd0;
            ub_rd_input_valid_out_0 <= 1'b0;
            ub_rd_input_valid_out_1 <= 1'b0;

            ub_rd_weight_data_out_0 <= 16'd0;
            ub_rd_weight_data_out_1 <= 16'd0;
            ub_rd_weight_valid_out_0 <= 1'b0;
            ub_rd_weight_valid_out_1 <= 1'b0;

            ub_rd_bias_data_out_0 <= 16'd0;
            ub_rd_bias_data_out_1 <= 16'd0;

            ub_rd_Y_data_out_0 <= 16'd0;
            ub_rd_Y_data_out_1 <= 16'd0;

            ub_rd_H_data_out_0 <= 16'd0;
            ub_rd_H_data_out_1 <= 16'd0;

            ub_rd_col_size_out <= 16'd0;
            ub_rd_col_size_valid_out <= 1'b0;
        end else begin
            // =================================================================
            // DEADLOCK BUG: The blocking assignment below creates a deadlock condition
            // when wr_ptr wraps around and conflicts with grad_descent_ptr
            // =================================================================

            // DEADLOCK SCENARIO 1: Check for potential wrap-around collision
            // When wr_ptr + 1 would wrap AND grad_descent_ptr is in the "danger zone"
            if ((wr_ptr == UNIFIED_BUFFER_WIDTH - 1) && (grad_descent_ptr > UNIFIED_BUFFER_WIDTH - 8)) begin
                // DEADLOCK CONDITION: wr_ptr will wrap to 0 on next write
                // but grad_descent_ptr is still in high address range
                // When both try to write simultaneously, the blocking assignment
                // causes a race condition that can hang the system
                deadlock_detected <= 1'b1;
            end

            // Regular write path (VPU -> UB)
            // Port 0
            if (ub_wr_valid_in_0) begin
                ub_memory[wr_ptr] <= ub_wr_data_in_0;
                // BUGGY CODE: Blocking assignment in clocked block - creates deadlock
                // When wr_ptr wraps, it creates a race with gradient descent writes
                wr_ptr = wr_ptr + 1;
            end

            // Port 1
            if (ub_wr_valid_in_1) begin
                ub_memory[wr_ptr] <= ub_wr_data_in_1;
                // BUGGY CODE: Blocking assignment in clocked block - creates deadlock
                wr_ptr = wr_ptr + 1;
            end

            // Gradient descent write path (VPU -> UB after backward pass)
            // This can interleave with regular writes and cause deadlock
            // when addresses overlap
            if (grad_descent_enable) begin
                // BUGGY CODE: No check if wr_ptr is being used by regular writes
                // This can conflict with the logic above when pointers overlap
                ub_memory[grad_descent_ptr] <= grad_descent_data_in;
                // BUGGY CODE: Blocking assignment that can conflict with wr_ptr updates
                grad_descent_ptr = grad_descent_ptr + 1;
            end

            // DEADLOCK SCENARIO 2: Double-write collision
            // If both regular write and gradient write try to access the same
            // memory location, the blocking assignments can cause system hang
            if ((wr_ptr == grad_descent_ptr) && deadlock_detected) begin
                // System is now deadlocked - both writers waiting for the other
                // but the blocking assignment prevents either from proceeding
                // This simulates a hardware hang condition
                wr_ptr <= wr_ptr;  // Self-blocking assignment!
            end
        end
    end

endmodule
