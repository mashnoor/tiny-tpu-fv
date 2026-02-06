`timescale 1ns/1ps

// =============================================================================
// Formal Verification Assertions for PE Module (for use with JasperGold)
// This version binds to pe_fv (the FV wrapper) instead of pe
// =============================================================================

module pe_assertions_fv #(
    parameter int DATA_WIDTH = 16
) (
    input logic clk,
    input logic rst,

    // North wires of PE
    input logic signed [15:0] pe_psum_in,
    input logic signed [15:0] pe_weight_in,
    input logic pe_accept_w_in,

    // West wires of PE
    input logic signed [15:0] pe_input_in,
    input logic pe_valid_in,
    input logic pe_switch_in,
    input logic pe_enabled,

    // South wires of the PE
    input logic signed [15:0] pe_psum_out,
    input logic signed [15:0] pe_weight_out,

    // East wires of the PE
    input logic signed [15:0] pe_input_out,
    input logic pe_valid_out,
    input logic pe_switch_out
);

    // =========================================================================
    // ASSERTION 1: Input Data Propagation
    // =========================================================================

    property input_data_propagation;
        @(posedge clk)
        disable iff (rst || !pe_enabled)
        (pe_valid_in) |=> (pe_input_out == $past(pe_input_in));
    endproperty

    INPUT_DATA_PROPAGATION: assert property (input_data_propagation)
        else $error("Input data propagation failed: pe_input_out = %d, expected = %d",
                   pe_input_out, $past(pe_input_in));


    // =========================================================================
    // ASSERTION 2: Valid Signal Propagation
    // =========================================================================

    property valid_signal_propagation;
        @(posedge clk)
        disable iff (rst || !pe_enabled)
        (pe_valid_in) |=> (pe_valid_out == 1'b1);
    endproperty

    VALID_SIGNAL_PROPAGATION: assert property (valid_signal_propagation)
        else $error("Valid signal not propagated correctly");


    // =========================================================================
    // ASSERTION 3: Weight Output Pipeline
    // =========================================================================

    property weight_output_pipeline;
        @(posedge clk)
        disable iff (rst || !pe_enabled)
        (pe_accept_w_in) |=> (pe_weight_out == $past(pe_weight_in));
    endproperty

    WEIGHT_OUTPUT_PIPELINE: assert property (weight_output_pipeline)
        else $error("Weight output pipeline failed: pe_weight_out = %d, expected = %d",
                   pe_weight_out, $past(pe_weight_in));


    property weight_output_zero_when_not_loading;
        @(posedge clk)
        disable iff (rst || !pe_enabled)
        (!pe_accept_w_in) |=> (pe_weight_out == 16'sd0);
    endproperty

    WEIGHT_OUTPUT_ZERO: assert property (weight_output_zero_when_not_loading)
        else $error("Weight output should be 0 when not loading");


    // =========================================================================
    // ASSERTION 4: Switch Signal Propagation
    // =========================================================================

    property switch_signal_propagation;
        @(posedge clk)
        disable iff (rst || !pe_enabled)
        (pe_switch_in) |=> (pe_switch_out == 1'b1);
    endproperty

    SWITCH_SIGNAL_PROPAGATION: assert property (switch_signal_propagation)
        else $error("Switch signal not propagated correctly");


    // =========================================================================
    // Cover Properties
    // =========================================================================

    cover property (@(posedge clk) pe_valid_in && pe_enabled)
        $info("Covered: Valid data processing cycle");

    cover property (@(posedge clk) pe_switch_in && pe_enabled)
        $info("Covered: Weight switch cycle");

    cover property (@(posedge clk) pe_accept_w_in && pe_enabled)
        $info("Covered: Weight load cycle");

endmodule


// =============================================================================
// BIND MODULE - Binds assertions to pe_fv module
// =============================================================================

module pe_assertions_bind_fv;
    bind pe_fv pe_assertions_fv #(
        .DATA_WIDTH(16)
    ) pe_assertions_inst (
        .clk(clk),
        .rst(rst),
        .pe_psum_in(pe_psum_in),
        .pe_weight_in(pe_weight_in),
        .pe_accept_w_in(pe_accept_w_in),
        .pe_input_in(pe_input_in),
        .pe_valid_in(pe_valid_in),
        .pe_switch_in(pe_switch_in),
        .pe_enabled(pe_enabled),
        .pe_psum_out(pe_psum_out),
        .pe_weight_out(pe_weight_out),
        .pe_input_out(pe_input_out),
        .pe_valid_out(pe_valid_out),
        .pe_switch_out(pe_switch_out)
    );
endmodule
