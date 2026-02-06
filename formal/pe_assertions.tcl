# Assertions file for PE formal verification
# Each assertion must be on a single line or use proper continuation

assert -name INPUT_DATA_PROPAGATION {@(posedge clk) disable iff (rst || !pe_enabled) (pe_valid_in) |=> (pe_input_out == $past(pe_input_in))}

assert -name VALID_SIGNAL_PROPAGATION {@(posedge clk) disable iff (rst || !pe_enabled) (pe_valid_in) |=> (pe_valid_out == 1'b1)}

assert -name WEIGHT_OUTPUT_PIPELINE {@(posedge clk) disable iff (rst || !pe_enabled) (pe_accept_w_in) |=> (pe_weight_out == $past(pe_weight_in))}

assert -name WEIGHT_OUTPUT_ZERO {@(posedge clk) disable iff (rst || !pe_enabled) (!pe_accept_w_in) |=> (pe_weight_out == 16'sd0)}

assert -name SWITCH_SIGNAL_PROPAGATION {@(posedge clk) disable iff (rst || !pe_enabled) (pe_switch_in) |=> (pe_switch_out == 1'b1)}
