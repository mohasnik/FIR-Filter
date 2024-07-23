// MODULE NAME : multiplier



module Multiplier #(
    parameter input_width
)(
    input signed [input_width-1:0] in0, in1,
    output signed[2*input_width-1:0] mult_result
);
    assign mult_result = in0 * in1;

endmodule