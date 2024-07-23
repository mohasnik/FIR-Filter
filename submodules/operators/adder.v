// MODULE NAME : adder

module Adder #(
    parameter input_width
) (
    input signed [input_width-1 : 0] in0, in1,
    output signed [input_width-1 : 0] sum_result
);
    assign sum_result = in0 + in1;

endmodule