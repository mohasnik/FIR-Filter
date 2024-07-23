module Comparator #(
    parameter bit_width
) (
    input[bit_width-1:0] in0, in1,
    output equal
);
    assign equal = (in0 == in1) ? 1'b1 : 1'b0;
endmodule