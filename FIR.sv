module FIR #(
    parameter LENGTH = 64, parameter WIDTH = 16
)(
    clk, reset, FIR_input, input_valid, FIR_output, output_valid
);

    // inputs / outputs :
    input clk, reset, input_valid;
    input [WIDTH-1:0] FIR_input;
    output output_valid;
    output [WIDTH-1:0] FIR_output;

    // wires :

    wire get_input, shift_en, flush, cnt_en, cnt_clr, 
        result_freeze, cnt_done, sum_ready;


    // -------------------------------------------------


    FIR_DP #(WIDTH, LENGTH) datapath(.clk(clk), .rst(reset), .get_input(get_input), 
                        .shift_en(shift_en), .flush(flush), .cnt_en(cnt_en), .cnt_clr(cnt_clr), 
                        .result_freeze(result_freeze), .FIR_input(FIR_input), .data_out(FIR_output), 
                        .sum_ready(sum_ready), .cnt_done(cnt_done));



    FIR_CT controller(.clk(clk), .rst(reset), .input_valid(input_valid), .cnt_done(cnt_done), .sum_ready(sum_ready),
                    .get_input(get_input), .shift_en(shift_en), .flush(flush), .cnt_clr(cnt_clr), 
                    .cnt_en(cnt_en), .result_freeze(result_freeze), .output_valid(output_valid));
    




endmodule