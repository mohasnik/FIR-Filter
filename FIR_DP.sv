`define SIGN_EXTEND(OUT_WIDTH, WIDTH, SIGNAL)  {{(OUT_WIDTH-WIDTH){SIGNAL[WIDTH - 1]}}, SIGNAL}

module FIR_DP #(
    parameter bit_width, parameter FIR_order

) (
    clk, rst,
    get_input, shift_en, flush, cnt_en, cnt_clr, result_freeze,
    FIR_input,
    data_out,
    sum_ready,
    cnt_done
);
    // parameters : 
    localparam adder_sum_width = 2*bit_width + $clog2(FIR_order);
    localparam counter_width = $clog2(FIR_order);

    // input / outputs :
    input clk, rst;
    input get_input, shift_en, flush, cnt_en, cnt_clr, result_freeze;
    input[bit_width-1:0] FIR_input;
    output[adder_sum_width - 1:0] data_out;
    output sum_ready, cnt_done;
    
    // wires : 
    wire[bit_width-1 : 0] mux_out, shift_reg_out, LUT_data, x_reg_out, coef_reg_out;
    wire[2*bit_width-1 : 0] mult_out, mult_reg_out;
    wire[counter_width-1 : 0] LUT_adress;
    wire [adder_sum_width-1 : 0] data_out, adder_out;
    wire init, comp_out, eq_reg1_out; 

    // -------------------------------------------------------
    


    // components : 

    Counter #(counter_width) upCounter(.clk(clk), .rst(rst), .increament(cnt_en), 
                        .clear(cnt_clr), .init(0), .count(LUT_adress), .Co());
    
    Comparator #(counter_width) comparator(.in0(LUT_adress), .in1(FIR_order-1), .equal(comp_out));

    shift_register #(FIR_order, bit_width) shift_reg(.clk(clk), .rst(rst), .shift_en(shift_en), 
                        .reg_in(mux_out), .reg_out(shift_reg_out));

    LUT #(FIR_order , bit_width) coef_LUT(.adr(LUT_adress), .data(LUT_data));

    Multiplier #(bit_width) multiplier(.in0(x_reg_out), .in1(coef_reg_out), .mult_result(mult_out));

        // NOTE : sign extend must be done for adder inputs
    Adder #(adder_sum_width) adder( .in0(`SIGN_EXTEND(adder_sum_width, 2*bit_width, mult_reg_out)), 
                        .in1(data_out), .sum_result(adder_out));
    
    
    // pipeline registers :

    register_freeze #(adder_sum_width) result_reg(.clk(clk), .rst(rst), .reg_freeze(result_freeze),
                     .flush(flush), .reg_in(adder_out), .reg_out(data_out));
    

    register_clr #(bit_width) coef_reg(.clk(clk), .rst(rst), .clr(flush), 
                    .reg_in(LUT_data), .reg_out(coef_reg_out));

    
    register_clr #(bit_width) x_reg(.clk(clk), .rst(rst), .clr(flush), 
                    .reg_in(shift_reg_out), .reg_out(x_reg_out));

    
    register_clr #(2*bit_width) mult_reg(.clk(clk), .rst(rst), .clr(flush), 
                    .reg_in(mult_out), .reg_out(mult_reg_out));

    register_clr #(1) eq_reg1(.clk(clk), .rst(rst), .clr(flush), 
                    .reg_in(comp_out), .reg_out(eq_reg1_out));

    register_clr #(1) eq_reg2(.clk(clk), .rst(rst), .clr(flush), 
                    .reg_in(eq_reg1_out), .reg_out(sum_ready));



    // multiplexer before shift register :
    assign mux_out = get_input ?  FIR_input : shift_reg_out;  

    assign cnt_done = comp_out;


    // assertions :
        
        // checking the equal signal (count done) and the registered signal (sum_ready)
        // to arrive at the proper time
    sequence done_sig_seq;
        cnt_done ##2 sum_ready;
    endsequence

    property cnt_done_true_registering;
        @(posedge clk) (LUT_adress == (FIR_order-1)) |-> done_sig_seq;
    endproperty

    done_sig: assert property (cnt_done_true_registering) $display("%0t ns, done signal pass", $time);
        else $error("Assertion done_sig failed");

        // -----------------------------------------------------------------------------

    

    
   
    
endmodule