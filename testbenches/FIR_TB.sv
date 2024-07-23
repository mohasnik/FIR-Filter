`define WIDTH 16
`define LENGTH 64
`define INPUTS_NUMBER 221184
`define INPUT_FILE "input_files/inputs.txt"
`define OUTPUT_FILE "output_files/result_outputs.txt"

`timescale 1ns/1ns
module FIR_TB();
    
    reg clk = 0, reset, input_valid = 0;
    reg [`WIDTH-1:0] FIR_input = 0;
    wire output_valid;
    wire [`WIDTH-1:0] FIR_output;

    reg [`WIDTH-1:0]  input_data [0:`INPUTS_NUMBER-1];

    integer i, out_file;


    FIR #(.LENGTH(`LENGTH), .WIDTH(`WIDTH)) filter
        (
            .clk(clk), .reset(reset),
            .FIR_input(FIR_input),
            .input_valid(input_valid),
            .FIR_output(FIR_output), 
            .output_valid(output_valid)
        );


    
    always #2 clk = ~clk;


    initial begin
        $readmemb(`INPUT_FILE, input_data);
    end

    initial begin
        out_file = $fopen(`OUTPUT_FILE);
        #20 reset = 1;
        #100 reset = 0;

        for(i = 0; i < `INPUTS_NUMBER; i = i + 1 ) begin
            FIR_input = input_data[i];
            #6 input_valid = 1;
            #6 input_valid = 0;

            wait(output_valid);
            $fwrite(out_file, "%b\n", filter.datapath.data_out);
            wait(~output_valid);
        end

        $fclose(out_file);

        #30 $stop;
    end



    // assertions :
        // checking the true number of shifting, as the value of the first register
        // should turn back to its place after one set of computation (one output generated)
    sequence shift_seq;
        ##1 ~(filter.datapath.shift_reg.registers[0] ^ $past(filter.datapath.shift_reg.registers[0], `LENGTH-1));
    endsequence
    
    property shift_pr;
        @(posedge clk) filter.datapath.cnt_done |-> shift_seq ;
    endproperty

    proper_shift: assert property (shift_pr) $display("proper shifting passed");
        else $warning("Assertion shift failed! the value of register[0] is %b but it should be which was %b previously", filter.datapath.shift_reg.registers[0], $past(filter.datapath.shift_reg.registers[0], `LENGTH) );

        // -----------------------------------------------------------------------------


        // adder loop check : 

    sequence  adder_loop_seq;
        ~(filter.datapath.data_out ^ $past(filter.datapath.mult_reg_out,1) + $past(filter.datapath.data_out));
    endsequence

    property adder_loop_pr;
        @(posedge clk) (filter.controller.ps == 2) |-> adder_loop_seq;
    endproperty

    adder_loop: assert property (adder_loop_pr) $display("sum loop passed");
        else $error("adder loop failed!");
        
        // -----------------------------------------------------------------------------



    //assertion handling :
        
        // turining off the count done check since one time checkign sufices:
    initial begin : cnt_done_check_off
        @(negedge output_valid)
        wait(output_valid == 1);
        @(negedge output_valid) begin 
            $assertoff(0, filter.datapath.done_sig); 
            $assertoff(0, adder_loop);
        end
    end 



endmodule