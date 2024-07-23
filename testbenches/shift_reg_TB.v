`define WIDTH 8
`define SIZE 10

module shift_reg_TB();
    reg clk = 0, rst;
    reg shift_en;
    reg[`WIDTH-1 : 0] reg_in;
    wire[`WIDTH-1:0] reg_out;


    shift_register #(`SIZE, `WIDTH) UUT(clk, rst, shift_en, reg_in, reg_out);


    always #5 clk = ~clk;

    initial begin
        #0 rst = 1;
        reg_in = `WIDTH'd22;
        shift_en = 0;
        #3 rst = 0;

        #29 shift_en = 1;
        #5 reg_in = 0;


        #100 $stop;



    end


endmodule