module counter_TB();

    reg clk = 0, rst;
    reg cnt_en = 0, cnt_clr = 0;
    wire co;
    wire [7 : 0] count;

    counter #(8) UUT(clk, rst, cnt_en, cnt_clr, co, count);

    always #5 clk = ~clk;

    initial begin
        #0 rst = 1;

        #12 rst = 0;

        #13 cnt_en = 1;

        #50 cnt_en = 0;

        #70 cnt_clr = 1;

        #23 cnt_clr = 0;
        cnt_en = 1;

        #52 cnt_clr = 1;
        #37 cnt_clr = 0;


        #100 $stop;



    end

endmodule