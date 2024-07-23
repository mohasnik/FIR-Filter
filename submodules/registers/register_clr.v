module register_clr #(
    parameter bit_width
) (
    input clk, rst, clr,
    input[bit_width-1:0] reg_in,
    output reg[bit_width-1:0] reg_out

);
    
    always @(posedge clk, posedge rst) begin
        if(rst)
            reg_out <= 0;
        else if(clr)
            reg_out <= 0;
        else
            reg_out <= reg_in;
    end


endmodule