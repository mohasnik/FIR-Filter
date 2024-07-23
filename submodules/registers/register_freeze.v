module register_freeze #(
    parameter bit_width
) (
    input clk, rst, reg_freeze, flush,
    input[bit_width-1:0] reg_in,
    output reg[bit_width-1:0] reg_out

);
    
    always @(posedge clk, posedge rst) begin
        if(rst)
            reg_out <= 0;
        else if(flush)
            reg_out <= 0;
        else if(~reg_freeze)
            reg_out <= reg_in;
    end


endmodule