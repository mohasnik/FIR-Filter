module shift_register #(
    parameter size, parameter bit_width = 8
) (
    input clk, rst,
    input shift_en,
    input[bit_width-1 : 0] reg_in,
    output[bit_width-1:0] reg_out
);

    reg[bit_width-1:0] registers [0:size-1];

    always @(posedge clk, posedge rst) begin
        if(rst) begin : shift_reg_reset
            
            integer i;

            for(i = 0; i < size; i = i+1) begin : shifting_loop
                registers[i] <= 0;
            end

        end
        else if(shift_en) begin : shift_reg_shift_en
            
            integer i;

            registers[0] <= reg_in;
            for(i = 0; i < size - 1; i = i+1) begin
                registers[i+1] <= registers[i];
            end

        end

    end

    assign reg_out = registers[size-1];

    
endmodule