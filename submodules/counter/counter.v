// -------------------------------------------------------------

// Module: counter
// Description:
// A counter to use as frequency divider for PRNG unit.
// the counter can be initialized by the init port for proper clock division.

// -------------------------------------------------------------



module Counter #(
    parameter size = 12
)(
    input clk, rst, 
    input increament, clear,
    input wire[size - 1 : 0] init,
	output Co,
    output reg[size-1:0] count
);


always @(posedge clk, posedge rst) begin
    if (rst)
        count <= init;
    else if(clear)
        count <= init;
    else if(increament)
        count <= count + 1;
end

assign Co = &{count};

endmodule
