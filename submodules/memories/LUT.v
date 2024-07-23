`define INITIAL_FILE_ADDRESS "input_files/coeffs_reversed.txt"
module LUT #(
    parameter LUT_size, parameter data_width
) (
    adr,
    data
);
    // -------------------------------------------------------
    // local parameters :
    localparam adress_width = $clog2(LUT_size);

    // input / output :
    input[adress_width-1:0] adr;
    output[data_width-1:0] data;

    // wires and registers :
    reg[data_width-1 : 0] coefs [0 : LUT_size-1];

    // -------------------------------------------------------


    initial begin
        $readmemb(`INITIAL_FILE_ADDRESS, coefs);
    end

    assign data = coefs[adr];

    
endmodule