module FIR_CT (
    input clk, rst, input_valid, cnt_done, sum_ready,
    output reg get_input, shift_en, flush, 
            cnt_clr, cnt_en, result_freeze,
    output reg output_valid
);

    parameter[2:0] STATE_IDLE = 0, STATE_GET_INPUT = 1, STATE_CALC = 2, STATE_WAIT_SUM = 3, STATE_READY = 4;
    reg[2:0] ps, ns;


    // next state assignment block
    always @(ps, input_valid, cnt_done, sum_ready) begin
        ns = STATE_IDLE;
        
        case (ps)
            
            STATE_IDLE : ns = input_valid ? STATE_GET_INPUT : STATE_IDLE;

            STATE_GET_INPUT : ns = STATE_CALC;

            STATE_CALC : ns = cnt_done ? STATE_WAIT_SUM : STATE_CALC;
            
            STATE_WAIT_SUM : ns = sum_ready ? STATE_READY : STATE_WAIT_SUM;
            
            STATE_READY : ns = STATE_IDLE;

        endcase
        
    end

    always @(ps, input_valid, cnt_done, sum_ready) begin

        {get_input, shift_en, flush, cnt_clr, cnt_en, result_freeze, output_valid} = 7'd0;

        case (ps)
            
            STATE_IDLE : begin
                cnt_clr = 1;
            end

            STATE_GET_INPUT : begin
                get_input = 1;
                cnt_clr = 1;
                shift_en = 1;
                flush = 1;
            end

            STATE_CALC : begin
                shift_en = 1;
                cnt_en = 1;
            end

            STATE_READY : begin
                result_freeze = 1;
                output_valid = 1;
            end

        endcase



    end

    always @(posedge clk, posedge rst) begin
        if(rst)
            ps <= STATE_IDLE;
        else    
            ps <= ns;
    end


endmodule