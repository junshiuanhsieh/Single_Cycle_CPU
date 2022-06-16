// Your code
module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I);

    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output reg [31:0] mem_addr_D ;
    output reg [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;
    
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    reg   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    reg   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    reg   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg
    wire   [ 1:0] ALUOp;
    wire   [ 3:0] ALUaction;
    wire   [31:0] ALUin_B;
    wire   [31:0] ImmGen;
    wire          Branch;
    wire          MemRead;
    wire          MemtoReg;
    wire          MemWrite;
    wire          ALUSrc;
    wire          RegWrite;
    wire          jal;
    wire          jalr;
    wire          auipc;

    parameter S_IF = 3'd0, S_ID = 3'd1, S_EX = 3'd2, S_ME = 3'd3, S_WB = 3'd4;
    reg [2:0] state, state_nxt;
    wire [31:0] alu_result;
    wire [1:0] alu_compare;
    wire mul_ready;
    wire [31:0] mul_result;

    assign mem_addr_I = PC;
    assign ALUin_B = ALUSrc ? ImmGen : rs2_data;
    assign mem_wen_D = (MemWrite && (state == S_ME));
    assign regWrite = (state == S_WB) ? RegWrite : 0;

    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//

    control control0(
        .instruction(mem_rdata_I[6:0]),
        .Branch(Branch),
        .MemRead(MemRead),
        .MemtoReg(MemtoReg),
        .MemWrite(MemWrite),
        .ALUSrc(ALUSrc),
        .RegWrite(RegWrite),
        .jal(jal),
        .jalr(jalr),
        .auipc(auipc),
        .ALUOp(ALUOp)
    );

    IMMgenerator immgen0(
        .instruction(mem_rdata_I),
        .Imm(ImmGen)
    );

    ALUcontrol ALUcontrol0(
        .ALUOp(ALUOp),
        .funct3(mem_rdata_I[14:12]),
        .funct7_30(mem_rdata_I[30]),
        .funct7_25(mem_rdata_I[25]),
        .ALUaction(ALUaction)
    );

    ALU alu0(
        .mode(ALUaction),       
        .in_A(rs1_data),    
        .in_B(ALUin_B),      
        .result(alu_result),  
        .compare(alu_compare)
    );

    mulDiv muldiv0(
        .clk(clk),
        .rst_n(rst_n),
        .valid(state == S_EX && ALUaction[3:2] == 2'b11),
        .mode(ALUaction[0]),  //mul : 4'b1100, div : 4'b1101  
        .in_A(rs1_data), 
        .in_B(ALUin_B),
        .ready(mul_ready),
        .out(mul_result)
    );  

    // Todo: any combinational/sequential circuit
    always @(*) begin
        state_nxt = state;
        case(state)
            S_IF : state_nxt = S_ID;
            S_ID : state_nxt = S_EX;
            S_EX : begin
                if(ALUaction[3:2] == 2'b11) begin
                    if (mul_ready) state_nxt = S_ME;
                end
                else state_nxt = S_ME;
            end
            S_ME : state_nxt = S_WB;
            S_WB : state_nxt = S_IF;
        endcase
    end

    always @(*) begin
        PC_nxt = PC;
        rs1 = rs1;
        rs2 = rs2;
        rd = rd;
        rd_data = rd_data;
        mem_wdata_D = mem_wdata_D;
        mem_addr_D = mem_addr_D;
        case(state)
            S_IF : begin

            end
            S_ID : begin
                rs1 = mem_rdata_I[19:15];
                rs2 = mem_rdata_I[24:20];
                rd = mem_rdata_I[11:7];
            end
            S_EX : begin

            end
            S_ME : begin
                mem_addr_D = alu_result;
                mem_wdata_D = rs2_data;
            end
            S_WB : begin
                if(auipc) rd_data = PC + (ImmGen << 12);
                else if(jal) rd_data = PC + 3'd4;
                else rd_data = (MemtoReg)? mem_rdata_D : (ALUaction[3:2] == 2'b11)? mul_result : alu_result;

                if (jalr) PC_nxt = alu_result;
                else if(jal) PC_nxt = PC + $signed(ImmGen << 1);
                else if(Branch && alu_compare == 2'd1) PC_nxt = PC + $signed(ImmGen << 1);
                else if(Branch && alu_compare == 2'd2 && mem_rdata_I[14:12] == 3'b101) PC_nxt = PC + $signed(ImmGen << 1);
                else if(Branch && alu_compare == 2'd3 && mem_rdata_I[14:12] == 3'b100) PC_nxt = PC + $signed(ImmGen << 1);
                // else if(auipc) PC_nxt = PC + (ImmGen << 12);
                else PC_nxt = PC + 3'd4;
            end
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            state <= 3'b0;
        end
        else begin
            PC <= PC_nxt;
            state <= state_nxt;
        end
    end
endmodule

module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end
    end
endmodule

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    input clk, rst_n;
    input valid;
    input mode;       // mode 0: mul, 1: div;
    input [31:0] in_A, in_B;
    output ready;
    output [31:0] out;

    // Definition of states
    parameter IDLE = 3'd0;
    parameter MUL  = 3'd1;
    parameter DIV  = 3'd2;
    parameter OUT  = 3'd3;

    // Wire and reg
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;
    reg  [32:0] alu;

    // assign output
    assign ready = (state == OUT);
    assign out = shreg[31:0];

    //FSM
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) begin
                    if (mode == 2'd0) state_nxt = MUL;
                    else if (mode == 2'd1) state_nxt = DIV;
                    else state_nxt = IDLE;
                end
                else state_nxt = IDLE; 
            end
            MUL : state_nxt = (counter == 5'd31) ? OUT : MUL; 
            DIV : state_nxt = (counter == 5'd31) ? OUT : DIV;
            OUT : state_nxt = IDLE;
            default : state_nxt = IDLE;
        endcase
    end

    // Counter
    always @(*) begin
        if (state == MUL || state == DIV) counter_nxt = counter + 1;
        else counter_nxt = 5'd0;
    end

    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // ALU output
    always @(*)begin
        case(state)
            IDLE: alu_out = 33'd0; 
            MUL: alu_out = (shreg[0]) ? alu_in + shreg[63:32] : shreg[63:32];
            DIV: begin 
                if (shreg[63:32] >= alu_in) begin 
                    alu_out = shreg[63:32] - alu_in;
                    alu_out[32] = 1'b1;
                end
                else begin 
                    alu_out = shreg[63:32];
                    alu_out[32] = 1'b0;
                end
            end
            OUT : alu_out = 32'd0;  
            default : alu_out = 32'd0;
        endcase
    end

    // Shift register
    always @(*) begin 
        shreg_nxt = shreg;
        if (state == IDLE && valid == 1'd1) begin
            if (state_nxt == DIV) shreg_nxt = in_A << 1;
            else shreg_nxt = in_A;
        end
        else if (state == MUL) begin  
            shreg_nxt = shreg >> 1;
            shreg_nxt[63:31] = alu_out;
        end
        else if (state == DIV) begin
            shreg_nxt = shreg;
            shreg_nxt[63:32] = alu_out[31:0];
            shreg_nxt =  shreg_nxt << 1;
            shreg_nxt[0] = alu_out[32];
            
            if (counter == 5'd31) shreg_nxt[63:32] = shreg_nxt[63:32] >> 1; 
        end
        // else shreg_nxt[32:0] = alu_out;
    end

    // Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            shreg <= 64'd0;
            counter <= 5'd0;
            alu_in <= 32'd0;
        end
        else begin
            state <= state_nxt;
            shreg <= shreg_nxt;
            counter <= counter_nxt;
            alu_in <= alu_in_nxt;
        end
    end
endmodule

module ALU(mode, in_A, in_B, result, compare);
    input [3:0] mode;        // ALU control
    input [31:0] in_A;       // in_A: data from rs1
    input [31:0] in_B;       // in_B: data from rs2 or imm
    output [31:0] result;    // ALU result
    output [1:0] compare;    // branch compare signal
                             // 1: rs1 == rs2 (beq)
                             // 2: rs1 >= rs2 (bge)
                             // 3: rs1 <= rs2 (blt) 
                                               
    // Definition of different modes
    parameter AND       = 4'b0000;
    parameter OR        = 4'b0001;
    parameter ADD       = 4'b0010;
    parameter SUB       = 4'b0110;  
    parameter XOR       = 4'b0111;
    parameter SRLI      = 4'b1000;  // shift right immediate
    parameter SLLI      = 4'b1001;  // shift left immediate
    parameter SLTI      = 4'b1010;  // set < immediate

    // Wire and reg
    reg  [31:0] alu_out;

    // assign output
    assign result = alu_out;
    assign compare = (mode == SUB)? ((alu_out == 1'd0)? 2'd1 : ((alu_out[31] == 1'd0)? 2'd2 : 2'd3)) : 1'd0; //equal:1, A>=B:2, A<B:3, else:0


    // ALU output 
    always @(*)begin
        case(mode)
        AND: alu_out= in_A & in_B;
        OR : alu_out= in_A | in_B;
        ADD: alu_out= $signed(in_A) + $signed(in_B);
        SUB: alu_out= $signed(in_A) - $signed(in_B);
        XOR: alu_out= in_A ^ in_B;
        SRLI: alu_out = in_A >> in_B;
        SLLI: alu_out = in_A << in_B;
        SLTI: alu_out = (in_A < in_B);
        default: alu_out = 1'd0;
        endcase 
    end
    
endmodule

module control(
    input [6:0] instruction,
    output reg  Branch,
    output reg  MemRead,
    output reg  MemtoReg,
    output reg  MemWrite,
    output reg  ALUSrc,
    output reg  RegWrite,
    output reg  jal,
    output reg  jalr,
    output reg  auipc,
    output reg  [1:0] ALUOp
);

    always @(*) begin
        case(instruction)
            7'b0010111: begin  //auipc
                ALUSrc      = 1'b1;
                MemtoReg    = 1'b0;
                RegWrite    = 1'b1;
                MemRead     = 1'b0;
                MemWrite    = 1'b0;
                Branch      = 1'b0;
                jal         = 1'b0;
                jalr        = 1'b0;
                auipc       = 1'b1;
                ALUOp       = 2'bx;         
            end
            7'b1101111: begin  //jal
                ALUSrc      = 1'b1;
                MemtoReg    = 1'b0;
                RegWrite    = 1'b1;
                MemRead     = 1'b0;
                MemWrite    = 1'b0;
                Branch      = 1'b0;
                jal         = 1'b1;
                jalr        = 1'b0;
                auipc       = 1'b0;
                ALUOp       = 2'bx;         
            end
            7'b1100111: begin  //jalr
                ALUSrc      = 1'b1;
                MemtoReg    = 1'b0;
                RegWrite    = 1'b1;
                MemRead     = 1'b0;
                MemWrite    = 1'b0;
                Branch      = 1'b0;
                jal         = 1'b0;
                jalr        = 1'b1;
                auipc       = 1'b0;
                ALUOp       = 2'd3;         
            end
            7'b1100011: begin  //beq
                ALUSrc      = 1'b0;
                MemtoReg    = 1'bx;
                RegWrite    = 1'b0;
                MemRead     = 1'b0;
                MemWrite    = 1'b0;
                Branch      = 1'b1;
                jal         = 1'b0;
                jalr        = 1'b0;
                auipc       = 1'b0;
                ALUOp       = 2'b1;         
            end
            7'b0000011: begin  //lw
                ALUSrc      = 1'b1;
                MemtoReg    = 1'b1;
                RegWrite    = 1'b1;
                MemRead     = 1'b1;
                MemWrite    = 1'b0;
                Branch      = 1'b0;
                jal         = 1'b0;
                jalr        = 1'b0;
                auipc       = 1'b0;
                ALUOp       = 2'd0;         
            end
            7'b0100011: begin  //sw
                ALUSrc      = 1'b1;
                MemtoReg    = 1'bx;
                RegWrite    = 1'b0;
                MemRead     = 1'b0;
                MemWrite    = 1'b1;
                Branch      = 1'b0;
                jal         = 1'b0;
                jalr        = 1'b0;
                auipc       = 1'b0;
                ALUOp       = 2'd0;         
            end
            7'b0010011: begin  //addi, slti, srai, slli
                ALUSrc      = 1'b1;
                MemtoReg    = 1'b0;
                RegWrite    = 1'b1;
                MemRead     = 1'b0;
                MemWrite    = 1'b0;
                Branch      = 1'b0;
                jal         = 1'b0;
                jalr        = 1'b0;
                auipc       = 1'b0;
                ALUOp       = 2'd3;         
            end
            7'b0110011: begin  //R_type
                ALUSrc      = 1'b0;
                MemtoReg    = 1'b0;
                RegWrite    = 1'b1;
                MemRead     = 1'b0;
                MemWrite    = 1'b0;
                Branch      = 1'b0;
                jal         = 1'b0;
                jalr        = 1'b0;
                auipc       = 1'b0;
                ALUOp       = 2'd2;         
            end
            default: begin  
                ALUSrc      = 1'b0;
                MemtoReg    = 1'b0;
                RegWrite    = 1'b0;
                MemRead     = 1'b0;
                MemWrite    = 1'b0;
                Branch      = 1'b0;
                jal         = 1'b0;
                jalr        = 1'b0;
                auipc       = 1'b0;
                ALUOp       = 2'd0;         
            end
        endcase
    end
endmodule

module ALUcontrol(
    input       [1:0]   ALUOp,
    input       [2:0]   funct3,
    input               funct7_30,
    input               funct7_25,
    output reg  [3:0]   ALUaction
    //output              mul_div_mode
);

    parameter AND       = 4'b0000;
    parameter OR        = 4'b0001;
    parameter ADD       = 4'b0010;
    parameter SUB       = 4'b0110;  
    parameter XOR       = 4'b0111;
    parameter SRAI      = 4'b1000;  // shift right immediate
    parameter SLLI      = 4'b1001;  // shift left immediate
    parameter SLTI      = 4'b1010;  // set < immediate
    parameter MUL       = 4'b1100;
    parameter DIV       = 4'b1101;

    always @(*) begin
        case(ALUOp)
            2'b00: begin
                ALUaction = ADD;
            end
            2'b01: begin
                ALUaction = SUB;
            end
            2'b10: begin
                if      (funct3 == 3'b111) ALUaction = AND;
                else if (funct3 == 3'b110) ALUaction = OR;
                else if (funct3 == 3'b100) ALUaction = funct7_25 ? DIV : XOR;
                else begin // 3'b000
                    if(funct7_25) ALUaction = MUL;
                    else ALUaction = funct7_30 ? SUB : ADD;
                end
            end
            2'b11: begin
                if      (funct3 == 3'b010) ALUaction = SLTI;
                else if (funct3 == 3'b101) ALUaction = SRAI;
                else if (funct3 == 3'b001) ALUaction = SLLI;
                else ALUaction = ADD;   
            end
        endcase

        //case(funct3)
        //    3'b000: begin  //sub, add, addi,jalr
        //        ALUaction <= (ALUOp == 2'd3) ? 4'b0010 : (ALUOp == 2'd1) ? 4'b0110 : funct7_25 ? 4'b1100 : funct7_30 ? 4'b0110 : 4'b0010;
        //    end
        //    3'b111: begin  //and
        //        ALUaction <= 4'b0000;
        //    end
        //    3'b110: begin  //or
        //        ALUaction <= 4'b0001;
        //    end
        //    3'b100: begin  //xor
        //        ALUaction <= funct7_25 ? 4'b1101 : 4'b0111;
        //    end
        //    3'b010: begin  //slti
        //        ALUaction <= (ALUOp == 2'b00) ? 4'b0010 : 4'b1010;
        //    end
        //    3'b101: begin  //srai
        //        ALUaction <= 4'b1001;
        //    end
        //    3'b001: begin  //slli
        //        ALUaction <= 4'b1000;
        //    end
        //    default: begin
        //        ALUaction <= 4'b0010;
        //    end
        //endcase
    end
endmodule

module IMMgenerator(
    input      [31:0]  instruction,
    output reg [31:0]  Imm
);
    always @(*) begin
        case(instruction[6:0])
            7'b0010111: begin  //auipc
                Imm <= {{11{instruction[31]}}, instruction[31:12]};
            end
            7'b1101111: begin  //jal
                Imm <= {{11{instruction[31]}}, instruction[31], instruction[19:12], 
                               instruction[20], instruction[30:21]};
            end
            7'b1100111: begin  //jalr
                Imm <= {{20{instruction[31]}}, instruction[31:20]};
            end
            7'b1100011: begin  //beq
                Imm <= {{20{instruction[31]}}, instruction[31],    instruction[7], 
                               instruction[30:25], instruction[11:8]};
            end
            7'b0000011: begin  //lw
                Imm <= {{20{instruction[31]}}, instruction[31:20]};
            end
            7'b0100011: begin  //sw
                Imm <= {{20{instruction[31]}}, instruction[31:25], instruction[11:7]};
            end
            7'b0010011: begin  //addi, slti, srai, slli
                Imm <= {{20{instruction[31]}}, instruction[31:20]};
            end
            default: begin  
                Imm <= {30'b0};
            end

        endcase
    end
endmodule
