//===========================================================
//
//			Ali Ekhterachian 400100576
//
//			Implemented Instructions are:
//			R format:  add(u), sub(u), and, or, xor, nor, slt, sltu;
//			I format:  beq, bne, lw, sw, addi(u), slti, sltiu, andi, ori, xori, lui.
//
//===========================================================

`timescale 1ns/1ns

   `define ADD  4'h0
   `define SUB  4'h1
   `define SLT  4'h2
   `define SLTU 4'h3
   `define AND  4'h4
   `define OR   4'h5
   `define NOR  4'h6
   `define XOR  4'h7
   `define LUI  4'h8

module single_cycle_mips 
(
	input clk,
	input reset
);
 
	initial begin
		$display("Single Cycle MIPS Implemention");
		$display("Ali Ekhterachian 400100576");
	end

	reg [31:0] PC;          // Keep PC as it is, its name is used in higher level test bench

   wire [31:0] instr;
   wire [ 5:0] op   = instr[31:26];
   wire [ 5:0] func = instr[ 5: 0];
  // wire [15:0] immediate = instr[15:0];
   wire [31:0] RD1, RD2, AluResult, MemReadData;

   wire AluZero;

   // Control Signals

   wire PCSrc= ((op==6'b000100 & AluZero) | (op==6'b000101 & (!AluZero)));

   reg SZEn, ALUSrc, RegDst, MemtoReg, RegWrite, MemWrite;


   reg [3:0] AluOP;

	
	// CONTROLLER COMES HERE

   always @(*) begin
      SZEn = 1'bx;
      AluOP = 4'hx;
      ALUSrc = (|op);
      RegDst = (~(|op));
      MemtoReg = 1'bx;
      RegWrite = 1'b0;
      MemWrite = 1'b0;
      //PCSrc=1'b0;
      //
      if(~(|op)) begin
         MemtoReg=0;
         case (func)
         6'h20:begin
             AluOP = `ADD;
         end
         6'h21: begin
             AluOP = `ADD;
         end
         6'h22:begin
             AluOP = `SUB;
         end
         6'h23:begin
             AluOP = `SUB;
         end
         6'h24: begin 
            AluOP = `AND;
         end
         6'h25:begin
             AluOP = `OR;
         end
         6'h27: begin
             AluOP = `NOR;
         end
         6'h26:begin
             AluOP = `XOR;
         end
         6'h2a:begin
             AluOP = `SLT;
         end
         6'h2b: begin
            AluOP = `SLTU;
         end
         endcase
         RegWrite=1;
      end else begin
        case(op)
         6'b101011: begin //sw
            SZEn = 1'b1;
            AluOP = `ADD;
            MemWrite=1;

         end
         6'b000100: begin //beq
            SZEn=1;
            ALUSrc=0;
            AluOP=`SUB;
        //    PCSrc=AluZero;
         end
         6'b000101: begin //bne
            SZEn=1;
            ALUSrc=0;
            AluOP=`SUB;
         //   PCSrc=~AluZero;
         end
         6'b100011: begin //lw
            SZEn = 1'b1;
            AluOP = `ADD;
            MemWrite=0;
            MemtoReg=1;
            RegWrite=1;
            
         end

         6'b001000: begin //addi
            SZEn = 1'b1;              
            AluOP = `ADD;
            MemtoReg=0;
            RegWrite=1;
         end
         6'b001001: begin // addiu
            SZEn = 1'b1;              
            AluOP = `ADD;
            MemtoReg=0;
            RegWrite=1;
         end
         6'b001011: begin //sltiu
            SZEn=0;
            AluOP=`SLT;
            MemtoReg=0;
            RegWrite=1; 
         end
         6'b001010: begin //slti
            SZEn=1;
            AluOP=`SLT;
            MemtoReg=0;
            RegWrite=1;
         end
         6'b001100: begin //andi
            SZEn=0;
            AluOP=`ADD;
            MemtoReg=0;
            RegWrite=1;
         end
         6'b001101: begin //ori
                        SZEn=0;
            AluOP=`OR;
            MemtoReg=0;
            RegWrite=1;
         end
         6'b001110: begin //xori
            SZEn=0;
            AluOP=`XOR;
            MemtoReg=0;
            RegWrite=1;
         end
         6'b001111: begin //lui
            SZEn=0;
            AluOP=`LUI;
            MemtoReg=0;
            RegWrite=1;
         end
        endcase 
      end

//      YOU COMPLETE THE REST


   end


	// DATA PATH STARTS HERE

   wire [31:0] Imm32 = SZEn ? {{16{instr[15]}},instr[15:0]} : {16'h0, instr[15:0]};     // ZSEn: 1 sign extend, 0 zero extend

   wire [31:0] PCplus4 = PC + 8'h4;

   wire [31:0] PCbranch = PCplus4 + (Imm32 << 2);

   always @(posedge clk)
      if(reset)
         PC <= 32'h0;
      else
         PC <= PCSrc ? PCbranch : PCplus4;


//========================================================== 
//	instantiated modules
//========================================================== 

// Register File

   reg_file rf
   (
      .clk   ( clk ),
      .write ( RegWrite ),
      .WR    ( RegDst   ? instr[15:11] : instr[20:16]),
      .WD    ( MemtoReg ? MemReadData  : AluResult),
      .RR1   ( instr[25:21] ),
      .RR2   ( instr[20:16] ),
      .RD1   ( RD1 ),
      .RD2   ( RD2 )
	);

   my_alu alu
   (
      .Op( AluOP ),
      .A ( RD1 ),
      .B ( ALUSrc ? Imm32 : RD2),
      .X ( AluResult ),
      .Z ( AluZero )
   );
   


//	Instruction Memory
	async_mem imem			// keep the exact instance name
	(
		.clk		   (1'b0),
		.write		(1'b0),		// no write for instruction memory
		.address	   ( PC ),		   // address instruction memory with pc
		.write_data	(32'bx),
		.read_data	( instr )
	);
	
// Data Memory
	async_mem dmem			// keep the exact instance name
	(
		.clk		   ( clk ),
		.write		( MemWrite ),
		.address	   ( AluResult ),
		.write_data	( RD2 ),
		.read_data	( MemReadData )
	);

endmodule


//==============================================================================

module my_alu(
   input  [3:0] Op,
   input  [31:0] A,
   input  [31:0] B,
   output [31:0] X,
   output        Z
   );

   wire sub = Op != `ADD;
   wire [31:0] bb = sub ? ~B : B;
   wire [32:0] sum = A + bb + sub;
   wire sltu = ! sum[32];

   wire v = sub ?
            ( A[31] != B[31] && A[31] != sum[31] )
          : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * )
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x = A & B;
         `OR  : x = A | B;
         `NOR : x = ~(A | B);
         `XOR : x = A ^ B;
         `LUI : x = {B[15:0], 16'h0};
         default : x = 32'hxxxxxxxx;
      endcase
      
   assign X = x;
   assign Z = x == 32'h00000000;

endmodule

//============================================================================
