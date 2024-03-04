`timescale 1ns/100ps

   `define ADD  4'b0000
   `define SUB  4'b0001
   `define SLT  4'b0010
   `define SLTU 4'b0011
   `define AND  4'b0100
   `define XOR  4'b0101
   `define OR   4'b0110
   `define NOR  4'b0111
   `define LUI  4'b1000
   `define J  4'b1001

module multi_cycle_mips(

   input clk,
   input reset,

   // Memory Ports
   output  [31:0] mem_addr,
   input   [31:0] mem_read_data,
   output  [31:0] mem_write_data,
   output         mem_read,
   output         mem_write
);

   // Data Path Registers
   reg MRE, MWE;
   reg [31:0] A, B, PC, IR, MDR, MAR;

   // Data Path Control Lines, donot forget, regs are not always regs !!
   reg setMRE, clrMRE, setMWE, clrMWE;
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, isJal,MDRwrt, MARwrt, multStart;

   // Memory Ports Binding
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Mux & ALU Control Lines
   reg [3:0] aluOp;
   reg [2:0] aluSelB;
   reg [1:0] aluSelA;
   reg SgnExt, MemtoReg, RegDst, IorD;

   // Wiring
   wire aluZero;
   wire [31:0] aluResult, rfRD1, rfRD2;

   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt )
         PC <= #0.1 aluResult;

      if( Awrt ) A <= #0.1 rfRD1;
      if( Bwrt ) B <= #0.1 rfRD2;

      if( MARwrt ) MAR <= #0.1 IorD ? aluResult : PC;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
          else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
          else if( setMWE) MWE <= #0.1 1'b1;
   end

   // Register File
   reg_file rf(
      .clk( clk ),
      .write( RFwrt ),

      .RR1( IR[25:21] ),
      .RR2( IR[20:16] ),
      .RD1( rfRD1 ),
      .RD2( rfRD2 ),

      .WR( isJal?  5'b11111 :(RegDst ? IR[15:11] : IR[20:16])),
      .WD( MemtoReg ? MDR : aluResult )
   );
   wire[63:0] Product;

   // Sign/Zero Extension
   wire [31:0] SZout =SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};

   // ALU-A Mux
   wire [31:0] aluA = aluSelA[1]? (aluSelA[0] ? Product[31:0] : Product[63:32]):(aluSelA[0] ? A : PC);

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (aluSelB)
      3'b00: aluB = B;
      3'b01: aluB = 32'h4;
      3'b10: aluB = SZout;
      3'b11: aluB = SZout << 2;
      3'b100: aluB ={4'b0000,IR[25:0],2'b00};
      3'b101: aluB=32'b0;
   endcase

   my_alu alu(
      .A( aluA ),
      .B( aluB ),
      .Op( aluOp ),

      .X( aluResult ),
      .Z( aluZero )
   );

   wire ready;
   multiplier4 multiplier(clk, multStart, A, B, Product, ready);

   // Controller Starts Here

   // Controller State Registers
   reg [4:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_ALU_R = 7, EX_ALU_I = 8,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_BRA_1 = 25, EX_BRA_2 = 26,
      EX_JR_1=27, EX_JAL_1=30,
      EX_MULTU_1=28, EX_MULTU_2=29;
      
      

   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         IorD = 0;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin

      nxt_state = 'bx;

      SgnExt = 'bx; IorD = 'bx;
      MemtoReg = 'bx; RegDst = 'bx;
      aluSelA = 'bx; aluSelB = 'bx; aluOp = 'bx;
      isJal=0;
      PCwrt = 0;multStart=0;
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;

      case(state)

         RESET:
            PrepareFetch;

         FETCH1:
            nxt_state = FETCH2;

         FETCH2:
            nxt_state = FETCH3;

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            clrMRE = 1;
            aluSelA = 0;
            aluSelB = 2'b01;
            aluOp = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000:             // R-format
                  case( IR[5:3] )
                     3'b000: ;
                     3'b001:
                     if(IR[2:0]==3'b000)
                        nxt_state =EX_JR_1 ;
                     else if(IR[2:0]==3'b001) begin//jalR
                        aluSelA=0;
                        aluSelB=5;
                        aluOp = `OR;
                        MemtoReg=0;
                        isJal=1;
                        RFwrt=1;
                        nxt_state = EX_JR_1;
                     end
                     3'b010: begin
                        aluSelA={1'b1,IR[1]};
                        aluSelB=5;
                        aluOp=`OR;
                        MemtoReg=0;
                        RegDst=1;
                        RFwrt=1;
                        PrepareFetch;
                     end
                     3'b011: nxt_state=EX_MULTU_1 ;
                     3'b100: nxt_state = EX_ALU_R;
                     3'b101: nxt_state = EX_ALU_R;
                     3'b110: ;
                     3'b111: ;
                  endcase

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_111,             //LUI
               6'b001_110:             // xori
                  nxt_state = EX_ALU_I;

               6'b100_011:
                  nxt_state = EX_LW_1;

               6'b101_011:
                  nxt_state = EX_SW_1;

               6'b000_100,
               6'b000_101:
                  nxt_state = EX_BRA_1;
               // rest of instructiones should be decoded here

               6'b000_010:begin//j
                  aluSelA=0;
                  aluSelB=4;
                  aluOp = `J;
                  PCwrt=1;
                  IorD = 1;
                  setMRE = 1;
                  MARwrt = 1;
                  nxt_state = FETCH1;
               end
               6'b000_011:begin//jal
                  aluSelA=0;
                  aluSelB=5;
                  aluOp = `OR;
                  MemtoReg=0;
                  isJal=1;
                  RFwrt=1;
                  nxt_state = EX_JAL_1;
               end               

            endcase
         end

         EX_ALU_R: begin
            aluSelA=1;
            aluSelB=0;
            if(IR[5:3]==3'b100)
            case( IR[2:0])
               3'b000: aluOp = `ADD;
               3'b001: aluOp = `ADD;
               3'b010: aluOp = `SUB;
               3'b011: aluOp = `SUB;
               3'b100: aluOp = `AND;
               3'b101: aluOp = `OR;
               3'b110: aluOp = `XOR;
               3'b111: aluOp = `NOR;                           
            endcase
            else if(IR[5:3]==3'b101)
               case( IR[2:0])
                  3'b010: aluOp = `SLT;
                  3'b011: aluOp = `SLTU;                           
            endcase
            MemtoReg=0;
            RegDst=1;
            RFwrt=1;
            PrepareFetch;
         end

         EX_ALU_I: begin
            aluSelA=1;
            aluSelB=2;
            case(IR[31:26])
               6'b001000: begin //addi
                  SgnExt = 1'b1;              
                  aluOp = `ADD;
               end
               6'b001001: begin // addiu
                  SgnExt = 1'b1;              
                  aluOp = `ADD;
               end
               6'b001011: begin //sltiu
                  SgnExt=1;
                  aluOp=`SLTU;
               end
               6'b001010: begin //slti
                  SgnExt=1;
                  aluOp=`SLT;
               end
               6'b001100: begin //andi
                  SgnExt=0;
                  aluOp=`AND;
               end
               6'b001101: begin //ori
                  SgnExt=0;
                  aluOp=`OR;
               end
               6'b001110: begin //xori
                  SgnExt=0;
                  aluOp=`XOR;
               end
               6'b001_111 :begin
                  SgnExt=0;
                  aluOp=`LUI;
               end                   
            endcase
            MemtoReg=0;
            RegDst=0;
            RFwrt=1;
            PrepareFetch;
         end


         EX_LW_1: begin
            SgnExt=1;
            aluOp = `ADD;
            aluSelA=1;
            aluSelB=2'b10;
            IorD=1;
            setMRE=1;
            MARwrt=1;
            nxt_state=EX_LW_2;
         end
         EX_LW_2:nxt_state=EX_LW_3;
         EX_LW_3:nxt_state=EX_LW_4;

         EX_LW_4: begin
            MDRwrt=1;
            clrMRE=1;
            nxt_state=EX_LW_5;
         end         
         EX_LW_5: begin
            MDRwrt=0;
            RegDst=0;
            MemtoReg=1;
            RFwrt=1;
            PrepareFetch;
         end     


         EX_SW_1: begin
            SgnExt=1;
            aluOp = `ADD;
            aluSelA=1;
            aluSelB=2'b10;
            IorD=1;
            setMWE=1;
            MARwrt=1;
            nxt_state=EX_SW_2;
         end

         EX_SW_2: begin
            clrMWE = 1;
            nxt_state=EX_SW_3;
         end
         EX_SW_3: begin
            PrepareFetch;
         end         

         EX_BRA_1: begin
            aluSelA=1;
            aluSelB=0;
            aluOp = `SUB;
            if(aluZero ^ IR[26])
               nxt_state = EX_BRA_2;
            else
               PrepareFetch;
         end
         EX_BRA_2: begin
            SgnExt=1;
            aluSelA=0;
            aluSelB=3;
            aluOp=`ADD;
            PCwrt=1;
            
            IorD = 1;
            setMRE = 1;
            MARwrt = 1;
            nxt_state = FETCH1;
         end
         
         EX_JR_1: begin
            aluSelA=1;
            aluSelB=5;
            aluOp=`OR;
            PCwrt=1;
            
            IorD = 1;
            setMRE = 1;
            MARwrt = 1;
            nxt_state = FETCH1;
         end

         EX_MULTU_1:begin
            multStart=1;
            nxt_state=EX_MULTU_2;
         end
         
         EX_MULTU_2: begin
            if(ready)
	            PrepareFetch;
	         else
	            nxt_state = EX_MULTU_2;
         end
         EX_JAL_1:begin
                              aluSelA=0;
                  aluSelB=4;
                  aluOp = `J;
                  PCwrt=1;
                  IorD = 1;
                  setMRE = 1;
                  MARwrt = 1;
                  nxt_state = FETCH1;
         end



      endcase

   end

endmodule

//==============================================================================

module my_alu(
   input [3:0] Op,
   input [31:0] A,
   input [31:0] B,

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
   wire[31:0] jumpA = A & 32'hF0000000;

   reg [31:0] x;

   always @( * )
      case( Op )
         `LUI : x= B<<16;
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         `J : x =   jumpA | B;

         default : x = 32'hxxxxxxxx;
      endcase

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;

endmodule

//==============================================================================

module reg_file(
   input clk,
   input write,
   input [4:0] WR,
   input [31:0] WD,
   input [4:0] RR1,
   input [4:0] RR2,
   output [31:0] RD1,
   output [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

//==============================================================================


module multiplier4(
   input clk,  
   input start,
   input [31:0] A, 
   input [31:0] B, 
   output reg [63:0] Product,
   output ready
    );

//----------------------------------- register deceleration
reg [31:0] Multiplicand ;
reg [5:0]  counter;

//------------------------------------- wire deceleration
wire product_write_enable;
wire [32:0] adder_output;
wire [32:0] lefts;
//-------------------------------------- combinational logic
assign ready = counter[5];
assign lefts= Product[63:32];
assign adder_output = Multiplicand +lefts;
assign product_write_enable = Product[0];

//--------------------------------------- sequential Logic
always @ (posedge clk)

   if(start) begin
      counter <= 6'h0 ;
      Multiplicand <= A ;
      Product <= {32'h00, B};
   end

   else if(! ready) begin
         counter <= counter + 1;
         Product <= Product >> 1;

      if(product_write_enable)
         Product[63:31] <= adder_output;
end   

endmodule