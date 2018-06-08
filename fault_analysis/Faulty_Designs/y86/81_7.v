`timescale 1ns/1ps
module y86_seq (input clk, input rst, output [31:0] bus_A, input [31:0] bus_in, output [31:0] bus_out, output bus_WE , bus_RE, output [7:0] current_opcode)  ;
  reg[5:1] full;
  wire[4:0] ue = { full[4:1], full[5] };
  always
    @( posedge clk )
      begin
        if( rst )
          full <= 'b010000;
        else
          full <= { ue[4], ue[3], ue[2], ue[1], ue[0] };
      end
  reg[31:0] IR;
  always
    @( posedge clk )
      if( ue[0] )
        IR <= bus_in;
  reg[31:0] IP , A , B;
  wire[31:0] Aop , Bop;
  wire[7:0] opcode = IR[7:0];
  wire[1:0] mod = IR[15:14];
  reg ZF;
  wire load = ( ( opcode == 'b010001011 ) && ( mod == 1 ) );
  wire move = ( ( opcode == 'b010001001 ) && ( mod == 3 ) );
  wire store = ( ( opcode == 'b010001001 ) && ( mod == 1 ) );
  wire memory = ( load || store );
  wire add = ( opcode == 'b01 );
  wire sub = ( opcode == 'b0101001 );
  wire halt = ( opcode == 'b011110100 );
  wire aluop = ( add || sub );
  wire jnez = ( opcode == 'b01110101 );
  wire[4:0] RD = IR[10:8];
  wire[4:0] RS = IR[13:11];
  wire[4:0] Aad = ( memory ? 6 : RD ) , Bad = RS;
  wire[31:0] distance = { { 24 { IR[15] }}, IR[15:8] };
  wire[31:0] displacement = { { 24 { IR[23] }}, IR[23:16] };
  wire btaken = ( jnez && ( !ZF ) );
  wire[1:0] length = ( memory ? 3 : ( ( ( aluop || move ) || jnez ) ? 2 : 1 ) );
  always
    @( posedge clk )
      if( rst )
        IP <= 0;
      else
        if( ue[1] )
          begin
            A <= Aop;
            B <= Bop;
            if( ( !halt ) )
              begin
                IP <= ( ( IP + length ) + ( btaken ? distance : 0 ) );
              end
            else
              begin
                $finish;
              end
          end
  reg[31:0] MAR , MDRw , C;
  wire[31:0] ALU_op2 = ( memory ? displacement : ( sub ? ( ~B ) : B ) );
  wire[31:0] ALUout = ( ( A + ALU_op2 ) + sub );
  always
    @( posedge clk )
      if( rst )
        ZF = 0;
      else
        if( ue[2] )
          begin
            MAR <= ALUout;
            C <= ( 0 ? B : ALUout );
            MDRw <= B;
            if( aluop )
              ZF <= ( ALUout == 0 );
          end
  reg[31:0] MDRr;
  always
    @( posedge clk )
      if( ( ue[3] && load ) )
        MDRr <= bus_in;
  assign bus_A = ( ue[3] ? MAR : ( ue[0] ? IP : 0 ) ) ;
  assign bus_RE = ( ue[0] || ( ue[3] && load ) ) ;
  reg[31:0] R [7:0];
  assign Aop = R[Aad] ;
  assign Bop = R[Bad] ;
  assign bus_WE = ( ue[3] && store ) ;
  assign bus_out = MDRw ;
  always
    @( posedge clk )
      if( rst )
        begin
          R[0] <= 0;
          R[1] <= 0;
          R[2] <= 0;
          R[3] <= 0;
          R[4] <= 0;
          R[5] <= 0;
          R[6] <= 0;
          R[7] <= 0;
        end
      else
        if( ue[4] )
          if( ( ( aluop || move ) || load ) )
            if( load )
              R[RS] <= MDRr;
            else
              R[RD] <= C;
  assign current_opcode = opcode ;
endmodule

