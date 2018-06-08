`timescale 1ns/1ps

//changed to synchrounous reset
module y86_seq(
  input clk,
  input rst,
  output [31:0] bus_A,
  input [31:0] bus_in,
  output [31:0] bus_out,
  output bus_WE, bus_RE,
  output [7:0] current_opcode);

  // global control

  reg [5:1] full;  
  wire [4:0] ue={ full[4:1], full[5] };

  always @(posedge clk) begin
    if(rst)
	   full<='b10000;
	 else
      full<={ ue[4], ue[3], ue[2], ue[1], ue[0] };
  end

  // stage 1 IF
  
  reg [31:0] IR;

  always @(posedge clk)
    if(ue[0]) IR<=bus_in;

  // stage 2 ID
  
  reg [31:0] IP, A, B;
  wire [31:0] Aop, Bop;
  wire [7:0] opcode=IR[7:0];
  wire [1:0] mod=IR[15:14];
  reg ZF;
  wire load=opcode=='h8b && mod==1;
  wire move=opcode=='h89 && mod==3;
  wire store=opcode=='h89 && mod==1;
  wire memory=load || store;
  wire add=opcode=='h01;
  wire sub=opcode=='h29;
  wire halt=opcode=='hf4;
  wire aluop=add || sub;
  wire jnez=opcode=='h75;
  wire [4:0] RD=IR[10:8];
  wire [4:0] RS=IR[13:11];
  wire [4:0] Aad=memory?6:RD,
             Bad=RS;
  wire [31:0] distance={ { 24 { IR[15] } }, IR[15:8] };
  wire [31:0] displacement={ { 24 { IR[23] } }, IR[23:16] };
  wire btaken=jnez && !ZF;
  wire [1:0] length=memory                 ?3:
                    (aluop || move || jnez)?2:
                                            1;

  always @(posedge clk)
    if(rst)
	    IP<=0;
    else if(ue[1]) begin
      A<=Aop;
      B<=Bop;
      if(!halt) 
	begin
	  IP<=IP+length+(btaken?distance:0);
	end
      else
	begin
          $finish;
	end
    end
      
  // stage 3 EX
  
  reg [31:0] MAR, MDRw, C;    

  wire [31:0] ALU_op2=memory?displacement:sub?~B:B;
  wire [31:0] ALUout=A+ALU_op2+sub;

  always @(posedge clk)
    if(rst)
	   ZF=0;
    else if(ue[2]) begin
      MAR<=ALUout;
      C<=move?B:ALUout;
      MDRw<=B;
      if(aluop) ZF<=(ALUout==0);
    end
  
  // stage 4 MEM
  
  reg [31:0] MDRr;
  
  always @(posedge clk)
    if(ue[3] && load) MDRr<=bus_in;
      
  assign bus_A=ue[3]?MAR:ue[0]?IP:0;
  assign bus_RE=ue[0] || (ue[3] && load);

  // stage 5 WB
  
  reg [31:0] R[7:0];
  
  assign Aop=R[Aad];
  assign Bop=R[Bad];
  
  assign bus_WE=ue[3] && store;
  assign bus_out=MDRw;

  always @(posedge clk)
    if(rst) begin
	   R[00]<=0; R[01]<=0; R[02]<=0; R[03]<=0; R[04]<=0; R[05]<=0; R[06]<=0; R[07]<=0;      
	 end 
	 else if(ue[4])
           if(aluop || move || load)
		if(load)//rausgezogen
			R[RS]<=MDRr;
		else
             		R[RD]<=C;
				 
  assign current_opcode = opcode;
  
  // ... and now for something completely different.
  // synthesis translate_off
  
  wire [31:0] eax = R[0];
  wire [31:0] ecx = R[1];
  wire [31:0] edx = R[2];
  wire [31:0] ebx = R[3];
  wire [31:0] esp = R[4];
  wire [31:0] ebp = R[5];
  wire [31:0] esi = R[6];
  wire [31:0] edi = R[7];
  wire [7:0] regs = IR[15:8];
  
  // synthesis translate_on

endmodule
