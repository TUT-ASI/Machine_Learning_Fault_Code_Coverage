/********************
* Filename:     arbiter.v
* Description:  Packets with the same priority and destined for the same output port are scheduled with a round-robin arbiter with the last served as least priority. 
              Priority direction Local, North, East, South, West
              Maintains the priority till it reads the TAIL flit
              One-hot encoding for state variable
              Output values [5:0]: Output[5:1] -> selection, Output[0] -> idle
*
* $Revision: 26 $
* $Id: arbiter.v 26 2015-11-22 19:24:28Z ranga $
* $Date: 2015-11-22 21:24:28 +0200 (Sun, 22 Nov 2015) $
* $Author: ranga $
*********************/
`timescale 1ns/1ps

`include "parameters.v"
`include "state_defines.v"

module arbiter(clk, rst,
                Lflit_id, Nflit_id, Eflit_id, Wflit_id, Sflit_id,
                Llength, Nlength, Elength, Wlength, Slength,
                Lreq, Nreq, Ereq, Wreq, Sreq,
                nextstate
              );
 
  input         clk, rst;
  input [2:0]   Lflit_id, Nflit_id, Eflit_id, Wflit_id, Sflit_id;
  input [11:0]  Llength, Nlength, Elength, Wlength, Slength;
  input         Lreq, Nreq, Ereq, Wreq, Sreq;
  
  output reg [5:0] nextstate;
  
  // Declaring the local variables
  reg [5:0] currentstate; 
  reg       Lruntimer, Nruntimer, Eruntimer, Wruntimer, Sruntimer;
  
  wire      Ltimesup, Ntimesup, Etimesup, Wtimesup, Stimesup;
    
  // Timer module that runs for the entire packet length
  timer Ltimer (clk, rst, Lflit_id, Llength, Lruntimer, Ltimesup);
  timer Ntimer (clk, rst, Nflit_id, Nlength, Nruntimer, Ntimesup);
  timer Etimer (clk, rst, Eflit_id, Elength, Eruntimer, Etimesup);
  timer Wtimer (clk, rst, Wflit_id, Wlength, Wruntimer, Wtimesup);
  timer Stimer (clk, rst, Sflit_id, Slength, Sruntimer, Stimesup);
  
  // Arbiter - State Machine
  // Current state sequential Logic
  always @ (posedge clk) begin
  if(rst)
    currentstate <= `IDLE;
  else
    currentstate <= nextstate;
  end
  
  // Next state decoder Logic
  always @ (Lreq, Nreq, Ereq, Wreq, Sreq, Ltimesup, Ntimesup, Etimesup, Wtimesup, Stimesup, currentstate) begin
    {Lruntimer, Nruntimer, Eruntimer, Wruntimer, Sruntimer} = 0;
    case(currentstate)
      `IDLE:
        begin
          if(Lreq == 1) begin
            nextstate = `GRANT_L;
          end
          else if(Nreq == 1) begin
            nextstate = `GRANT_N;
          end
          else if(Ereq == 1) begin
            nextstate = `GRANT_E;
          end
          else if(Wreq == 1) begin
            nextstate = `GRANT_W;
          end
          else if (Sreq == 1) begin
            nextstate = `GRANT_S;
          end
          else begin
            nextstate = `IDLE;
          end
        end
        
      `GRANT_L:
        begin
          if(Lreq == 1 && Ltimesup == 0) begin
            Lruntimer = 1;
            nextstate = `GRANT_L;
          end
          else if(Nreq == 1) begin
            nextstate = `GRANT_N;
          end
          else if(Ereq == 1) begin
            nextstate = `GRANT_E;
          end
          else if(Wreq == 1) begin
            nextstate = `GRANT_W;
          end
          else if(Sreq == 1) begin
            nextstate = `GRANT_S;
          end
          else begin
            nextstate = `IDLE;
          end
        end
        
      `GRANT_N:
        begin
          if(Nreq == 1 && Ntimesup == 0) begin
            Nruntimer = 1;
            nextstate = `GRANT_N;
          end
          else if(Ereq == 1) begin
            nextstate = `GRANT_E;
          end
          else if(Wreq == 1) begin
            nextstate = `GRANT_W;
          end
          else if(Sreq == 1) begin
            nextstate = `GRANT_S;
          end
          else if(Lreq == 1) begin
            nextstate = `GRANT_L;
          end
          else begin
            nextstate = `IDLE;
          end
        end
      
      `GRANT_E:
        begin
          if(Ereq == 1 && Etimesup == 0) begin
            Eruntimer = 1;
            nextstate = `GRANT_E;
          end
          else if(Wreq == 1) begin
            nextstate = `GRANT_W;
          end
          else if(Sreq == 1) begin
            nextstate = `GRANT_S;
          end
          else if(Lreq == 1) begin
            nextstate = `GRANT_L;
          end
          else if(Nreq == 1) begin
            nextstate = `GRANT_N;
          end
          else begin
            nextstate = `IDLE;
          end
        end
      
      `GRANT_W:
        begin
          if(Wreq == 1 && Wtimesup == 0) begin
            Wruntimer = 1;
            nextstate = `GRANT_W;
          end
          else if(Sreq == 1) begin
            nextstate = `GRANT_S;
          end
          else if(Lreq == 1) begin
            nextstate = `GRANT_L;
          end
          else if(Nreq == 1) begin
            nextstate = `GRANT_N;
          end
          else if(Ereq == 1) begin
            nextstate = `GRANT_E;
          end
          else begin
            nextstate = `IDLE;
          end
        end
        
      `GRANT_S:
        begin
          if(Sreq == 1 && Stimesup == 0) begin
            Sruntimer = 1;
            nextstate = `GRANT_S;
          end
          else if(Lreq == 1) begin
            nextstate = `GRANT_L;
          end
          else if(Nreq == 1) begin
            nextstate = `GRANT_N;
          end
          else if(Ereq == 1) begin
            nextstate = `GRANT_E;
          end
          else if(Wreq == 1) begin
            nextstate = `GRANT_W;
          end
          else begin
            nextstate = `IDLE;
          end
        end
      
      default:
        begin
          nextstate = `IDLE;
        end
    endcase
  end

endmodule

module timer (clk, rst, flit_id, length, runtimer, timesup);

  input           clk, rst;
  input [2 : 0]   flit_id;
  input [11 : 0]  length;
  input           runtimer;
  
  output reg      timesup;
  
  //Declaring the local variables
  reg [11 : 0]     timeoutclockperiods; // stores packet length
  reg [11 : 0]     count;
  
  // Setting Access time for each request 
  always @ (posedge clk) begin: timeout
    if(rst) begin
      count <= 0;
      timeoutclockperiods <= 0;
    end
    else begin
      if (flit_id == `HEADER) begin
        timeoutclockperiods <= length;
      end
      if (runtimer == 0) begin
        count <= 0;
      end
      else begin
        count <= count + 1;
      end
    end
  end
  
  // Asserting the timesup signal when the access time exceeds timeoutclockperiod
  always @ (count, timeoutclockperiods) begin : timeup
    if (count == timeoutclockperiods)
      timesup = 1;
    else
      timesup = 0;
  end

endmodule

