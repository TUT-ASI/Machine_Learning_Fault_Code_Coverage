// -------------------------------------------
//  THIS FILE IS GENERATED AUTOMATICALLY    --
//            DO NOT EDIT                   --
// -------------------------------------------
// Copyright (C) 2017  Siavoosh Payandeh Azad 
// License: GNU GENERAL PUBLIC LICENSE Version 3 

`timescale 1ns/1ps

module arbiter_tb;

logic [5:0] nextstate;
logic [2:0] lflit_id, nflit_id, eflit_id, wflit_id, sflit_id = {3'b000, 3'b000, 3'b000, 3'b000, 3'b000};
logic [11:0] llength, nlength, elength, wlength, slength = 0;
logic lreq, nreq, ereq, wreq, sreq = 0;
logic clk, rst = 1;

parameter clk_period = 10;

// clock generation!
  initial begin
    clk = 1;
    forever
      #(clk_period/2) clk = ~clk;
  end

task reset;
    {lflit_id, nflit_id, eflit_id, wflit_id, sflit_id} = {3'b000, 3'b000, 3'b000, 3'b000, 3'b000};
    {llength,  nlength,  elength,  wlength,  slength}  = 0;
    {lreq,     nreq,     ereq,     wreq,     sreq}     = 0;
endtask


// instantiate the compoent
arbiter DUT (clk, rst, lflit_id, nflit_id, eflit_id, wflit_id, sflit_id, llength, nlength, elength, wlength, slength, lreq, nreq, ereq, wreq, sreq, nextstate);

// Applying the stimuli - Start the simulation
    initial begin : SIM

        reset();
        #(15)
        rst <= 0;         lflit_id[2] <= 1;         lreq <= 1;         nreq <= 0;         ereq <= 0;         wreq <= 0;         sreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[2] <= 1;         sreq <= 1; 
        #(10)
    
        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[2] <= 0;         lflit_id[1] <= 0;         nflit_id[2] <= 0;         eflit_id[2] <= 0;         wflit_id[2] <= 0;         sflit_id[2] <= 0;         sreq <= 1; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[0] <= 1;         lreq <= 0;         nreq <= 0;         ereq <= 1;         sreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[0] <= 1;         lreq <= 0;         nreq <= 0;         ereq <= 0;         wreq <= 1;         sreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[0] <= 1;         nreq <= 1;         sreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[0] <= 0;         nflit_id[0] <= 0;         eflit_id[0] <= 0;         wflit_id[0] <= 0;         sflit_id[0] <= 0;         lreq <= 1;         nreq <= 1;         wreq <= 0;         sreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[0] <= 0;         nflit_id[0] <= 0;         eflit_id[0] <= 0;         wflit_id[0] <= 0;         sflit_id[0] <= 0;         lreq <= 0;         nreq <= 1;         ereq <= 1;         wreq <= 0;         sreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[0] <= 0;         nflit_id[0] <= 0;         eflit_id[0] <= 0;         wflit_id[0] <= 0;         sflit_id[0] <= 0;         lreq <= 0;         nreq <= 0;         ereq <= 1;         wreq <= 1;         sreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[0] <= 0;         nflit_id[0] <= 0;         eflit_id[0] <= 0;         wflit_id[0] <= 0;         sflit_id[0] <= 0;         nreq <= 1;         wreq <= 1;         sreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[2] <= 1;         lflit_id[0] <= 0;         nflit_id[0] <= 0;         eflit_id[0] <= 0;         wflit_id[0] <= 0;         sflit_id[0] <= 0;         lreq <= 1;         nreq <= 1;         wreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[0] <= 1;         lreq <= 1;         nreq <= 1;         wreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         nreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[2] <= 1;         lreq <= 0;         nreq <= 1;         ereq <= 1;         sreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         lflit_id[2] <= 0;         nflit_id[2] <= 0;         eflit_id[2] <= 0;         wflit_id[2] <= 0;         sflit_id[2] <= 0;         lreq <= 0;         nreq <= 1;         ereq <= 1;         wreq <= 1;         sreq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         ereq <= 0; 
        #(10)

        rst <= 1;
        #(20)        
        reset();
        rst <= 0;         wreq <= 0; 
        #(10)

        #(clk_period * 2); 
        $stop;
    end

// Properties

property property_2; 
@(posedge clk) 
    (!rst && lflit_id[2] && lreq && !nreq && !ereq && !wreq && !sreq) |-> !nextstate[0]; 
endproperty

property property_3; 
@(posedge clk) 
    (!rst && lflit_id[2] && sreq) |-> !nextstate[0]; 
endproperty

property property_4; 
@(posedge clk) 
    (!rst && !lflit_id[2] && !lflit_id[1] && !nflit_id[2] && !eflit_id[2] && !wflit_id[2] && !sflit_id[2] && sreq) |-> !nextstate[0]; 
endproperty

property property_5; 
@(posedge clk) 
    (!rst && lflit_id[0] && !lreq && !nreq && ereq && !sreq) |-> !nextstate[0]; 
endproperty

property property_6; 
@(posedge clk) 
    (!rst && lflit_id[0] && !lreq && !nreq && !ereq && wreq && !sreq) |-> !nextstate[0]; 
endproperty

property property_7; 
@(posedge clk) 
    (!rst && lflit_id[0] && nreq && !sreq) |-> !nextstate[0]; 
endproperty

property property_8; 
@(posedge clk) 
    (!rst && !lflit_id[0] && !nflit_id[0] && !eflit_id[0] && !wflit_id[0] && !sflit_id[0] && lreq && nreq && !wreq && !sreq) |-> !nextstate[0]; 
endproperty

property property_9; 
@(posedge clk) 
    (!rst && !lflit_id[0] && !nflit_id[0] && !eflit_id[0] && !wflit_id[0] && !sflit_id[0] && !lreq && nreq && ereq && !wreq && !sreq) |-> !nextstate[0]; 
endproperty

property property_10; 
@(posedge clk) 
    (!rst && !lflit_id[0] && !nflit_id[0] && !eflit_id[0] && !wflit_id[0] && !sflit_id[0] && !lreq && !nreq && ereq && wreq && !sreq) |-> !nextstate[0]; 
endproperty

property property_11; 
@(posedge clk) 
    (!rst && !lflit_id[0] && !nflit_id[0] && !eflit_id[0] && !wflit_id[0] && !sflit_id[0] && nreq && wreq && !sreq) |-> !nextstate[0]; 
endproperty

property property_12; 
@(posedge clk) 
    (!rst && !lreq) |-> !nextstate[1]; 
endproperty

property property_16; 
@(posedge clk) 
    (!rst && lflit_id[2] && !lflit_id[0] && !nflit_id[0] && !eflit_id[0] && !wflit_id[0] && !sflit_id[0] && lreq && nreq && !wreq) |-> !nextstate[2]; 
endproperty

property property_17; 
@(posedge clk) 
    (!rst && lflit_id[0] && lreq && nreq && !wreq) |-> !nextstate[2]; 
endproperty

property property_18; 
@(posedge clk) 
    (!rst && !nreq) |-> !nextstate[2]; 
endproperty

property property_21; 
@(posedge clk) 
    (!rst && lflit_id[2] && !lreq && nreq && ereq && !sreq) |-> !nextstate[3]; 
endproperty

property property_22; 
@(posedge clk) 
    (!rst && !lflit_id[2] && !nflit_id[2] && !eflit_id[2] && !wflit_id[2] && !sflit_id[2] && !lreq && nreq && ereq && wreq && !sreq) |-> !nextstate[3]; 
endproperty

property property_23; 
@(posedge clk) 
    (!rst && !ereq) |-> !nextstate[3]; 
endproperty

property property_25; 
@(posedge clk) 
    (!rst && !wreq) |-> !nextstate[4]; 
endproperty

// Assertions

property_2_assert : assert property (property_2) else $error("property_2 not held!");
property_3_assert : assert property (property_3) else $error("property_3 not held!");
property_4_assert : assert property (property_4) else $error("property_4 not held!");
property_5_assert : assert property (property_5) else $error("property_5 not held!");
property_6_assert : assert property (property_6) else $error("property_6 not held!");
property_7_assert : assert property (property_7) else $error("property_7 not held!");
property_8_assert : assert property (property_8) else $error("property_8 not held!");
property_9_assert : assert property (property_9) else $error("property_9 not held!");
property_10_assert : assert property (property_10) else $error("property_10 not held!");
property_11_assert : assert property (property_11) else $error("property_11 not held!");
property_12_assert : assert property (property_12) else $error("property_12 not held!");
property_16_assert : assert property (property_16) else $error("property_16 not held!");
property_17_assert : assert property (property_17) else $error("property_17 not held!");
property_18_assert : assert property (property_18) else $error("property_18 not held!");
property_21_assert : assert property (property_21) else $error("property_21 not held!");
property_22_assert : assert property (property_22) else $error("property_22 not held!");
property_23_assert : assert property (property_23) else $error("property_23 not held!");
property_25_assert : assert property (property_25) else $error("property_25 not held!");

endmodule // arbiter_tb
