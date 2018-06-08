/********************
* Filename:     tb_userinterface.v
* Description:  Test bench of Arbiter decides which of the Input port buffer gets the highest priority among the others. Arbitration is based on Round-Robin Scheduling policy with the last served as least priority. Priority direction Local, North, East, South, West
*
* $Revision: 26 $
* $Id: tb_userinterface.v 26 2015-11-22 19:24:28Z ranga $
* $Date: 2015-11-22 21:24:28 +0200 (Sun, 22 Nov 2015) $
* $Author: ranga $
*********************/
`timescale 1ns/1ps

module tb_userinterface();

  // Declaring the port variables for DUT
  reg bfm_clk;
  reg [5:0] bfm_command;
  
  wire bfm_grant;
  
  // BFM commands Declaration
  parameter NOREQ1 = 6'd1,
            REQFL  = 6'd2,
            REQFN  = 6'd3,
            REQFE  = 6'd4,
            REQFW  = 6'd5,
            REQFS  = 6'd6,
            NOREQ2 = 6'd7,
            REQFLN = 6'd8,
            REQFLE = 6'd9,
            REQFLW = 6'd10,
            REQFLS = 6'd11,
            REQFLL = 6'd12,
            REQFNE = 6'd13,
            REQFNW = 6'd14,
            REQFNS = 6'd15,
            REQFNL = 6'd16,
            REQFNN = 6'd17,
            REQFEW = 6'd18,
            REQFES = 6'd19,
            REQFEL = 6'd20,
            REQFEN = 6'd21,
            REQFEE = 6'd22,
            REQFWS = 6'd23,
            REQFWL = 6'd24,
            REQFWN = 6'd25,
            REQFWE = 6'd26,
            REQFWW = 6'd27,
            REQFSL = 6'd28,
            REQFSN = 6'd29,
            REQFSE = 6'd30,
            REQFSW = 6'd31,
            REQFSS = 6'd32, 
            REQFNE_L = 6'd33, 
            REQFNW_L = 6'd34, 
            REQFNS_L = 6'd35, 
            REQFEW_L = 6'd36, 
            REQFES_L = 6'd37, 
            REQFWS_L = 6'd38,   
            REQFLE_N = 6'd39,
            REQFLW_N = 6'd40,
            REQFLS_N = 6'd41,
            REQFEW_N = 6'd42,
            REQFES_N = 6'd43,
            REQFWS_N = 6'd44,
            REQFLN_E = 6'd45,
            REQFLW_E = 6'd46,
            REQFLS_E = 6'd47,
            REQFNW_E = 6'd48,
            REQFNS_E = 6'd49,
            REQFWS_E = 6'd50,
            REQFLN_W = 6'd51,
            REQFLE_W = 6'd52,
            REQFLS_W = 6'd53,
            REQFNE_W = 6'd54,
            REQFNS_W = 6'd55,
            REQFES_W = 6'd56,
            REQFLN_S = 6'd57, 
            REQFLE_S = 6'd58, 
            REQFLW_S = 6'd59, 
            REQFNE_S = 6'd60, 
            REQFNW_S = 6'd61, 
            REQFEW_S = 6'd62;  

  // Instantiate BFM
  bfm_arbiter BFM (bfm_clk, bfm_command, bfm_grant);
  
  // Specify the CYCLE parameter
  parameter CYCLE = 10;
  
  // Generating Clock of period 10ns
  initial begin
    bfm_clk = 0;
    forever
      #(CYCLE/2) bfm_clk = ~bfm_clk;
  end
  
  // Applying Commands
  initial begin : SIM
    BFM.reset;
    
    bfm_command = NOREQ1;
    @(posedge bfm_grant);

    bfm_command = REQFL;
    @(posedge bfm_grant);

    bfm_command = REQFN;
    @(posedge bfm_grant);

    bfm_command = REQFE;
    @(posedge bfm_grant);

    bfm_command = REQFW;
    @(posedge bfm_grant);

    bfm_command = REQFS;
    @(posedge bfm_grant);

    bfm_command = NOREQ2;
    @(posedge bfm_grant);

    bfm_command = REQFLN;
    @(posedge bfm_grant);

    bfm_command = REQFNE;
    @(posedge bfm_grant);

    bfm_command = REQFEW;
    @(posedge bfm_grant);

    bfm_command = REQFWS;
    @(posedge bfm_grant);

    bfm_command = REQFSL;
    @(posedge bfm_grant);

    bfm_command = REQFLL;
    @(posedge bfm_grant);

    bfm_command = REQFLE;
    @(posedge bfm_grant);

    bfm_command = REQFES;
    @(posedge bfm_grant);

    bfm_command = REQFSN;
    @(posedge bfm_grant);

    bfm_command = REQFNN;
    @(posedge bfm_grant);

    bfm_command = REQFNW;
    @(posedge bfm_grant);

    bfm_command = REQFWL;
    @(posedge bfm_grant);

    bfm_command = REQFLW;
    @(posedge bfm_grant);

    bfm_command = REQFWE;
    @(posedge bfm_grant);

    bfm_command = REQFEE;
    @(posedge bfm_grant);

    bfm_command = REQFEN;
    @(posedge bfm_grant);

    bfm_command = REQFNL;
    @(posedge bfm_grant);

    bfm_command = REQFLS;
    @(posedge bfm_grant);

    bfm_command = REQFSS;
    @(posedge bfm_grant);

    bfm_command = REQFSW;
    @(posedge bfm_grant);

    bfm_command = REQFWW;
    @(posedge bfm_grant);

    bfm_command = REQFWN;
    @(posedge bfm_grant);

    bfm_command = REQFNS;
    @(posedge bfm_grant);

    bfm_command = REQFSE;
    @(posedge bfm_grant);

    bfm_command = REQFEL;
    @(posedge bfm_grant);

    bfm_command = NOREQ2;
    @(posedge bfm_grant);

    // // Two requests at the same time
    // //BFM.reset;

    // bfm_command = REQFNE_L;
    // @(posedge bfm_grant);

    // bfm_command = REQFNW_L;
    // @(posedge bfm_grant);

    // bfm_command = REQFNS_L;
    // @(posedge bfm_grant);

    // bfm_command = REQFEW_L;
    // @(posedge bfm_grant);

    // bfm_command = REQFES_L;
    // @(posedge bfm_grant);

    // bfm_command = REQFWS_L;
    // @(posedge bfm_grant);

    //For toggle coverage of reset
    BFM.reset;

    $display("\n ****** Simulation Complete ********** \n");
    #(CYCLE * 2); 
    $stop;
  
  end
  
endmodule

