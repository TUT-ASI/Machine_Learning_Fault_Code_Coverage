/********************
* Filename:     state_defines.v
* Description:  definitions of the possibile values for the arbiter state variable
                one-hot encoding considered
* $Revision: 21 $
* $Id: state_defines.v 21 2015-11-21 10:54:06Z ranga $
* $Date: 2015-11-21 12:54:06 +0200 (Sat, 21 Nov 2015) $
* $Author: ranga $
*********************/

`define IDLE    6'b000001
`define GRANT_L 6'b000010
`define GRANT_N 6'b000100
`define GRANT_E 6'b001000
`define GRANT_W 6'b010000
`define GRANT_S 6'b100000

`define L_PORT 5'b00001
`define N_PORT 5'b00010
`define E_PORT 5'b00100
`define W_PORT 5'b01000
`define S_PORT 5'b10000