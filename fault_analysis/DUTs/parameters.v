/********************
* Filename:    parameters.v
* Description: Parameters for Packet FLITS
* $Revision: 21 $
* $Id: parameters.v 21 2015-11-21 10:54:06Z ranga $
* $Date: 2015-11-21 12:54:06 +0200 (Sat, 21 Nov 2015) $
* $Author: ranga $
*********************/

  // defining the flit ID -- One hot encoding
  `define HEADER  3'b001
  `define PAYLOAD 3'b010
  `define TAIL    3'b100

  // Specifying the FIFO parameters
  `define FIFO_DEPTH 'd4               // 4 flits capacity
  `define PTR_SIZE   `FIFO_DEPTH       // Controls reading and writing (for full and empty) >> Depends on the FIFO_DEPTH
  `define DATA_WIDTH 'd32              // # of data bits with parity