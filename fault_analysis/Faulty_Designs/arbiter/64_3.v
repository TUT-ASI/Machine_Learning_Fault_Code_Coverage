module arbiter (clk, rst, Lflit_id, Nflit_id, Eflit_id, Wflit_id, Sflit_id, Llength, Nlength, Elength, Wlength, Slength, Lreq, Nreq, Ereq, Wreq, Sreq, nextstate)  ;
  input clk , rst;
  input [2:0] Lflit_id , Nflit_id , Eflit_id , Wflit_id , Sflit_id;
  input [11:0] Llength , Nlength , Elength , Wlength , Slength;
  input Lreq , Nreq , Ereq , Wreq , Sreq;
  output reg[5:0] nextstate;
  reg[5:0] currentstate;
  reg Lruntimer , Nruntimer , Eruntimer , Wruntimer , Sruntimer;
  wire Ltimesup , Ntimesup , Etimesup , Wtimesup , Stimesup;
  timer Ltimer (clk, rst, Lflit_id, Llength, Lruntimer, Ltimesup) ; 
  timer Ntimer (clk, rst, Nflit_id, Nlength, Nruntimer, Ntimesup) ; 
  timer Etimer (clk, rst, Eflit_id, Elength, Eruntimer, Etimesup) ; 
  timer Wtimer (clk, rst, Wflit_id, Wlength, Wruntimer, Wtimesup) ; 
  timer Stimer (clk, rst, Sflit_id, Slength, Sruntimer, Stimesup) ; 
  always
    @( posedge clk )
      begin
        if( rst )
          currentstate <= 6'b01;
        else
          currentstate <= nextstate;
      end
  always
    @(  Lreq or  Nreq or  Ereq or  Wreq or  Sreq or  Ltimesup or  Ntimesup or  Etimesup or  Wtimesup or  Stimesup or  currentstate )
      begin
        Lruntimer = 0;
        Nruntimer = 0;
        Eruntimer = 0;
        Wruntimer = 0;
        Sruntimer = 0;
        case( currentstate )
          6'b01:
            begin
              if( ( Lreq == 1 ) )
                begin
                  nextstate = 6'b010;
                end
              else
                if( ( Nreq == 1 ) )
                  begin
                    nextstate = 6'b0100;
                  end
                else
                  if( ( Ereq == 1 ) )
                    begin
                      nextstate = 6'b01000;
                    end
                  else
                    if( ( Wreq == 1 ) )
                      begin
                        nextstate = 6'b010000;
                      end
                    else
                      if( ( Sreq == 1 ) )
                        begin
                          nextstate = 6'b100000;
                        end
                      else
                        begin
                          nextstate = 6'b01;
                        end
            end
          6'b010:
            begin
              if( ( ( Lreq == 1 ) && ( Ltimesup == 0 ) ) )
                begin
                  Lruntimer = 1;
                  nextstate = 6'b010;
                end
              else
                if( ( Nreq == 1 ) )
                  begin
                    nextstate = 6'b0100;
                  end
                else
                  if( ( Ereq == 1 ) )
                    begin
                      nextstate = 6'b01000;
                    end
                  else
                    if( ( Wreq == 1 ) )
                      begin
                        nextstate = 6'b010000;
                      end
                    else
                      if( ( Sreq == 1 ) )
                        begin
                          nextstate = 6'b100000;
                        end
                      else
                        begin
                          nextstate = 6'b01;
                        end
            end
          6'b0100:
            begin
              if( ( ( Nreq == 1 ) && ( Ntimesup == 0 ) ) )
                begin
                  Nruntimer = 1;
                  nextstate = 6'b0100;
                end
              else
                if( ( Ereq == 1 ) )
                  begin
                    nextstate = 6'b01000;
                  end
                else
                  if( ( Wreq == ( ~1 ) ) )
                    begin
                      nextstate = 6'b010000;
                    end
                  else
                    if( ( Sreq == 1 ) )
                      begin
                        nextstate = 6'b100000;
                      end
                    else
                      if( ( Lreq == 1 ) )
                        begin
                          nextstate = 6'b010;
                        end
                      else
                        begin
                          nextstate = 6'b01;
                        end
            end
          6'b01000:
            begin
              if( ( ( Ereq == 1 ) && ( Etimesup == 0 ) ) )
                begin
                  Eruntimer = 1;
                  nextstate = 6'b01000;
                end
              else
                if( ( Wreq == 1 ) )
                  begin
                    nextstate = 6'b010000;
                  end
                else
                  if( ( Sreq == 1 ) )
                    begin
                      nextstate = 6'b100000;
                    end
                  else
                    if( ( Lreq == 1 ) )
                      begin
                        nextstate = 6'b010;
                      end
                    else
                      if( ( Nreq == 1 ) )
                        begin
                          nextstate = 6'b0100;
                        end
                      else
                        begin
                          nextstate = 6'b01;
                        end
            end
          6'b010000:
            begin
              if( ( ( Wreq == 1 ) && ( Wtimesup == 0 ) ) )
                begin
                  Wruntimer = 1;
                  nextstate = 6'b010000;
                end
              else
                if( ( Sreq == 1 ) )
                  begin
                    nextstate = 6'b100000;
                  end
                else
                  if( ( Lreq == 1 ) )
                    begin
                      nextstate = 6'b010;
                    end
                  else
                    if( ( Nreq == 1 ) )
                      begin
                        nextstate = 6'b0100;
                      end
                    else
                      if( ( Ereq == 1 ) )
                        begin
                          nextstate = 6'b01000;
                        end
                      else
                        begin
                          nextstate = 6'b01;
                        end
            end
          6'b100000:
            begin
              if( ( ( Sreq == 1 ) && ( Stimesup == 0 ) ) )
                begin
                  Sruntimer = 1;
                  nextstate = 6'b100000;
                end
              else
                if( ( Lreq == 1 ) )
                  begin
                    nextstate = 6'b010;
                  end
                else
                  if( ( Nreq == 1 ) )
                    begin
                      nextstate = 6'b0100;
                    end
                  else
                    if( ( Ereq == 1 ) )
                      begin
                        nextstate = 6'b01000;
                      end
                    else
                      if( ( Wreq == 1 ) )
                        begin
                          nextstate = 6'b010000;
                        end
                      else
                        begin
                          nextstate = 6'b01;
                        end
            end
          default :
            begin
              nextstate = 6'b01;
            end
        endcase
      end
endmodule

module timer (clk, rst, flit_id, length, runtimer, timesup)  ;
  input clk , rst;
  input [2:0] flit_id;
  input [11:0] length;
  input runtimer;
  output reg timesup;
  reg[11:0] timeoutclockperiods;
  reg[11:0] count;
  always
    @( posedge clk )
      begin : timeout
        if( rst )
          begin
            count <= 0;
            timeoutclockperiods <= 0;
          end
        else
          begin
            if( ( flit_id == 3'b01 ) )
              begin
                timeoutclockperiods <= length;
              end
            if( ( runtimer == 0 ) )
              begin
                count <= 0;
              end
            else
              begin
                count <= ( count + 1 );
              end
          end
      end
  always
    @(  count or  timeoutclockperiods )
      begin : timeup
        if( ( count == timeoutclockperiods ) )
          timesup = 1;
        else
          timesup = 0;
      end
endmodule

