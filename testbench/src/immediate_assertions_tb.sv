/*md
# Description
This testbench shows how to code an immediate assertion.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)

*/

//sv+
module immediate_assertions_tb();

  logic clock;
  logic reset;

  parameter CLIENTS = 32;

  logic [CLIENTS-1:0] request;
  logic [CLIENTS-1:0] grant;

  wire stall = 1'b0;

  rr_arbiter #(.CLIENTS(32)) dut (
                  .request (request),
                  .grant   (grant),
                  .stall   (stall),
                  .clock   (clock),
                  .reset   (reset));

/*md
# Overview
While concurrent assertions are much more commonly used in
formal verification immediate assertions can be used as well.
*/

  logic state;
  parameter IDLE_S = 1'b0, WAIT_S = 1'b1;
  always @(posedge clock) begin
    if (reset) begin
      state <= IDLE_S;
    end
    else begin
      case (state)
        IDLE_S: begin
          if (request[4] && !grant[4])
            state <= WAIT_S;
        end
        default: begin
          //-------------------------
          //  Immediate assumption
          //-------------------------
          assume property (request[4])
          if (grant[4])
            state <= IDLE_S;
        end
      endcase
    end
  end


  property gnt4_in_31_cycles_P1(req, gnt);
    req |-> ##[0:31] gnt;
  endproperty;

  gnt4_in_31_cycles_AT1: assert property (
    @(posedge clock) (gnt4_in_31_cycles_P1(request[4], grant[4]))
  );

endmodule
//sv-
