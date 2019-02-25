/*md
# Description
This testbench explains local variable.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)
*/

//sv+
module local_variables_tb();

  logic clock;
  logic reset;

  parameter CLIENTS = 32;
  parameter CLIENTS_W = $clog2(CLIENTS);

  logic [CLIENTS-1:0] request;
  logic [CLIENTS-1:0] grant;

  rr_arbiter #(.CLIENTS(32)) dut (
                  .request (request),
                  .grant   (grant),
                  .stall   (stall),
                  .clock   (clock),
                  .reset   (reset));

  logic cycle_after_reset;
  always @(posedge clock) begin
    if (reset)
      cycle_after_reset <= 1'b1;
    else
      cycle_after_reset <= 1'b0;
  end

  req_stable_AS1: assume property (
    @(posedge clock) disable iff (cycle_after_reset) (
      &((~($past(request) & (~$past(grant)))) | request)
    )
  );

/*md
# Overview
Local variables are defined within a sequence. These are very helpful in writing
certain kinds of sequences. Their scope is restricted to the sequence they are
defined in.
Note that local variables are per thread variable. Each instance of the parent
sequence will have its own copy of local variable.
Local variables can be only used in expressions of the sequence and not in
delay or repetion operators.
*/

  property last_selected_static_on_stall_P;
    logic [CLIENTS_W-1:0] last_selected;
     ($rose(stall), last_selected = dut.last_selected)##1(stall)[*50] |->
     dut.last_selected  == last_selected;
  endproperty

  last_selected_static_on_stall_AT: assert property (
     @(posedge clock) (last_selected_static_on_stall_P)
  );

endmodule
//sv-
