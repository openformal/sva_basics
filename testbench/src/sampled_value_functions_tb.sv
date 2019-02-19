/*md
# Description
This testbench introduces sampled value functions.
These are descried in 2012 System Verilog LRM in section 16.9.3 on page 360.

endpackage

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)

*/

//sv+
module sampled_value_functions_tb();

  logic clock;
  logic reset;

  parameter CLIENTS = 32;

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

/*md
## $rose(expression [,[clocking_event]])
$rose returns true if the LSB of the expression changed to 1.
Otherwise, it returns false.
*/
  sequence gnt4_in_31_cycles_S1;
    $rose(request[4]) ##[0:31] grant[4];
  endsequence;

  gnt4_in_31_cycles_C1: cover property (
    @(posedge clock) (gnt4_in_31_cycles_S1)
  );

/*md
## $fell(expression [,[clocking_event]])
$fell returns true if the LSB of the expression changed to 0.
Otherwise, it returns false.
*/
  property req4_wait_for_grant_P;
    request[4] && !grant[4] |-> !$fell(request[4]);
  endproperty;

  gnt4_in_31_cycles_AS1: assume property (
    @(posedge clock) (req4_wait_for_grant_P)
  );

/*md
## $stable(expression [,[clocking_event]])
$stable returns true if the value of the expression did not change.
Otherwise, it returns false.
*/
  req4_stable_on_stall_AT1: assert property (
    @(posedge clock) disable iff (cycle_after_reset) (
      stall && request[4] |-> ##1 $stable(request[4])
    )
  );

/*md
## $changed(expression [,[clocking_event]])
$changed returns true if the value of the expression changed.
Otherwise, it returns false.
This function was introduced in 2012 version of System Verilog.
*/
  req4_stable_on_stall_AT2: assert property (
    @(posedge clock) disable iff (cycle_after_reset) (
      stall && request[4] |-> ##1 !$changed(request[4])
    )
  );

/*md
## $past(expression1 [,[number_of_ticks] [,[expression2] [,[clocking_event]]]])

Past sampled values can be accessed with the $past function.
The following three optional arguments are provided:
— expression2 is used as a gating expression for the clocking event.
— number_of_ticks specifies the number of clock ticks in the past.
— clocking_event specifies the clocking event for sampling expression1.

expression1 and expression2 may be any expression allowed in assertions.
If expression2 is not specified, then it defaults to 1'b1.

In the assumption below we use $past to express that request for any bit does
not get deasserted till grant is received.
Note: This is a succint but convoluted expression. A generate on assumtion on
individual bits is easier to understand.
*/
  req_stable_on_stall_AS1: assume property (
    @(posedge clock) disable iff (cycle_after_reset) (
      &((~($past(request) & (~$past(grant)))) | request)
    )
  );

endmodule
//sv-
