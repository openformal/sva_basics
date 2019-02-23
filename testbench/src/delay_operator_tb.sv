/*md
# Description
This testbench explains delay operator**(##)** usage in sequences

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)

*/

//sv+
module delay_operator_tb();

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

  req_stable_AS1: assume property (
    @(posedge clock) disable iff (cycle_after_reset) (
      &((~($past(request) & (~$past(grant)))) | request)
    )
  );

/*md
# Overview
Delay operator is used to specify number of clock cycles between sequences or
parts of sequences.

## Constant delay value (##[n])
A ##[n] means there is delay of n cycles between the preceding sequence
and the subsquent sequence.

Note: ##0 is legal
*/
  req4_req5_gnt4_d3_gnt5: cover property (
     @(posedge clock) request[4] ##1 request[5] ##1 grant[4] ##3 grant[5]
  );

/*md
## Delay range (##[m:n])
A ##[m:n] means there is delay of m to n cycles between the preceding sequence
and the subsquent sequence.
*/
  req4_req5_gnt4_d3_6_gnt5: cover property (
     @(posedge clock) request[4] ##1 request[5] ##1 grant[4] ##[3:6] grant[5]
  );

/*md
## Finite but unspecified delay (##[m:$])
A ##[m:$] means there is delay of m to unspecified cycles between the preceding
sequence and the subsquent sequence.

##[*] is same as ##[0:$].

##[+] is same as ##[1:$].

*/
  req4_req5_gnt4_d3_many_gnt5: cover property (
     @(posedge clock) request[4] ##1 request[5] ##1 grant[4] ##[3:$] grant[5]
  );
endmodule
//sv-

/*md
**_NOTE :
For specifying liveness properties (eventually), refer to the testbench on
liveness.
*/
