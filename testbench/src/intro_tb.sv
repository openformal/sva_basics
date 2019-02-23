/*md
# Description
This testbench introduces sequences, properties, assertions, and assumptions.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)

*/

//sv+
module intro_tb();

  logic clock;
  logic reset;

  parameter CLIENTS = 32;

  logic [CLIENTS-1:0] request;
  logic [CLIENTS-1:0] grant;

//md In this testbench stall is disabled
  wire stall = 1'b0;

  rr_arbiter #(.CLIENTS(32)) dut (
                  .request (request),
                  .grant   (grant),
                  .stall   (stall),
                  .clock   (clock),
                  .reset   (reset));

/*md
# Rule (gnt_in_31_cycles)
If the stall is never asserted, a grant should be asserted for a
for a request within 31 (=CLIENTS-1) cycles.

Let us concentrate on one requestor for this testbench, requestor 4.

## Sequence
A sequence is a series of boolean conditions or sequences. A sequence
can spans one to multiple clocks.
This sequence describes an grant[4] being set in 0 to 31 clocks.
*/

 sequence gnt4_in_31_cycles_S;
   ##[0:31] grant[4];
 endsequence;

/*md
## Property
A property can be viewed as a rule. It can have expressions and sequences.
Properties can use implication operators (|->, |=>).
antecedant(precondition) |-> consequent
*/
  property gnt4_in_31_cycles_P0;
    request[4] |-> gnt4_in_31_cycles_S;
  endproperty;

//md An equivalent way of writing this would begin

  property gnt4_in_31_cycles_P1;
    request[4] |-> ##[0:31] grant[4];
  endproperty;

/*md
## Assertion
Assertion is a check. The form below is concurrent assertion which
is checked to be always true.
Assertions can have expressions, sequences and properties.
*/
  gnt4_in_31_cycles_AT: assert property (
    @(posedge clock) (gnt4_in_31_cycles_P0)
  );

/*md
## Assumption
Assumption is a constraint on the formal verification tool.
It defines a rule that the tool must follow while proving
an assertion or generating a cover property for a cover

In this case the design requires that request be kept
asserted while the grant is not received.
Since there are multiple requestors we will use a generate
to make properties.
*/
  generate
    for (genvar i=0; i<CLIENTS; i++) begin
      hold_request_till_grant: assume property (
        @(posedge clock) (
          request[i] && !grant[i] |-> ##1 request[i]
        )
      );
    end
  endgenerate

/*md
## Cover
Cover is a instruction to the tool to create a scenario
where the property is true.

The cover below defines a condition where a response
for a request is received after 31 clock cycles.

The sequence below shows clocking within the sequence.
*/
  sequence gnt5_received_in_31_cycles_S;
    @(posedge clock) !request[5] ##1 request[5] ##0 (!grant[5])[*31] ##1 grant[5];
  endsequence;

  gnt5_received_in_31_cycles_C: cover property (gnt5_received_in_31_cycles_S);

/*md
The following cover property is not possible and will fail.
A failure of a cover property indicates that there is no
trace that satisfies the sequence that property is trying to
cover.
Also note that this is closely related to the assertion (gnt4_in_31_cycles_AT)
coded earlier in this testbench. If assert(prop) holds true, then cover
(not prop) will hold false. In this case, since we have proven an aseertion
stating a grant comes in 0 to 31 cycle, a cover of grant coming in 32 cycles
will be false.
*/

  sequence gnt5_received_in_32_cycles_Fail_S;
    @(posedge clock) !request[5] ##1 request[5] ##0 (!grant[5])[*32] ##1 grant[5];
  endsequence;

  gnt5_received_in_32_cycles_Fail_C: cover property (gnt5_received_in_32_cycles_Fail_S);

endmodule
//sv-
