# Description
This testbench explains consecutive repitition operator**(*)** usage in sequences

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)

```sv
module cons_rep_operator_tb();

  logic clock;
  logic reset;

  parameter CLIENTS = 32;

  logic [CLIENTS-1:0] request;
  logic [CLIENTS-1:0] grant;

  wire stall = 0;

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

```
# Overview
Consecutive repetition ( [*const_or_range_expression] ): Consecutive repetition
specifies finitely many iterative matches of the operand sequence, with a delay
of one clock tick from the end of one match to the beginning of the next.
The overall repetition sequence matches at the end of the last iterative match
of the operand.

[*] is an equivalent representation of [*0:$]

[+] is an equivalent representation of [*1:$].

##
## Consecutive repetition with constraint
The example below shows the following case,
request[4] && !grant[4] ##1 !grant[4] ##1 !grant[4] ##1 !grant[4] ##1 grant[4]
```sv
  req4_req5_gnt4_d3_gnt5_C: cover property (
     @(posedge clock) request[4] ##0 (!grant[4])[*3] ##1 grant[4]
  );

```

/*md
## Consecutive repetition with range
The example below allows the following cases,
request[4] && !grant[4] ##1 !grant[4] ##1 grant[4]
request[4] && !grant[4] ##1 !grant[4] ##1 !grant[4] ##1 grant[4]
request[4] && !grant[4] ##1 !grant[4] ##1 !grant[4] ##1 !grant[4] ##1 grant[4]
```sv
  req4_req5_gnt4_d1_3_gnt5_C: cover property (
     @(posedge clock) request[4] ##0 (!grant[4])[*1:3] ##1 grant[4]
  );

```
## More examples of consecutive repetition

In this testbench the stall signal is tied to 0. So when a request bit
is asserted, corresponding grant will be asserted within 31 clock cycles.
Assume the precondition, request[4] asserted, happens on cycle 1. The latest
grant[4] can be asserted is cycle 32.

```sv

/*
Assertion below will pass because all traces will satisfy the sequence.
A trace with grant[4] deasserted till cycle 31 cycle is *not* a counterexample.
Such a trace will satisfy the assertion as it will end at cycle 30 as it is
the last iterative match.
*/
  req4_and_not_gnt4_for_upto_cycle30_AT: assert property (
     @(posedge clock) request[4] &&!grant[4] |-> ##1 (!grant[4])[*0:29]
  );

```
The assertion below is an extension of the one above by adding grant[4]
at the end. Now the sequences can only terminate when grant[4] is met.
There exists a scenario, !grant[31] ##1 grant[4] which is legal. That
scenario is counterexample to the assertion below. Hence, this assertion
will fail
```sv
  req4_and_not_gnt4_within_30_AT_FAIL: assert property (
     @(posedge clock) request[4] && !grant[4] |-> ##1 (!grant[4])[*0:29] ##1 grant[4]
  );

```
Assertions below will pass because all traces will satisfy the sequence.
```sv
  req4_and_not_gnt4_for_upto_31_AT: assert property (
     @(posedge clock) request[4] && !grant[4] |-> ##1 (!grant[4])[*0:30]
  );

  req4_and_not_gnt4_within_31_AT: assert property (
     @(posedge clock) request[4] && !grant[4] |-> ##1 (!grant[4])[*0:31] ##1 grant[4]
  );

```
Assertions below will pass because all traces will satisfy the sequence.
This is true even if there is no trace that can have 32 !grant[4]'s.
```sv
  req4_and_not_gnt4_for_upto_32_AT: assert property (
     @(posedge clock) request[4] && !grant[4] |-> ##1 (!grant[4])[*0:31]
  );

  req4_and_not_gnt4_within_32_AT: assert property (
     @(posedge clock) request[4] && !grant[4] |-> ##1 (!grant[4])[*0:31] ##1 grant[4]
  );

```
If the objective is to make sure there can not be 32 !grant[4]'s, the property
below will work.
```sv
  req4_and_not_gnt4_for_31_AT: assert property (
     @(posedge clock) request[4] |-> not ((!grant[4])[*32])
  );

```
# Scenarios vs rules
Traditional simulation based verification is built around generating scenarios.
Engineers trained in such an approach often gravitate towards the following
approach.

1. Identify a precondition/antecedant
2. Generate legal output sequence that captures all possibilities of legal outputs
3. Code the assertion: precondition -> sequences

The second step, making a sequence that covers all legal outputs, may not
be easy. It may also involve indeterminate delays ##[0:$] in assumptions
when there are multiple dependant interfaces.

A better approach is to think in terms of guarantees and rules. The example
below shows the subtle difference between the two approaches.

For the examples above, the first approach requires legal sequence space.
request[4] and grant[4] in the same cycle
request[4] and grant[4] in 1 cycle
...
request[4] and grant[4] in 32 cycles
It is captured as
(!grant[4])[*0:31] ##1 grant[4]
The assertion will be,
```sv
  gnt4_within_32_AT1: assert property (
    request[4] |-> (!grant[4])[*0:31] ##1 grant[4]
  );

/*
The second approach approaches this as a gurantee that grant is provided
within 32 cycles. An assertion for that will look like,
*/
  gnt4_within_32_AT2: assert property (
    request[4] |-> ##[0:31] grant[4]
  );
endmodule
```
