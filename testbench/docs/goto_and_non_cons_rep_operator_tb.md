# Description
This testbench explains non consecutive repitition operator**(*)** and
goto repetion operator.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)

```sv
module goto_and_non_cons_rep_operator_tb();

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

**Goto repetition ( [->const_or_range_expression] ):**
Goto repetition specifies finitely many iterative matches of the
operand Boolean expression, with a delay of one or more clock ticks from one
match of the operand to the next successive match and no match of the operand
strictly in between. The overall repetition sequence matches at the last
iterative match of the operand.

**Nonconsecutive repetition ( [=const_or_range_expression] ):**
Nonconsecutive repetition specifies finitely many iterative matches of the
operand Boolean expression, with a delay of one or more clock ticks from one
match of the operand to the next successive match and no match of the operand
strictly in between. The overall repetition sequence matches at or after the
last iterative match of the operand, but before any later match of the operand.

Notice the definition of the operators are identical except on how the
match is detected in the end.

##
## Goto and non consecutive repetition with constant
The sequence below describes a single request-grant operation on client 4
followed by grant to client 5.

A cover for the first one can have a delay of between 3rd grant[4] and
grant[5] when using = operator. There will be no grant[4] during this delay.
In case of -> operator the grant[5] will need to be asserted the clock
cycle afted 3rd grant[4].
```sv

  client4_4_transactions_C: cover property (
     @(posedge clock) (request[4] && grant[4])[=3] ##1 grant[5]
  );

  client4_4_transactions_C: cover property (
     @(posedge clock) (request[4] && grant[4])[->3] ##1 grant[5]
  );

```
## Gotot / non consecutive repetition with range
The example below allows the following cases,
```sv
  client4_2_to_4_transactions_C: cover property (
     @(posedge clock) (request[4] && grant[4])[=2:4]
  );

  client4_2_to_4_transactions_C: cover property (
     @(posedge clock) (request[4] && grant[4])[->2:4]
  );

```
## Matching of goto and non consecutive repetition sequences
Consider the following property. This looks correct but it will fail.
In this case the fisrt part - (request[4] && grant[4])[=1] is true 2 cycle
after the request[4] && grant[4] provided a new request[4] && grant[4] does not
happen in that cycle. So this will allow the following sequence as a positive
match of the precondition,
|Signal     | Cycle 1 | Cycle 2 | Cycle 3 |
|:---------:|:-------:|:-------:|:-------:|
|reuest[4]  | 1       |0        |0        |
|grant[4]   | 1       |0        |0        |
|request[5] | 1       |1        |1        |
|grant[5]   | 1       |1        |0        |
In this case the if there is another requestor, say request[6], grant[5] wiil
not be asserted in 3rd cycle. That will make the assertion fail.
Use of goto operator "->" will fix this. The only difference between = and ->
is that -> will be true only the very cycle the match happens, which is cycle
2 in this case.
```sv
  request5_after_request4_AT_FAIL: assert property (
     @(posedge clock) (request[4] && grant[4])[=1] ##1 request[5] |-> grant[5]
  );

  request5_after_request4_AT1: assert property (
     @(posedge clock) (request[4] && grant[4])[->1] ##1 request[5] |-> grant[5]
  );
endmodule
```
