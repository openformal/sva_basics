# Description
This testbench explains the system functions.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)
```sv
module system_functions_tb();

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

```
# Overview
System functions facilitate describing certain frequently seen behaviour in
designs succinctly.

## $onehot
$onehot(expression) is true only when one and only one bit is set in the
expression.
```sv
  req_and_no_stall_implies_grant_AT: assert property (
     @(posedge clock) (|request) && !stall |-> $onehot(grant)
  );

/*
## $onehot0
$onehot0(expression) is true only when single bit is set or no bits are set in
the expression.
*/
  grant_onehot0_AT: assert property (
     @(posedge clock) $onehot0(grant)
  );

```
## $countones
$countones(expression) returns nuber of bits set in the expression.
```sv
  grant_none_or_one_AT: assert property (
     @(posedge clock) $countones(grant) <= 1
  );
endmodule
```
