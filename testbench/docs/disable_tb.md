# Description
This testbench introduces the mechanism of disabling an assertion
based on logical conditions.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)

# Overview
Sometimes it is desirable to turn of assertions under certain conditions.
One such common example is reset conditions. While reset may not apply
to formal verification scenario in many cases, assertions added to the
design are present during verification too. So there is a need to write
assertions in DV friendly manner.

There are many other use cases of disable.

```sv
module disable_tb();

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

  req4_stable_till_gnt: assume property (
    @(posedge clock) disable iff (reset)
        request[4] && !grant[4] |-> ##1 request[4]
  );

  sequence gnt_in_31_cycles_S1;
    ##[0:31] grant[4];
  endsequence;

  property gnt4_in_31_cycles_P1;
    request[4] |-> gnt_in_31_cycles_S1;
  endproperty;

  gnt4_in_31_cycles_AT1: assert property (
    @(posedge clock) disable iff (reset) (gnt4_in_31_cycles_P1)
  );

endmodule
```
