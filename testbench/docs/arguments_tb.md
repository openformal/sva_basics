# Description
This testbench shows how to add arguments to properties to make them
reusable.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)

```sv
module arguments_tb();

  logic clock;
  logic reset;

  parameter CLIENTS = 32;

  logic [CLIENTS-1:0] request;
  logic [CLIENTS-1:0] grant;

```
In this testbench stall is disabled
```sv
  wire stall = 1'b0;

  rr_arbiter #(.CLIENTS(32)) dut (
                  .request (request),
                  .grant   (grant),
                  .stall   (stall),
                  .clock   (clock),
                  .reset   (reset));

  req4_stable_till_gnt: assume property (
    @(posedge clock) request[4] && !grant[4] |-> ##1 request[4]
  );

```
# Overview
Adding arguments to properties makes them reusable.
These arguments may or may not have type defined.
## Property with formal arguments without type
```sv
  property gnt4_in_31_cycles_P1(req, gnt);
    req |-> ##[0:31] gnt;
  endproperty;

  gnt4_in_31_cycles_AT1: assert property (
    @(posedge clock) (gnt4_in_31_cycles_P1(request[4], grant[4]))
  );

```
## Property with formal arguments with type
```sv
  property gnt4_in_31_cycles_P2(logic req, logic gnt);
    req |-> ##[0:31] gnt;
  endproperty;

  gnt4_in_31_cycles_AT2: assert property (
    @(posedge clock) (gnt4_in_31_cycles_P2(request[4], grant[4]))
  );

```
## Sequence with arguments
The example below shows explicit connection
```sv

  sequence toggle(in0);
    @(posedge clock) ##1 in0 ##1 !in0 ##1 in0;
  endsequence

  cover_gnt1_toggles: cover property (toggle(in0.(grant[1])));

endmodule
```
