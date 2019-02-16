# Description
This testbench shows how to bind modules.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)

# Overview
In many instances it is desirable to write assertions and assumprions in a
separate file. One way is to create a module that houses all these and then
bind this module to the design file.

# Binding module
A binding module is a regular module that has signals required for properties
as inputs.

```sv

```
## Create a bind module
```sv
module rr_arbiter_props(
  input last_selected,
  input stall,
  input clock
  );

  stall_check: assert property (
    @(posedge clock) ( stall |-> ##1 $stable(last_selected))
  );

endmodule
```
```sv
module bind_tb();

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

```
## Binding a module by module name
```sv
  bind rr_arbiter rr_arbiter_props u0_rr_arbiter_props(
                  .last_selected (last_selected),
                  .stall         (stall),
                  .clock         (clock));

```
## Binding a module by instance
```sv
  bind bind_tb.dut rr_arbiter_props u1_rr_arbiter_props(
                  .last_selected (last_selected),
                  .stall         (stall),
                  .clock         (clock));

endmodule
```
# A note on binding property modules
There are valid usecases of binding a module and this language feature is
quite useful. Having said that, one of the reasons of binding a module often
quoted is that this allows the verification engineers to independently add
assertions in the design files.

It can be argued that behaviour that can be obsersed from outside of the
module can be placed in the interface or a bind module that is instantiated
along with the design through module bindings. This way the binding module
is at the same level of hierarchy as the module being checked.

For properties that are specific to the intenal workings of a design
the design is the best person to write the properties so these should
remain inside the design. That preserves the context of the signals too.
In the example above, last_selected signal looks out of context.

