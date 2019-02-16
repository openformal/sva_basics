# Description
This testbench introduces clocking of sequences, porperties, assertions,
and assumptions.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)

In this testbench stall is disabled# Overview
Concurrent SVAs need to have a clock. This testbench covers the single clock
scenario. The clock can be specified in the assertion, property or sequence.

## Clocking in assertion
## Clocking in property
This method is commonly recommended. It allows the sequences
to be reusable;
## Clocking in sequence## Clocking blocks
### Named clocking block
### Default clocking block```sv

```
## Events
Events may not be fully supported in all Formal Verification tools.

# Recommendation
Clocking methodology depends on the use case and ASIC flow.
In general, explicit clocking in properties (or assertions/assumptions/
covers where property is not present) is good for reuse and debug.
```sv
