# Description
This testbench tries to illustrate the difference between liveness and safety.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)
```sv
module safety_vs_liveness_tb();

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
Safety properties define a behaviour that must be observed over a finite
period of time.
Liveness propeties define a behaviour that must be observed without specifying
any time bound.

All violations of safety properties are bounded time violations.
Violation traces (counter-examples) of liveness properties can be of infinite
length.

In general liveness properties are harder to prove. However, they can be very
effectively used to find bugs in the designs.

# Safety vs liveness example
Both of the properties below will fail because the stall signal is left
unconstrained.
```sv


  grant_within_32_AT0_FAIL: assert property (
    @(posedge clock) request[4] |-> ##[0:31] grant[4]
  );

  grant_within_32_AT1_FAIL: assert property (
    @(posedge clock) request[4] |-> s_eventually grant[4]
  );

```
# Strong vs weak properties
Strong properties only pass when antecedent is observed. In formal verification
infine length traces are allowed as a violations trace. In simulation the
property fails if end of simulation is observed before antecedant is observed.

Weak propeties can only have finite length violations. In simulation they pass
if end of simulation occurs before the antecedant is seen.

Below is an example of a strong and week property. The weak property will pass
because there is no finite length trace that violates it. The strong one will
fail. **strong(property)** and **weak(property)** functions can be used
on a property to make it strong or weak.

property operators that start with "s_" indicate a strong property.

_Note_: In SystemVerilog 2005 specifications the fist property below was
considered a strong property. The 2009/2012 version makes it a weak property.
```sv

  grant_within_32_AT2: assert property (
    @(posedge clock) request[4] |-> ##[0:$] grant[4]
  );

  grant_within_32_AT3_FAIL: assert property (
    @(posedge clock) request[4] |-> strong(##[0:$] grant[4])
  );

endmodule
```
# Recommendation
It is better to write a safety property as it is less complex to prove. In the
case above, writing a property that states a grant comes in 32 cycles when
stall is not present is better than writing a property that states grant will
eventually come if stall is not present.

There are instances where a liveness property can cover a large range of bugs
and is very useful. Liveness properties are very useful in detecting deadlock
conditions. When writing liveness properties care must be taken to make sure
they are strong.

# Infinite traces in waveforms
Since the designs always have a finite states any infinite trace is cyclical
in nature. Formal verification tools divide infinite length violations into
the initial and cyclical parts. The cyclical part is usually colored differently
indicating that it repeats infinitely. The counterexamples of the liveness
assertions above are a good examples of infinite length trace. In this case
the cyclical part is single cycle long.
