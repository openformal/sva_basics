# Description
This testbench explains the use of **if** and **case** keywords.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)
```sv
module if_and_case_tb();

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
It is sometimes useful to express exclusive related properties together
just like it is done in writing design or verifiction. For this purpose,
if and case keywords are used.

## if
The property below shows the use of if keyword.
*_(Note: This property does not capture complete requirements of stall.)_*
```sv
  req_stall_grant_AT: assert property (
     @(posedge clock) (|request) |->
       if (stall)
         grant == '0
       else
         $onehot(grant)
  );

```
## case
The property below shows how to use a case statement.
```sv

  round_robin_AT: assert property (
    @(posedge clock) disable iff (cycle_after_reset) !stall && (request == 32'hFFFF_FFFF) |->
      case ($past(grant, 1))
        32'h1: grant == 32'h2;
        32'h2: grant == 32'h4;
        32'h4: grant == 32'h8;
        default: $onehot(grant);
     endcase
  );

```
