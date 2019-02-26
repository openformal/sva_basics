# Description
This testbench explains sequence operators.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)
```sv
module sequence_operators_tb();

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
Sequence operators work on sequences and are helpful in generating
sequences using existing sequences.

## within operator
usage: "sequence 1" within "sequence 2"

The above sequence has a match when sequence 2 has a match and there exists
at least one match of sequence 1 between the start of the match clock tick
and end of the match clock tick for sequence 2. The start end of the match
are same as seuence 2.
```sv

  sequence grant_1_5_S;
    grant[1] ##20 grant[5];
  endsequence

  sequence grant_2_6_S;
    grant[2] ##2 grant[6];
  endsequence

  grant_1_2_6_5_C: cover property (
    @(posedge clock) grant_2_6_S within grant_1_5_S
  );

```
## and operator
usage: "sequence 1" and "sequence 2"

The above sequence has a match when both sequence 1 and 2 have a match and these
matches start on the same clock cycle. The start of the match is this clock
cycle and the end of the match is the later of the end of the match of
sequence 1 and 2.
```sv

  sequence grant_1_6_S;
    grant[1] ##2 grant[6];
  endsequence

  grant_1_6_5_C: cover property (
    @(posedge clock) grant_1_5_S and grant_1_6_S
  );

```
## or operator
usage: "sequence 1" or "sequence 2"

The above sequence has a match when either sequence 1 or 2 have a match.
The start and end of the match is same as the matching sequence. If both
sequences match the end of the match is the earlier of the end of the matches.
```sv

  grant_1_6or5_C: cover property (
    @(posedge clock) grant_1_5_S or grant_1_6_S
  );

  /*
## intersect operator
usage: "sequence 1" intersect "sequence 2"

The above sequence has a match when both sequence 1 or 2 have a match and the
start and end of the matches for both sequences are identical.

In the example below the set of sequences that will satisfy the cover will
have to be 21 clock cycles long as one of the sequences, grant_1_5_S is
21 cycles long.
*/

  sequence grant_1_4_5_S;
    grant[1] ##10 grant[4] ##[0:20] grant[5];
  endsequence

  grant_1_4_5_C: cover property (
    @(posedge clock) grant_1_5_S intersect grant_1_4_5_S
  );

```
## not operator
usage: not "sequence 1"

The above sequence is true on a clock cycle when there is no match of the
sequence 1 that starts on the clock cycle.
```sv

  grant_2_skipped_AT: assert property (
    @(posedge clock) not ((!stall && !grant[2] && request[2]) throughout
      (grant[1] ##4 grant[5]))
  );

```
## first_match operator
usage: first_match("sequence 1")

firstmatch operator defines the first match of the sequence 1.

The example below is just to show the syntax. This construct can be used
for cases where certain behavior only occurs once, say out of reset.
```sv

  first_match_grant_1_4_5_C: cover property (
     @(posedge clock) first_match(grant_1_4_5_S)
  );

```
## throughout operator
usage: signal throughout "sequence 1"
This sequence matches if the expression is trues throughout the match
of sequence 1. The start and end of the match is same as that of the
sequence 1.
```sv

  grant_1_4_5_no_stall_C: cover property (
     @(posedge clock) !stall throughout grant_1_4_5_S
  );
endmodule
```
