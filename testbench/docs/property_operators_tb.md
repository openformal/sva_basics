# Description
This testbench explains property operators. These operators are allowed in the
properties but not in the sequences. They specify a rule rather than a
scenario. Some property operators are explained in other dedicated testbenches.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)
```sv
module property_operators_tb();

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
# Overview
Property operators are allowed in the properties but not in the sequences.
They specify a rule rather than a scenario. Some property operators are
explained in other dedicated testbenches.

## not

not is a property operator. It can be used on the sequences (but not in the
sequences).
```sv

  sequence grant_2_skipped_S;
    grant[1] && request[2] ##1 grant[3] && request[2];
  endsequence;

  grant_2_not_skipped_AT: assert property (
    @(posedge clock) not(grant_2_skipped_S)
  );

```
## always and s_always
A property is an always if it has one of the following forms that use the
always operators:

### Weak always
always property_expr

A property always property_expr evaluates to true if, and only if,
property_expr holds at every current or future clock tick.

### Ranged form of weak always
always [ cycle_delay_const_range_expression ] property_expr

A property always [cycle_delay_const_range_expression] property_expr evaluates
to true if, and only if, property_expr holds at every current or future clock
tick that is within the range of clock ticks specified by
cycle_delay_const_range_expression. It is not required that all clock ticks
within this range exist. The range for a weak always may be unbounded.

### Ranged form of strong always
s_always [ constant_range ] property_expr

A property s_always [constant_range] property_expr evaluates to true if,
and only if, all current or future clock ticks specified by constant_range
exist and property_expr holds at each of these clock ticks. The range for a
strong always shall be bounded. always can be used to specify an expression
being true for a delay range or forever.

## eventually and s_eventually
### Strong eventually
s_eventually property_expr

A property s_eventually property_expr evaluates to true if, and only if, there exists a current or
future clock tick at which property_expr evaluates to true.

### Ranged form of weak eventually
eventually [ constant_range ] property_expr

A property eventually [constant_range] property_expr evaluates to true if,
and only if, either there exists a current or future clock tick within the
range specified by constant_range at which property_expr evaluates to true
or not all the current or future clock ticks within the range specified by
constant_range exist. The range for a weak eventually shall be bounded.

### Ranged form of strong eventually
s_eventually [ cycle_delay_const_range_expression ] property_expr

A property s_eventually [cycle_delay_const_range_expression] property_expr
evaluates to true if, and only if, there exists a current or future clock
tick within the range specified by cycle_delay_const_range_expression at
which property_expr evaluates to true. The range for a strong eventually
may be unbounded.
```sv

  request_4_always_high_AS: assume property (
    @(posedge clock) request[4]
  );

  logic no_stall;
  always @(posedge clock) no_stall <= no_stall;
  no_stall_AS: assume property (
    @(posedge clock) stall == !no_stall
  );

  grant_4_every_32_AT: assert property (
    @(posedge clock) no_stall |-> always s_eventually [0:31] grant[4]
  );

```
## nexttime
### Weak nexttime
nexttime property_expr

The weak nexttime property nexttime property_expr evaluates to true if,
and only if, either the property_expr evaluates to true beginning at the next
clock tick or there is no further clock tick.

### Indexed form of weak nexttime
nexttime [ constant_expression ] property_expr

The indexed weak nexttime property nexttime [constant_expression] property_expr
evaluates to true if, and only if, either there are not constant_expression
clock ticks or property_expr evaluates to true beginning at the last of the
next constant_expression clock ticks.

### Strong nexttime
s_nexttime property_expr

The strong nexttime property s_nexttime property_expr evaluates to true if,
and only if, there exists a next clock tick and property_expr evaluates to
true beginning at that clock tick.

### Indexed form of strong nexttime
s_nexttime [ constant_expression ] property_expr
The indexed strong nexttime property s_nexttime [constant_expression]
property_expr evaluates to true if, and only if, there exist constant_expression
clock ticks and property_expr evaluates to true beginning at the last of the
next constant_expression clock ticks.

```sv

  req_3_untill_grant_3_AS: assume property (
    @(posedge clock) request[3] && !grant[3] |-> nexttime request[3]
  );

  check_assume_req_3_AT: assert property (
    @(posedge clock) not (request[3] & !grant[3] ##1 !request[3])
  );

```
## until, until_with

An until property of the non-overlapping form evaluates to true if
property_expr1 evaluates to true at every clock tick beginning with the
starting clock tick of the evaluation attempt and continuing until at least one
tick before a clock tick where property_expr2 evaluates to true. An until
property of one of the overlapping forms evaluates to true if property_expr1
evaluates to true at every clock tick beginning with the starting clock tick
of the evaluation attempt and continuing until and including a clock tick at
which property_expr2 evaluates to true. An until property of one of the strong
forms requires a current or future clock tick exist at which property_expr2
evaluates to true, while an until property of one of the weak forms does not
ake this requirement. An until property of one of the weak forms evaluates to
true if property_expr1 evaluates to true at each clock tick,
even if property_expr2 never holds.

For until property of overlapping form, with _with, property_exp1 has to be
true on the cycle property_expr2 is held true.

### Weak non-overlapping form
property_expr1 until property_expr2
### Strong non-overlapping form
property_expr1 s_until property_expr2
### Weak overlapping form
property_expr1 until_with property_expr2
### Strong overlapping form
property_expr1 s_until_with property_expr2
```sv

  req_4_untill_grant_4_AS: assume property (
    @(posedge clock) request[4] until_with grant[4]
  );

  check_assume_req_4_AT: assert property (
    @(posedge clock) not (request[4] & !grant[4] ##1 !request[4])
  );

```
## #-#, #=#
sequence_expr#-#property_expr
sequence_expr#=#property_expr

This clause is used to trigger monitoring of a property expression and is
allowed at the property level.
The result of the followed-by is either true or false. The left-hand operand
sequence_expr is called the antecedent, while the right-hand operand
property_expr is called the consequent. For the followed-by property to succeed,
the following must hold:
— From a given start point sequence_expr shall have at least one successful match.
— property_expr shall be successfully evaluated starting from the end point of
some successful match of sequence_expr.
From a given start point, evaluation of the followed-by succeeds and returns
true if, and only if, there exists a match of the antecedent sequence_expr
beginning at the start point, and the evaluation of the consequent property_expr
beginning at the end point of the match succeeds and returns true.
Two forms of followed-by are provided: overlapped using operator #-# and
nonoverlapped using operator #=#. For overlapped followed-by, there shall be a
match for the antecedent sequence_expr, where the end point of this match is
the start point of the evaluation of the consequent property_expr. For
nonoverlapped followed-by, the start point of the evaluation of the consequent
property_expr is the clock tick after the end point of the match.
```sv

  wire no_further_stalls;
  stop_stalls_AS: assume property (
    @(posedge clock) no_further_stalls #-# always !stall
  );

```
Removal of the assumption above will make the property below fail
```sv

  req_4_gets_gnt_AT: assert property (
    @(posedge clock) request[4] |-> s_eventually grant[4]
  );

endmodule
```
# Weak and strong operators
The property operators s_nexttime, s_always, s_eventually, s_until,
s_until_with, and sequence operator strong are strong: they require that some
terminating condition happen in the future, and this includes the requirement
that the property clock ticks enough time to enable the condition to happen.
The property operators nexttime, always, until, eventually, until_with, and
sequence operator weak are weak: they do not impose any requirement on the
terminating condition, and do not require the clock to tick.
The concept of weak and strong operators is closely related to an important
notion of safety properties. Safety properties have the characteristic that
all their failures happen at a finite time. For example, the property always a
is a safety property since it is violated only if after finitely many clock
ticks there is a clock tick at which a is false, even if there are infinitely
many clock ticks in the computation. To the contrary, a failure of the property
s_eventually a on a computation with infinitely many clock ticks cannot be
identified at a finite time; if it is violated, the value of a must be false
at each of the infinitely many clock ticks.
