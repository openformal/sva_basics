/*s_md
# Description
This testbench shows how to add arguments to properties to make them
reusable.

# DUT
This testbench uses a round robin arbiter as a context for introducing the
concepts. The dut design file is -
[sva_basics/design/src/rr_arbiter.sv](https://github.com/openformal/sva_basics/blob/master/design/docs/rr_arbiter.md)

e_md*/

//s_sv
module arguments_tb();

  logic clock;
  logic reset;

  parameter CLIENTS = 32;

  logic [CLIENTS-1:0] request;
  logic [CLIENTS-1:0] grant;

//md In this testbench stall is disabled
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

/*s_md
# Overview
Adding arguments to properties makes them reusable.
These arguments may or may not have type defined.
## Property with formal arguments without type
e_md*/
  property gnt4_in_31_cycles_P1(req, gnt);
    req |-> ##[0:31] gnt;
  endproperty;

  gnt4_in_31_cycles_AT1: assert property (
    @(posedge clock) (gnt4_in_31_cycles_P1(request[4], grant[4]))
  );

//md ## Property with formal arguments with type
  property gnt4_in_31_cycles_P2(logic req, logic gnt);
    req |-> ##[0:31] gnt;
  endproperty;

  gnt4_in_31_cycles_AT2: assert property (
    @(posedge clock) (gnt4_in_31_cycles_P2(request[4], grant[4]))
  );

endmodule
//e_sv
