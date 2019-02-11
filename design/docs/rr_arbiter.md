# Description
This module is a parameterized round robin arbiter.
# Specifications
This module arbiterates among requenstors and returns grants
to the active requests in round robin order. Out of reset,
client 0 has the highest priority.
## IO specifications:
### request:
This bus has a bit for each client. The bit is an active high
signal. Once asserted for a client, the request must be held high
for that client till a grant is received.

### stall:
This signal stalls the arbitration. No grants are issues during
the stalled cycle.

### grant:
This bus has a bit for each client. The bit indicates a grant
for the corresponding client. A grant can come the same cycle
as the request is presented.

```sv
module rr_arbiter #(
  parameter CLIENTS = 8
  )
  (
  input      [CLIENTS-1:0] request,
  input                    stall,
  output reg [CLIENTS-1:0] grant,
  input                    clock,
  input                    reset);

  parameter CLIENTS_W = $clog2(CLIENTS);

  logic [CLIENTS_W-1:0] last_selected;
  logic [CLIENTS_W-1:0] next_selected;

  wire [CLIENTS-1:0] rotated_request = (request >> last_selected) |
                                       (request << (CLIENTS - last_selected));

  always_comb begin
    next_selected = '0;
    for (int i=CLIENTS-1; i>0; i--) begin
      if (rotated_request[i]) begin
        next_selected = i;
      end
    end
    next_selected = next_selected + last_selected;
  end

  always @(posedge clock) begin
    if (reset) begin
      last_selected <= '0;
    end
    else begin
      if (!stall) begin
        last_selected <= next_selected;
      end
    end
  end

  always_comb begin
    grant = '0;
    if (!stall) begin
      grant[next_selected] = 1'b1;
    end
  end

endmodule
```
