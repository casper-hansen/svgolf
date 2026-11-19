// tests/cycle: a generate `if` on a parameter: sv_mirror keeps both branches as an `if` of the process list, or
// takes the one a hypothesis decides; sv_cycle covers the decided mirror and refuses the branching one by name.
module genif #(parameter int N = 4, parameter int W = 8) (
  input  logic         clk,
  input  logic [W-1:0] d,
  output logic [W-1:0] q
);
  if (N == 1) begin : g_one
    always_ff @(posedge clk) q <= d;
  end else begin : g_many
    always_ff @(posedge clk) q <= ~d;
  end
endmodule
