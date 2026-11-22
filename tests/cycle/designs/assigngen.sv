// tests/cycle: continuous assignments inside a generate loop (one per word) and one at the module level that reads
// the family's signal (u = t | a), beside a register: sv_mirror covers them; sv_cycle refuses the clock step by name
// (a comb process that reads a signal a comb process drives: not a flat comb part).
module assigngen #(parameter int N = 4, parameter int W = 8) (
  input  logic           clk,
  input  logic [N*W-1:0] a, b,
  output logic [N*W-1:0] q
);
  logic [N*W-1:0] t, u;
  for (genvar k = 0; k < N; k++) begin : g_word
    assign t[k*W +: W] = a[k*W +: W] ^ b[k*W +: W];
  end
  assign u = t | a;
  always_ff @(posedge clk) q <= u;
endmodule
