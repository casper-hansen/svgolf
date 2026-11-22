// tests/cycle: a one-deep generated family of continuous assignments, alone in its generate block (word k of t is
// a[k] ^ b[k]), beside one register at the module level: a flat comb part whose family is a `List.map` over the
// loop (sv_cycle covers its clock step, any size).
module famword #(parameter int N = 4, parameter int W = 8) (
  input  logic           clk,
  input  logic [N*W-1:0] a, b,
  output logic [N*W-1:0] q
);
  logic [N*W-1:0] t;
  for (genvar k = 0; k < N; k++) begin : g_word
    assign t[k*W +: W] = a[k*W +: W] ^ b[k*W +: W];
  end
  always_ff @(posedge clk) q <= t;
endmodule
