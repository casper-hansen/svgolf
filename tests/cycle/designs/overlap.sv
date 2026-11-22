// tests/cycle: a generated family of continuous assignments whose windows overlap when W = 1 (word k drives
// t[k*W +: 2]; disjoint at the default W = 2): sv_mirror covers the instantiation; sv_cycle refuses the clock step
// by name (the windows are not disjoint at every size: no one-driver rule, no settle).
module overlap #(parameter int N = 2, parameter int W = 2) (
  input  logic           clk,
  input  logic [N*W+1:0] a,
  output logic [N*W+1:0] q
);
  logic [N*W+1:0] t;
  for (genvar k = 0; k < N; k++) begin : g_w
    assign t[k*W +: 2] = a[k*W +: 2];
  end
  always_ff @(posedge clk) q <= t;
endmodule
