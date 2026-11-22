// tests/cycle: a two-deep generated family of continuous assignments (cell (i, j) of t is a[i][j] ^ b[j][i]) that
// feeds a family of registers (cell (i, j) of q): sv_cycle covers the clock step of a flat comb part (continuous
// assignments to pairwise disjoint static windows, none reading a signal a comb process drives), any size.
module famgrid #(parameter int N = 2, parameter int W = 4) (
  input  logic             clk,
  input  logic [N*N*W-1:0] a, b,
  output logic [N*N*W-1:0] q
);
  logic [N*N*W-1:0] t;
  for (genvar i = 0; i < N; i++) begin : g_row
    for (genvar j = 0; j < N; j++) begin : g_cell
      assign t[(i*N+j)*W +: W] = a[(i*N+j)*W +: W] ^ b[(j*N+i)*W +: W];
      always_ff @(posedge clk) q[(i*N+j)*W +: W] <= t[(i*N+j)*W +: W];
    end
  end
endmodule
