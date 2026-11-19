// tests/cycle: a family whose process reads the window `(k-1)*W` in the `else` of an `if (k == 0)`: at `k = 0`
// that window leaves its vector (the instantiation reads it as `x`, in the branch that is not taken), so no
// window tactic proves it; sv_mirror splits the process at the loop's first value, `if k = 0 then … else …`.
module edge_split #(parameter int N = 4, parameter int W = 8) (
  input  logic           clk,
  input  logic [W-1:0]   d,
  output logic [N*W-1:0] s
);
  for (genvar k = 0; k < N; k++) begin : g_stage
    always_ff @(posedge clk)
      if (k == 0) s[k*W +: W] <= d;
      else        s[k*W +: W] <= s[(k-1)*W +: W];
  end
endmodule
