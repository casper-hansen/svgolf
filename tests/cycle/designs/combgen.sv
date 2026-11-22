// tests/cycle: an always_comb inside a generate loop (sv_mirror covers it; sv_cycle refuses an always_comb process
// among several comb processes by name: only continuous assignments form a flat comb part).
module combgen #(parameter int N = 4) (
  input  logic         clk,
  input  logic [N-1:0] a, b,
  output logic [N-1:0] q
);
  logic [N-1:0] t;
  for (genvar k = 0; k < N; k++) begin : g_and
    always_comb t[k] = a[k] & b[k];
  end
  always_ff @(posedge clk) q <= t;
endmodule
