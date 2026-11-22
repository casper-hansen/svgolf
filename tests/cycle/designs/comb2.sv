// tests/cycle: two continuous assignments beside a register, the second reading the first's signal (sv_mirror covers
// them; sv_cycle refuses the clock step by name: a comb process that reads a signal a comb process drives).
module comb2 #(parameter int N = 4) (
  input  logic         clk,
  input  logic [N-1:0] a, b,
  output logic [N-1:0] q
);
  logic [N-1:0] t, u;
  assign t = a | b;
  assign u = t & a;
  always_ff @(posedge clk) q <= u;
endmodule
