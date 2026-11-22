// tests/cycle: two continuous assignments that read only the inputs, beside a register: a flat comb part at the
// module level (sv_cycle covers it, the continuous windows disjoint by evaluation).
module assign2 #(parameter int N = 4) (
  input  logic         clk,
  input  logic [N-1:0] a, b,
  output logic [N-1:0] q
);
  logic [N-1:0] t, u;
  assign t = a | b;
  assign u = a & b;
  always_ff @(posedge clk) q <= t ^ u;
endmodule
