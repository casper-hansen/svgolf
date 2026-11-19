// tests/cycle: a generate `if` on a genvar inside a generate loop (the first stage of a shift register apart):
// sv_mirror keeps the family's two cases as an `if` on the genvar, each instantiated under its case.
module genifk #(parameter int N = 4, parameter int W = 8) (
  input  logic           clk,
  input  logic [W-1:0]   d,
  output logic [N*W-1:0] s
);
  for (genvar k = 0; k < N; k++) begin : g_stage
    if (k == 0) begin : g_head
      always_ff @(posedge clk) s[0 +: W] <= d;
    end else begin : g_tail
      always_ff @(posedge clk) s[k*W +: W] <= s[(k-1)*W +: W];
    end
  end
endmodule
