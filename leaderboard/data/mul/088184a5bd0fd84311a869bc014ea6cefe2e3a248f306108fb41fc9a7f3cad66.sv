// svGolf task `mul` -- reference solution 5: a log-depth carry-save TREE multiplier whose leaves each hold TWO
// partial-product rows, parametric in N, written with a LOCALPARAM.
//
// The N partial-product rows pp[j] (the shifted copies of a, gated by the bits of b) are taken two at a time:
// leaf j of H = ceil(N/2) holds the carry-save pair (S, C) = (pp[2j], pp[2j+1]), two rows being already a
// pair. The H leaves are those of one balanced binary tree in a binary-HEAP numbering: the root is node 0,
// node k has the children 2k+1 and 2k+2, the H-1 internal nodes are 0 .. H-2 and the H leaves H-1 .. 2H-2.
// EVERY internal node is a 4:2 compressor on its two children's pairs: two stacked rows of 3:2 counters
// (full adders), the first row X/Y, the second S/C; the two rows of the root go through a ripple-carry
// final adder. There is no pairing node and no constant select: a node never has to be told apart from
// its siblings, which is what the single-row tree (mul_tree.sv) needs th/nth for.
//
// The one non-affine quantity, H = ceil(N/2), is a `localparam integer` defined by a division by a literal:
// the sv_comb tactics read it as one more named constant of N (PROVING.md, section 4), so every index and
// bound stays an integer constant expression and `omega` decides the obligations (H = (N + 1) / 2 is
// known to it). `bb` is `b` zero-extended to 2H+1 bits, so the last leaf of an odd N has a zero row.
// A shifted partial product is a GATHER read of `ae`, the zero-padded copy of `a`, so no write ever
// leaves its vector. All sums are taken modulo 2^(2N), exactly the width of the product.
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  localparam integer H = (N + 1) / 2;   // leaves: ceil(N/2) pairs of partial-product rows

  logic [4*N-2:0]          ae;   // ae[x] = a[x-(2N-1)] for 2N-1 <= x < 3N-1, else 0
  logic [2*H:0]            bb;   // b zero-extended
  logic [2*H-2:0][2*N-1:0] S, C; // sum / carry row of each heap node
  logic [H-1:0][2*N-1:0]   X, Y; // first-row sum / carry of node k (row H-1 unused)
  localparam integer M = (7 * N) / 8;
  localparam integer U = 2*N - M;
  localparam integer FQ = U / 5;
  localparam integer FR = U % 5;
  localparam integer FL = $clog2(FQ + 1);
  logic [M:0] R;
  logic [U-1:0] fp, fg;
  logic [FQ:0][5:0] fgg, fpp, fcc;
  logic [FL:0][FQ:0] bg, bp;
  logic [FR:0] Rt;

  assign ae[2*N-2:0]     = '0;
  assign ae[3*N-2:2*N-1] = a;
  assign ae[4*N-2:3*N-1] = '0;
  assign bb[N-1:0]       = b;
  assign bb[2*H:N]       = '0;
  assign X[H-1]          = '0;
  assign Y[H-1]          = '0;
  assign R[0] = 1'b0;
  assign bg[0][0] = R[M];
  assign bp[0][0] = 1'b0;
  assign fgg[FQ] = '0;
  assign fpp[FQ] = '0;
  assign fcc[FQ] = '0;
  assign Rt[0] = bg[FL][FQ];

  genvar j, k, c, t, fl;
  generate
    // leaves: node H-1+j is the pair of partial-product rows 2j and 2j+1 (gather reads of ae)
    for (j = 0; j < H; j++) begin : g_leaf
      for (c = 0; c < 2*N; c++) begin : g_lc
        assign S[H-1+j][c] = bb[2*j] & ae[c + 2*N - 1 - 2*j];
        assign C[H-1+j][c] = ae[c + 2*N - 2 - 2*j] & bb[2*j+1];
      end
    end
    // internal nodes: a 4:2 compressor on the children 2k+1, 2k+2
    for (k = 0; k < H-1; k++) begin : g_node
      assign Y[k][0] = 1'b0;
      assign C[k][0] = 1'b0;
      for (c = 0; c < 2*N; c++) begin : g_col
        assign X[k][c] = (S[2*k+2][c] ^ C[2*k+1][c]) ^ S[2*k+1][c];
        assign S[k][c] = (X[k][c] ^ C[2*k+2][c]) ^ Y[k][c];
      end
      for (c = 0; c < 2*N-1; c++) begin : g_car
        assign Y[k][c+1] = (S[2*k+2][c] ^ C[2*k+1][c]) ? S[2*k+1][c] : C[2*k+1][c];
        assign C[k][c+1] = (Y[k][c] ^ C[2*k+2][c]) ? X[k][c] : C[2*k+2][c];
      end
    end
    for (c = 0; c < M; c++) begin : g_fin_lo
      assign p[c]   = S[0][c] ^ (C[0][c] ^ R[c]);
      assign R[c+1] = (C[0][c] ^ S[0][c]) ? R[c] : S[0][c];
    end
    for (c = 0; c < U; c++) begin : g_fpg
      assign fp[c] = S[0][M+c] ^ C[0][M+c];
      assign fg[c] = S[0][M+c] & C[0][M+c];
    end
    for (j = 0; j < FQ; j++) begin : g_fblk
      assign fgg[j][0] = 1'b0;
      assign fpp[j][0] = 1'b1;
      for (t = 0; t < 5; t++) begin : g_frip
        assign fgg[j][t+1] = fg[5*j+t] | (fp[5*j+t] & fgg[j][t]);
        assign fpp[j][t+1] = fp[5*j+t] & fpp[j][t];
      end
      assign bg[0][j+1] = fgg[j][5];
      assign bp[0][j+1] = fpp[j][5];
    end
    for (fl = 0; fl < FL; fl++) begin : g_flvl
      for (j = 0; j < FQ + 1; j++) begin : g_fnd
        if (j >= (1 << fl)) begin : g_fop
          assign bg[fl+1][j] = bg[fl][j] | (bp[fl][j] & bg[fl][j - (1 << fl)]);
          assign bp[fl+1][j] = bp[fl][j] & bp[fl][j - (1 << fl)];
        end else begin : g_fpass
          assign bg[fl+1][j] = bg[fl][j];
          assign bp[fl+1][j] = bp[fl][j];
        end
      end
    end
    for (j = 0; j < FQ; j++) begin : g_floc
      assign fcc[j][0] = bg[FL][j];
      for (t = 0; t < 5; t++) begin : g_flc
        assign fcc[j][t+1] = fp[5*j+t] ? fcc[j][t] : S[0][M+5*j+t];
        assign p[M+5*j+t] = S[0][M+5*j+t] ^ (C[0][M+5*j+t] ^ fcc[j][t]);
      end
    end
    for (t = 0; t < FR; t++) begin : g_ftail
      assign Rt[t+1]     = fg[5*FQ+t] | (fp[5*FQ+t] & Rt[t]);
      assign p[M+5*FQ+t] = fp[5*FQ+t] ^ Rt[t];
    end
  endgenerate
endmodule
