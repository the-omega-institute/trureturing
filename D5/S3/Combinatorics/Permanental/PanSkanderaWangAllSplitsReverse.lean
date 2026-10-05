/- GID: D5/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsReverse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permanental/PanSkanderaWangAllSplitsReverse
   mirror-E: none(waiver:direct-Lean-proof-of-pan-skandera-wang-all-split-inequality)
   anchors: []
   utility: none
   digest: Reversal transports TNN matrices and swaps complementary splits. -/

/- Mathematical classification: data and predicate definitions only.
   admission_basis: none (definition support for the all-split result)
   utility reason: general statements at arbitrary orders, not a bounded certificate.
   Direct frozen dependencies:
     none (the frozen PSW theorem is used through the supporting modules).
   Information-escape registration is paused under CLAUDE.md section 3.9. -/

import D5.S3.Combinatorics.Permanental.PanSkanderaWangAllSplitsPermanentPadding

open Finset Matrix Equiv
namespace PSW
open scoped Classical

/-- Reverse rows and columns simultaneously, preserving the ordered-minor signs. -/
def reverseMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A.submatrix Fin.rev Fin.rev

end PSW
