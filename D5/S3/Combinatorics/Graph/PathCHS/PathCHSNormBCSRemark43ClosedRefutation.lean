/- GID: D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.claim; result=D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.result; claim=D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.claim
   digest: A boundary case refutes the proposed one-term formula. -/

/-
admission_basis: open-problem-resolution (#18567; Refuted)
escape_witness: none
For the witness n = 2, the eigenvalues have sum zero and product minus one. Expanding the seven
terms of the degree-six complete homogeneous polynomial therefore gives one;
this fixed-instance calculation supplies a finite normalization bypass.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
Declaration proof_shape (same-delivery helpers expanded):
  claim: bind-only; consumers: result.
  result: bind-only; consumers: settling result.
-/

import D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm

open D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductAlgebra

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43ClosedRefutation

open D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm

/-- Bouthat–Chávez–Sheng, arXiv:2606.17356v1, end of Remark 4.3 ("In particular, if n+1 ≥ d/2, the sum
becomes ‖P_n‖_{X,d}^d = (n²+n−d)/((n+d)(n+d+1)) binom(n+d+1, d/2)"), for `n ≥ 1` and even `d ≥ 2`. -/
def claim : Prop :=
  ∀ n d : ℕ, 1 ≤ n → 2 ≤ d → Even d → d / 2 ≤ n + 1 →
    chs n d = ((n : ℝ) ^ 2 + n - d) / ((n + d) * (n + d + 1)) * (Nat.choose (n + d + 1) (d / 2) : ℝ)


end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43ClosedRefutation

namespace D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43ClosedRefutation
open D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm

theorem result : ¬ claim := by
  have h6 : chs 2 6 = 1 := by
    have hf : pathFormula 2 3 = 1 := Eq.symm ((fun {a b} => Int.neg_inj.mp) rfl)
    simpa only [hf,Int.cast_one] using D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chs_formula 2 3
  intro hc
  have he := hc 2 6 NeZero.one_le Nat.AtLeastTwo.prop
    (Nat.even_iff.mpr rfl) (Nat.le_add_left (6 / 2) 0)
  norm_num [h6] at he

end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43ClosedRefutation
