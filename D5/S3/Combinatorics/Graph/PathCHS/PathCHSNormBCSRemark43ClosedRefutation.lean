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
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
Direct frozen dependencies (declaration statement_id):
  D5/S0/Conventions/IntegerIndexBinomial.binom = sha256:1b5d115d3154df46a4f4c71aecf721ba76b76342a8accd9a42835a7efcd0ea68
  D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductContinuants.cont = sha256:19af67c82efc5874450f4ad32eb6bde111939a02aabcd0f72501879f5c32a817
  D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.PS = sha256:2d46169a6d2871c90eab4fdbaa167dba26d8f6f62bf20bd742893956c989794e
  D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.binomialCoefficient = sha256:e633460d785a69db1779401737563030445a32266f87f53d0e3222753412caa6
  D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q = sha256:74bb80061068763bfcd8db53c51b9e3e5b2c3b39c9f0b7b72a73f8d0f2bb1917
  D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_constantCoeff = sha256:ee126d120dacce4ad39408a9e755a57608f4ea38d4d36b3fc9e66ff89ce8c4eb
  D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_equation = sha256:e979565eb30d5b39c38b0532f6b82822fc311008796f10ada96bf0bc6c643d3e
  D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge.q_subst_coefficient_transform = sha256:5e8caaadeda02486d4b5489d458781fc3ed3507ed89a73adbb3ccac48ce6877f
  D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.det_sparse_front = sha256:c757f994f53837ddb59a934a6718fd1f6d8469440e070cd1b9fed64d3dc27c97
Declaration proof_shape (same-delivery helpers inlined; escape_witness: none):
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
    have hf : pathFormula 2 3 = 1 := by decide
    simpa only [hf,Int.cast_one] using D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chs_formula 2 3
  intro hc
  have he := hc 2 6 (by decide) (by decide) (by decide) (by decide)
  norm_num [h6] at he

end D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormBCSRemark43ClosedRefutation
