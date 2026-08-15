/- GID: D5/S3/Quantum/Algebra/QuotientContractionRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/QuotientContractionRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A strict contraction on a closed-subspace quotient has no nonzero fixed class. -/

import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/- Library-search audit trail (2026-08-16):
   * Repository search found no D5 quotient-contraction rigidity declaration.
   * Pinned-Mathlib name and type searches found no exact fixed-point theorem. They found
     `Submodule.mkQL`, `Submodule.liftQL`, `ContinuousLinearMap.le_opNorm`, and
     `Submodule.Quotient.mk_eq_zero`, which are imported and composed below.
   * Loogle query `‖?f‖ < 1 → ?f ?x = ?x → ?x = 0` returned no exact match.
   * LeanSearch's `/api/search` request failed and is not counted as a negative result.
   * GitHub Lean-code searches for `ContinuousLinearMap "fixed point"`, `"norm_lt_one" fixed`,
     and `"le_opNorm" fixed` returned no hits. -/

namespace D5.S3.Quantum.Algebra.QuotientContractionRigidity

variable {𝕜 H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

/-- The continuous linear map on `H ⧸ M` induced by a continuous linear endomorphism that
preserves `M`. -/
def inducedQuotientMap (M : Submodule 𝕜 H) (R : H →L[𝕜] H)
    (h_invariant : ∀ y ∈ M, R y ∈ M) :
    (H ⧸ M) →L[𝕜] (H ⧸ M) :=
  M.liftQL (M.mkQL.comp R) (by
    intro y hy
    change M.mkQ (R y) = 0
    exact (Submodule.Quotient.mk_eq_zero (p := M)).mpr (h_invariant y hy))

@[simp]
theorem inducedQuotientMap_mkQ (M : Submodule 𝕜 H) (R : H →L[𝕜] H)
    (h_invariant : ∀ y ∈ M, R y ∈ M) (y : H) :
    inducedQuotientMap M R h_invariant (M.mkQ y) = M.mkQ (R y) := by
  rfl

/-- If `R` fixes `x` modulo a closed invariant subspace `M` and the induced quotient operator
has norm strictly less than one, then `x` belongs to `M`. -/
theorem quotient_contraction_rigidity
    (M : Submodule 𝕜 H) [IsClosed (M : Set H)] (R : H →L[𝕜] H)
    (h_invariant : ∀ y ∈ M, R y ∈ M) (x : H)
    (h_fixed_mod : R x - x ∈ M)
    (h_contract : ‖inducedQuotientMap M R h_invariant‖ < 1) :
    x ∈ M := by
  have h_mk_sub : M.mkQ (R x - x) = 0 := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact h_fixed_mod
  have h_mk_eq : M.mkQ (R x) = M.mkQ x := by
    rw [← sub_eq_zero, ← map_sub]
    exact h_mk_sub
  have h_quotient_fixed : inducedQuotientMap M R h_invariant (M.mkQ x) = M.mkQ x := by
    rw [inducedQuotientMap_mkQ, h_mk_eq]
  by_contra hx
  have h_mk_ne : M.mkQ x ≠ 0 := by
    intro hzero
    exact hx ((Submodule.Quotient.mk_eq_zero (p := M)).mp hzero)
  have h_norm_pos : 0 < ‖M.mkQ x‖ := norm_pos_iff.mpr h_mk_ne
  have h_norm_le :
      ‖M.mkQ x‖ ≤ ‖inducedQuotientMap M R h_invariant‖ * ‖M.mkQ x‖ := by
    simpa only [h_quotient_fixed] using
      (inducedQuotientMap M R h_invariant).le_opNorm (M.mkQ x)
  have h_norm_lt :
      ‖inducedQuotientMap M R h_invariant‖ * ‖M.mkQ x‖ < ‖M.mkQ x‖ := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right h_contract h_norm_pos
  exact (not_lt_of_ge h_norm_le) h_norm_lt

example : ℝ := 0

#print axioms quotient_contraction_rigidity

end D5.S3.Quantum.Algebra.QuotientContractionRigidity
