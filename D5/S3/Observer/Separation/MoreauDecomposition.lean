/- GID: D5/S3/Observer/Separation/MoreauDecomposition
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/MoreauDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Closed convex cones admit a unique orthogonal polar decomposition. -/

import D5.S3.Observer.Separation.ConeResidualWitness

/- Library-search audit trail (2026-08-17):
   * Repository search found `ConeResidualWitness.coneProjection` and its residual-duality
     theorem, but no existence-and-uniqueness declaration for the full decomposition.
   * Pinned-Mathlib source and local smart searches found no declaration named for Moreau
     decomposition. Loogle query `"Moreau"` returned zero declarations.
   * Loogle returned the exact Hilbert projection primitive
     `exists_norm_eq_iInf_of_complete_convex`; Mathlib also supplies the exact variational
     characterization `norm_eq_iInf_iff_real_inner_le_zero`. Both are applied below. -/

namespace D5.S3.Observer.Separation.MoreauDecomposition

open Set
open scoped RealInnerProductSpace

open D5.S3.Observer.Separation.ConeResidualWitness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Every vector has a unique decomposition into a point of a closed convex cone and an
orthogonal residual in its polar cone. Mathlib defines `innerDual` with the nonnegative
sign convention, so membership of the residual in the polar cone is written `-r ∈ innerDual C`. -/
theorem moreau_decomposition (C : ProperCone Real E) (x : E) :
    ∃! decomposition : E × E,
      decomposition.1 ∈ C ∧
        -decomposition.2 ∈ ProperCone.innerDual (C : Set E) ∧
          inner Real decomposition.1 decomposition.2 = 0 ∧
            x = decomposition.1 + decomposition.2 := by
  let p := coneProjection C x
  let r := x - p
  have hprojection :=
    Classical.choose_spec
      (exists_norm_eq_iInf_of_complete_convex
        C.nonempty C.isClosed.isComplete C.convex x)
  have hp : p ∈ C := by
    simpa [p, coneProjection] using hprojection.1
  have hminimal : ‖x - p‖ = ⨅ c : (C : Set E), ‖x - c‖ := by
    simpa [p, coneProjection] using hprojection.2
  have hvariational : ∀ c ∈ C, inner Real r (c - p) ≤ 0 := by
    simpa [r] using
      (norm_eq_iInf_iff_real_inner_le_zero C.convex hp).mp hminimal
  have hinner_nonneg : 0 ≤ inner Real r p := by
    have hzero := hvariational 0 C.zero_mem
    rw [zero_sub, inner_neg_right] at hzero
    linarith
  have hinner_nonpos : inner Real r p ≤ 0 := by
    have htwop : (2 : Real) • p ∈ C := C.smul_mem hp (by norm_num)
    have htwo := hvariational ((2 : Real) • p) htwop
    simpa [two_smul] using htwo
  have hrp : inner Real r p = 0 :=
    le_antisymm hinner_nonpos hinner_nonneg
  have hpolar : ∀ c ∈ C, inner Real r c ≤ 0 := by
    intro c hc
    have hadd := hvariational (c + p) (C.add_mem hc hp)
    simpa using hadd
  have hdual : -r ∈ ProperCone.innerDual (C : Set E) := by
    rw [ProperCone.mem_innerDual]
    intro c hc
    rw [inner_neg_right, real_inner_comm]
    exact neg_nonneg.mpr (hpolar c hc)
  have hpr : inner Real p r = 0 := by
    rw [real_inner_comm]
    exact hrp
  have hx : x = p + r := by
    dsimp [r]
    abel
  refine ⟨(p, r), ⟨hp, hdual, hpr, hx⟩, ?_⟩
  rintro ⟨q, s⟩ ⟨hq, hsdual, hqs, hxs⟩
  have hps : inner Real p s ≤ 0 := by
    have h := ProperCone.mem_innerDual.mp hsdual hp
    rw [inner_neg_right] at h
    linarith
  have hqr : inner Real q r ≤ 0 := by
    have h := ProperCone.mem_innerDual.mp hdual hq
    rw [inner_neg_right] at h
    linarith
  have hsum : p + r = q + s := hx.symm.trans hxs
  have hdifference : p - q = s - r := by
    calc
      p - q = (p + r) - (q + r) := by abel
      _ = (q + s) - (q + r) := by rw [hsum]
      _ = s - r := by abel
  have hself_nonpos : inner Real (p - q) (p - q) ≤ 0 := by
    calc
      inner Real (p - q) (p - q) = inner Real (p - q) (s - r) := by
        rw [hdifference]
      _ = inner Real p s - inner Real p r -
          (inner Real q s - inner Real q r) := by
        rw [inner_sub_left p q (s - r), inner_sub_right p s r, inner_sub_right q s r]
      _ ≤ 0 := by rw [hpr, hqs]; linarith
  have hpq : p = q := by
    rw [real_inner_self_nonpos] at hself_nonpos
    exact sub_eq_zero.mp hself_nonpos
  have hsr : s = r := by
    apply add_left_cancel (a := p)
    simpa [hpq] using hsum.symm
  exact Prod.ext hpq.symm hsr

#print axioms moreau_decomposition

end D5.S3.Observer.Separation.MoreauDecomposition
