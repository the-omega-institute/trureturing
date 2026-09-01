/- GID: D5/S3/Observer/Hilbert/NymanBeurlingTargetQuotientCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/Hilbert/NymanBeurlingTargetQuotientCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hilbert-space equivalences underlying the Nyman-Beurling target quotient criterion. -/

import D5.S3.Quantum.Algebra.DoubleOrthogonalClosure
import D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.List.TFAE

/- Library-search audit trail (2026-09-01):
   * Repository receipt and keyword searches found no formalization of the Nyman-Beurling
     criterion. The nearby observer and analytic receipts for Theorems 29.8 and 29.9 have
     different statements. Generic D5 modules cover double orthogonal closure and increasing
     projection limits, but no existing declaration packages the four target criteria below.
   * Pinned Mathlib provides `Submodule.Quotient.mk_eq_zero`,
     `Submodule.starProjection_apply_eq_zero_iff`, `Metric.mem_closure_iff_infDist_zero`,
     `Metric.infDist_le_infDist_of_subset`, and `Submodule.mem_iSup_of_directed`; each is reused.
     The imported D5 theorem `double_orthogonal_complement_eq_closure` supplies the exact
     double-orthogonal step. No pinned theorem states the full equivalence.
   * Searches of the installed third-party packages found no Nyman-Beurling or Baez-Duarte
     theorem. The analytic Nyman-Beurling theorem is therefore an explicit hypothesis. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Hilbert.NymanBeurlingTargetQuotientCriterion

open Filter Topology
open scoped InnerProductSpace
open D5.S3.Quantum.Algebra.DoubleOrthogonalClosure
open D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Membership in the closed cumulative space, vanishing of the quotient class, vanishing of
the residual projection, and convergence of the finite-stage distances are equivalent. -/
theorem hilbert_target_criteria
    (S : ℕ → Submodule 𝕜 H) (hS : Monotone S) (χ : H) :
    List.TFAE [
      χ ∈ cumulativeSpace S,
      (Submodule.Quotient.mk χ : H ⧸ cumulativeSpace S) = 0,
      ((cumulativeSpace S)ᗮ).starProjection χ = 0,
      Tendsto (fun N => Metric.infDist χ (S N)) atTop (𝓝 0)] := by
  tfae_have 1 ↔ 2 := by
    exact (Submodule.Quotient.mk_eq_zero (p := cumulativeSpace S) (x := χ)).symm
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hχ
      apply (Submodule.starProjection_apply_eq_zero_iff ((cumulativeSpace S)ᗮ)).2
      exact (cumulativeSpace S).le_orthogonal_orthogonal hχ
    · intro hχ
      have hχ' : χ ∈ (cumulativeSpace S)ᗮᗮ :=
        (Submodule.starProjection_apply_eq_zero_iff ((cumulativeSpace S)ᗮ)).1 hχ
      rw [double_orthogonal_complement_eq_closure] at hχ'
      have hclosed : IsClosed ((cumulativeSpace S : Submodule 𝕜 H) : Set H) := by
        exact Submodule.isClosed_topologicalClosure _
      rwa [hclosed.submodule_topologicalClosure_eq] at hχ'
  tfae_have 1 ↔ 4 := by
    constructor
    · intro hχ
      have hclosure : χ ∈ closure ((⨆ N, S N : Submodule 𝕜 H) : Set H) := by
        rw [← Submodule.topologicalClosure_coe]
        exact hχ
      refine tendsto_order.2 ⟨?_, ?_⟩
      · intro b hb
        filter_upwards with N
        exact hb.trans_le Metric.infDist_nonneg
      · intro b hb
        obtain ⟨y, hy, hdist⟩ := (Metric.mem_closure_iff.1 hclosure) b hb
        obtain ⟨N, hyN⟩ : ∃ N, y ∈ S N := by
          change y ∈ (⨆ N, S N) at hy
          rwa [Submodule.mem_iSup_of_directed _ hS.directed_le] at hy
        filter_upwards [eventually_ge_atTop N] with M hNM
        exact (Metric.infDist_le_dist_of_mem (hS hNM hyN)).trans_lt hdist
    · intro hdist
      let U : Submodule 𝕜 H := ⨆ N, S N
      have hle : ∀ N, Metric.infDist χ (U : Set H) ≤ Metric.infDist χ (S N : Set H) := by
        intro N
        exact Metric.infDist_le_infDist_of_subset (le_iSup S N) ⟨0, (S N).zero_mem⟩
      have hnonpos : Metric.infDist χ (U : Set H) ≤ 0 :=
        ge_of_tendsto hdist (Eventually.of_forall hle)
      have hzero : Metric.infDist χ (U : Set H) = 0 :=
        le_antisymm hnonpos Metric.infDist_nonneg
      have hclosure : χ ∈ closure (U : Set H) :=
        (Metric.mem_closure_iff_infDist_zero ⟨0, U.zero_mem⟩).2 hzero
      rw [← Submodule.topologicalClosure_coe] at hclosure
      exact hclosure
  tfae_finish

/-- Abstract form of Theorem 29.4: the external Nyman-Beurling theorem connects `RH` to the
closed-span criterion, while Hilbert-space geometry supplies the other three equivalences. -/
theorem nyman_beurling_target_quotient_criterion
    (RH : Prop) (S : ℕ → Submodule 𝕜 H) (hS : Monotone S) (χ : H)
    (nymanBeurling : RH ↔ χ ∈ cumulativeSpace S) :
    List.TFAE [
      RH,
      χ ∈ cumulativeSpace S,
      (Submodule.Quotient.mk χ : H ⧸ cumulativeSpace S) = 0,
      ((cumulativeSpace S)ᗮ).starProjection χ = 0,
      Tendsto (fun N => Metric.infDist χ (S N)) atTop (𝓝 0)] := by
  have hFour := hilbert_target_criteria S hS χ
  tfae_have 1 ↔ 2 := nymanBeurling
  tfae_have 2 ↔ 3 := hFour.out 0 1
  tfae_have 2 ↔ 4 := hFour.out 0 2
  tfae_have 2 ↔ 5 := hFour.out 0 3
  tfae_finish

/-- The four Hilbert-space criteria can all hold: use a constant line and a vector on it. -/
example :
    let e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    let S : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := fun _ => Submodule.span ℝ {e₁}
    e₁ ∈ cumulativeSpace S ∧
      (Submodule.Quotient.mk e₁ : _ ⧸ cumulativeSpace S) = 0 ∧
      ((cumulativeSpace S)ᗮ).starProjection e₁ = 0 ∧
      Tendsto (fun N => Metric.infDist e₁ (S N)) atTop (𝓝 0) := by
  dsimp only
  let e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  let S : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := fun _ => Submodule.span ℝ {e₁}
  have hFour := hilbert_target_criteria S monotone_const e₁
  have hmem : e₁ ∈ cumulativeSpace S := by
    exact (le_iSup S 0).trans (Submodule.le_topologicalClosure _) <|
      Submodule.mem_span_singleton_self e₁
  exact ⟨hmem, (hFour.out 0 1).1 hmem, (hFour.out 0 2).1 hmem,
    (hFour.out 0 3).1 hmem⟩

/-- The four Hilbert-space criteria can all fail: use the other coordinate vector. -/
example :
    let e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    let e₂ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
    let S : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := fun _ => Submodule.span ℝ {e₁}
    e₂ ∉ cumulativeSpace S ∧
      (Submodule.Quotient.mk e₂ : _ ⧸ cumulativeSpace S) ≠ 0 ∧
      ((cumulativeSpace S)ᗮ).starProjection e₂ ≠ 0 ∧
      ¬Tendsto (fun N => Metric.infDist e₂ (S N)) atTop (𝓝 0) := by
  dsimp only
  let e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  let e₂ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
  let S : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := fun _ => Submodule.span ℝ {e₁}
  have hFour := hilbert_target_criteria S monotone_const e₂
  have hnotmem : e₂ ∉ cumulativeSpace S := by
    simp only [cumulativeSpace, S, iSup_const, Submodule.topologicalClosure_eq_self]
    rw [Submodule.mem_span_singleton]
    rintro ⟨a, ha⟩
    have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) ha
    simp [e₁, e₂] at hcoord
  exact ⟨hnotmem, mt (hFour.out 0 1).2 hnotmem, mt (hFour.out 0 2).2 hnotmem,
    mt (hFour.out 0 3).2 hnotmem⟩

#print axioms hilbert_target_criteria
#print axioms nyman_beurling_target_quotient_criterion

end D5.S3.Observer.Hilbert.NymanBeurlingTargetQuotientCriterion
