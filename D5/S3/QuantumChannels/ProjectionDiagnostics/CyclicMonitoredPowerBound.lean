/- GID: D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredPowerBound
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredPowerBound
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The actual cyclic monitored operator has a strictly contracting power. -/

import D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredContraction
import D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit

/-! The actual cyclic no-dark theorem feeds the frozen dark-block estimate. -/

noncomputable section
open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredPowerBound

open CyclicMonitoredContraction
open D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

private theorem conservation (U : E ≃ₗᵢ[ℂ] E) (v : E) :
    star (cyclicStep U v) * cyclicStep U v +
      star (cyclicClick U v) * cyclicClick U v = 1 := by
  have hinner (x y : cyclicSpace U v) :
      inner ℂ (cyclicStep U v x) (cyclicStep U v y) +
        inner ℂ (cyclicClick U v x) (cyclicClick U v y) = inner ℂ x y := by
    let P := (ℂ ∙ v).starProjection
    have h1 := (ℂ ∙ v).starProjection_inner_eq_zero (U (x : E))
      (P (U (y : E))) ((ℂ ∙ v).starProjection_apply_mem _)
    have h2 := (inner_eq_zero_symm).2
      ((ℂ ∙ v).starProjection_inner_eq_zero (U (y : E))
        (P (U (x : E))) ((ℂ ∙ v).starProjection_apply_mem _))
    rw [inner_sub_left] at h1
    rw [inner_sub_right] at h2
    have h1' := sub_eq_zero.mp h1
    have h2' := sub_eq_zero.mp h2
    change inner ℂ (U (x : E) - P (U (x : E)))
      (U (y : E) - P (U (y : E))) +
      inner ℂ (P (U (x : E))) (P (U (y : E))) = inner ℂ (x : E) (y : E)
    simp only [inner_sub_left, inner_sub_right, h1', h2', sub_self, sub_zero,
      sub_add_cancel, U.inner_map_map]
  ext x
  apply ext_inner_left ℂ
  intro y
  simpa only [ContinuousLinearMap.add_apply, mul_apply_eq_comp,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_add_right] using hinner y x

/-- Strict power contraction on the actual cyclic monitored space. -/
theorem cyclic_power_contraction (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ‖cyclicStep U v ^ N‖ ≤ q := by
  classical
  let C := cyclicSpace U v
  let A := cyclicStep U v
  let B := cyclicClick U v
  let d := Module.finrank ℂ C
  let e := (stdOrthonormalBasis ℂ C).repr
  let M := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  let φ := e.conjStarAlgEquiv.trans M.symm
  let Q := φ A
  let L : Unit → Matrix (Fin d) (Fin d) ℂ := fun _ => φ B
  have hφ (X : C →L[ℂ] C) : M (φ X) = e.conjStarAlgEquiv X := by
    simp [φ]
  have hcomp : Qᴴ * Q + ∑ i : Unit, (L i)ᴴ * L i = 1 := by
    have h := congrArg φ (conservation U v)
    simpa only [map_add, map_mul, map_star, map_one, Matrix.star_eq_conjTranspose,
      Finset.univ_unique, Finset.sum_singleton, Q, L, A, B] using h
  have hzero : darkSpace Q L = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro y hy
    change y = 0
    have hx : e.symm y ∈ (⨅ n : ℕ, LinearMap.ker
        (B.toLinearMap.comp (A.toLinearMap ^ n))) := by
      apply (Submodule.mem_iInf _).mpr
      intro n
      have hn := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hy n) ()
      rw [LinearMap.mem_ker] at hn ⊢
      have hm : M (φ (B * A ^ n)) y = 0 := by
        simpa only [map_mul, map_pow, Q, L] using hn
      rw [hφ, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] at hm
      have hm' := e.injective (by simpa using hm)
      simpa only [mul_apply_eq_comp, ContinuousLinearMap.toLinearMap_pow] using hm'
    rw [cyclic_future_kernel_eq_bot U v] at hx
    have hx' : e.symm y = 0 := hx
    have := congrArg e hx'
    simpa using this
  have hD : darkProjection Q L = 0 := by
    simp [darkProjection, hzero]
  have hd : d ≠ 0 := by
    intro hd
    haveI : Subsingleton C := (Module.finrank_eq_zero_iff.mp hd)
    have hvmem : v ∈ C := Submodule.subset_span ⟨0, rfl⟩
    have hz : (⟨v, hvmem⟩ : C) = 0 := Subsingleton.elim _ _
    have hvzero : v = 0 := congrArg Subtype.val hz
    simpa [hvzero] using hv
  obtain ⟨g, c, hg, _, _, _, _, _, _, _, _, hn, hgd, _⟩ :=
    dark_block_contraction Q L hcomp hd
  have hn' : ‖Q ^ d‖ ^ 2 ≤ 1 - g := by
    have h := hn d
    rw [hD, sub_zero, ← Matrix.conjTranspose_pow,
      ← Matrix.star_eq_conjTranspose, CStarRing.norm_star_mul_self, ← sq, ← hgd] at h
    exact h
  have hnorm : ‖A ^ d‖ < 1 := by
    have hnormeq : ‖Q ^ d‖ = ‖A ^ d‖ := by
      rw [← map_pow, StarAlgEquiv.norm_map]
    rw [hnormeq] at hn'
    have hsq : ‖A ^ d‖ ^ 2 < 1 := lt_of_le_of_lt hn' (sub_lt_self _ hg)
    exact (sq_lt_one_iff₀ (norm_nonneg _)).mp hsq
  exact ⟨d, Nat.one_le_iff_ne_zero.mpr hd, ‖A ^ d‖, norm_nonneg _, hnorm, le_rfl⟩

#print axioms cyclic_power_contraction

end D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredPowerBound
