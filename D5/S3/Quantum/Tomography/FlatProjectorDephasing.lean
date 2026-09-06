/- GID: D5/S3/Quantum/Tomography/FlatProjectorDephasing
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/FlatProjectorDephasing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An existing normalized rank-one projector with diagonal one-sixth has a canonical dephased unit-modulus lift obtained from its first column. -/

import D5.S3.Quantum.Tomography.RankOneContextCommutator

/- Reuse audit:
   * Uses the existing `IsNormalizedRankOneProjection`, in particular its
     compression law `P X P = trace (P X) • P`.
   * Does not introduce another orthonormal-basis, rank-one-projector, or
     matrix carrier. This is only the physical-projector-to-root adapter.
-/

open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.FlatProjectorDephasing

open Matrix
open D5.S3.Quantum.Tomography.RankOneContextCommutator

private theorem coordinate_compression
    (P : Matrix (Fin 6) (Fin 6) ℂ)
    (hP : IsNormalizedRankOneProjection P) (i j : Fin 6) :
    P i 0 * P 0 j = P 0 0 * P i j := by
  let E : Matrix (Fin 6) (Fin 6) ℂ :=
    fun k l ↦ if k = 0 ∧ l = 0 then 1 else 0
  have hPE : P * E = fun k l ↦ if l = 0 then P k 0 else 0 := by
    ext k l
    by_cases hl : l = 0
    · subst l
      simp [Matrix.mul_apply, E]
    · simp [Matrix.mul_apply, E, hl]
  have htrace : trace (P * E) = P 0 0 := by
    rw [hPE]
    simp [Matrix.trace]
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ ↦ M i j) (hP.2.2.2 E)
  rw [htrace, hPE] at h
  simpa [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] using h

private theorem flat_rankOne_projector_has_canonical_dephased_lift
    (P : Matrix (Fin 6) (Fin 6) ℂ)
    (hP : IsNormalizedRankOneProjection P)
    (hdiag : ∀ i, P i i = (1 / 6 : ℂ)) :
    let u : Fin 6 → ℂ := fun i ↦ 6 * P i 0
    u 0 = 1 ∧ (∀ i, Complex.normSq (u i) = 1) ∧
      ∀ i j, P i j = (u i * star (u j)) / 6 := by
  let u : Fin 6 → ℂ := fun i ↦ 6 * P i 0
  have hrow (j : Fin 6) : P 0 j = star (P j 0) := by
    simpa only [Matrix.conjTranspose_apply] using
      (congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ ↦ M 0 j) hP.1).symm
  have hrec (i j : Fin 6) : P i j = 6 * (P i 0 * P 0 j) := by
    have h := coordinate_compression P hP i j
    rw [hdiag 0] at h
    linear_combination -6 * h
  change u 0 = 1 ∧ (∀ i, Complex.normSq (u i) = 1) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · dsimp [u]
    rw [hdiag]
    norm_num
  · intro i
    have hprod : u i * star (u i) = 1 := by
      dsimp [u]
      simp only [map_mul, star_ofNat]
      rw [← hrow i]
      have h := coordinate_compression P hP i i
      rw [hdiag 0, hdiag i] at h
      linear_combination 36 * h
    have hcast : (Complex.normSq (u i) : ℂ) = 1 := by
      simpa only [Complex.star_def, Complex.mul_conj] using hprod
    exact_mod_cast hcast
  · intro i j
    dsimp [u]
    simp only [map_mul, star_ofNat]
    rw [← hrow j, hrec i j]
    ring

/-- An actual flat rank-one projector satisfying the second-basis diagonal
constraints determines a root of the unnormalized common-unbiased equations.
Its first-column lift is canonical and reconstructs the whole projector. -/
theorem flat_rankOne_projector_has_canonical_dephased_root
    (P H : Matrix (Fin 6) (Fin 6) ℂ)
    (hP : IsNormalizedRankOneProjection P)
    (hdiag : ∀ i, P i i = (1 / 6 : ℂ))
    (hsecond : ∀ a, (Hᴴ * P * H) a a = 1) :
    let u : Fin 6 → ℂ := fun i ↦ 6 * P i 0
    u 0 = 1 ∧ (∀ i, Complex.normSq (u i) = 1) ∧
      (∀ a, Complex.normSq ((Hᴴ *ᵥ u) a) = 6) ∧
      ∀ i j, P i j = (u i * star (u j)) / 6 := by
  let u : Fin 6 → ℂ := fun i ↦ 6 * P i 0
  obtain ⟨hu0, hunorm, hrec⟩ :=
    flat_rankOne_projector_has_canonical_dephased_lift P hP hdiag
  change u 0 = 1 ∧ (∀ i, Complex.normSq (u i) = 1) ∧ _
  refine ⟨hu0, hunorm, ?_, hrec⟩
  intro a
  have hentry : (Hᴴ * P * H) a a =
      ((Hᴴ *ᵥ u) a * star ((Hᴴ *ᵥ u) a)) / 6 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec,
      dotProduct, hrec, map_sum, map_mul, star_star,
      Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsecond] at hentry
  have hprod : (Hᴴ *ᵥ u) a * star ((Hᴴ *ᵥ u) a) = 6 := by
    linear_combination -6 * hentry
  have hcast : (Complex.normSq ((Hᴴ *ᵥ u) a) : ℂ) = 6 := by
    simpa only [Complex.star_def, Complex.mul_conj] using hprod
  exact_mod_cast hcast

#print axioms flat_rankOne_projector_has_canonical_dephased_root

end D5.S3.Quantum.Tomography.FlatProjectorDephasing
