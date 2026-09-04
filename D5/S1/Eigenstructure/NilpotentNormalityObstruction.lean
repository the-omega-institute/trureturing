/- GID: D5/S1/Eigenstructure/NilpotentNormalityObstruction
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/NilpotentNormalityObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonzero nilpotent perturbation of a scalar cannot be normal or self-adjoint. -/

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum

/- Library-search audit trail (2026-09-04):
   * Exact, symbolic, digestion-ledger, generalized-owner, and in-flight searches
     found no existing theorem for the normality obstruction of a nonzero
     nilpotent scalar shift. The nearby Jordan-profile and kernel-tower modules
     prove different coordinate and recovery statements.
   * Pinned Mathlib has no packaged `normal + nilpotent = zero` declaration.
     The proof below directly uses `spectralRadius_pow_le`,
     `IsStarNormal.spectralRadius_eq_nnnorm`, and
     `Commute.isStarNormal_sub`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Eigenstructure.NilpotentNormalityObstruction

/-- A normal nilpotent element of a complex C-star algebra is zero. -/
lemma isStarNormal_nilpotent_eq_zero {A : Type*} [CStarAlgebra A]
    (N : A) (hNilpotent : IsNilpotent N) (hNormal : IsStarNormal N) : N = 0 := by
  letI : IsStarNormal N := hNormal
  obtain ⟨n, hn⟩ := hNilpotent
  by_cases hnZero : n = 0
  · subst n
    have hOne : (1 : A) = 0 := by
      simpa using hn
    calc
      N = N * 1 := by simp
      _ = N * 0 := by rw [hOne]
      _ = 0 := by simp
  · have hRadiusPow : spectralRadius ℂ N ^ n = 0 := by
      apply bot_unique
      simpa [hn] using spectrum.spectralRadius_pow_le (𝕜 := ℂ) N n hnZero
    have hRadius : spectralRadius ℂ N = 0 :=
      eq_zero_of_pow_eq_zero hRadiusPow
    have hNormCoe : (‖N‖₊ : ENNReal) = 0 := by
      rw [← IsStarNormal.spectralRadius_eq_nnnorm N]
      exact hRadius
    have hNorm : ‖N‖₊ = 0 := ENNReal.coe_eq_zero.mp hNormCoe
    exact nnnorm_eq_zero.mp hNorm

/-- If `N` is nonzero and nilpotent, then the scalar shift `lambda * 1 + N`
cannot be normal, and therefore cannot be self-adjoint. The ambient C-star
algebra may in particular be the bounded operators for any chosen Hilbert
space inner product. -/
theorem nonzero_nilpotent_shift_not_normal {A : Type*} [CStarAlgebra A]
    (lambda : ℂ) (N : A) (hNilpotent : IsNilpotent N) (hN : N ≠ 0) :
    ¬ IsStarNormal (lambda • (1 : A) + N) ∧
      ¬ IsSelfAdjoint (lambda • (1 : A) + N) := by
  have hNotNormal : ¬ IsStarNormal (lambda • (1 : A) + N) := by
    intro hShiftNormal
    let scalar : A := lambda • (1 : A)
    letI : IsStarNormal (lambda • (1 : A) + N) := hShiftNormal
    letI : IsStarNormal scalar := by
      dsimp only [scalar]
      infer_instance
    have hCommute : Commute (lambda • (1 : A) + N) (star scalar) := by
      simpa only [scalar, star_smul, star_one] using
        (Commute.one_right (lambda • (1 : A) + N)).smul_right (star lambda)
    have hDifferenceNormal :
        IsStarNormal ((lambda • (1 : A) + N) - scalar) :=
      hCommute.isStarNormal_sub
    have hDifference : (lambda • (1 : A) + N) - scalar = N := by
      dsimp only [scalar]
      abel
    rw [hDifference] at hDifferenceNormal
    exact hN (isStarNormal_nilpotent_eq_zero N hNilpotent hDifferenceNormal)
  exact ⟨hNotNormal, fun hSelfAdjoint => hNotNormal hSelfAdjoint.isStarNormal⟩

#print axioms nonzero_nilpotent_shift_not_normal

end D5.S1.Eigenstructure.NilpotentNormalityObstruction
