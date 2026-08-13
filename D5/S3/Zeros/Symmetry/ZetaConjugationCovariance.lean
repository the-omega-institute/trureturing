/- GID: D5/S3/Zeros/Symmetry/ZetaConjugationCovariance
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/ZetaConjugationCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Riemann zeta and its completed reading commute with complex conjugation. -/

/- Library-search audit trail (2026-08-14):
   * Searches for `riemannZeta_conj`, `conj.*riemannZeta`,
     `completedRiemannZeta.*conj`, and the corresponding Hurwitz-zeta shapes
     found no exact theorem in pinned Mathlib or D5.
   * Exact pinned-mathlib dependency hits: `Complex.Gamma_conj`,
     `Complex.conj_cpow`, `MeasureTheory.integral_conj`,
     `completedRiemannZeta_eq`, and `riemannZeta_def_of_ne_zero`.
   * Exact frozen D5 dependency hit: `xi_reading_reflection` supplies the
     entire completed reading's reflection symmetry.
-/

import D5.S3.Zeros.CompletedZeta
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace D5.S3.Zeros.Symmetry.ZetaConjugationCovariance

open Complex MeasureTheory Set
open D5.S3.Zeros.CompletedZeta
open scoped ComplexConjugate

private theorem mellin_conj_of_real (f : ℝ → ℂ)
    (hf : ∀ t, conj (f t) = f t) (s : ℂ) :
    mellin f (conj s) = conj (mellin f s) := by
  rw [mellin, mellin, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [smul_eq_mul, map_mul]
  rw [hf]
  have htarg : ((t : ℂ).arg) ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg ht.le]
    exact ne_of_lt Real.pi_pos
  rw [show conj s - 1 = conj (s - 1) by simp,
    cpow_conj (t : ℂ) (s - 1) htarg]
  simp

private theorem completed_riemann_zeta_zero_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  rw [completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀]
  unfold WeakFEPair.Λ₀
  rw [show conj s / 2 = conj (s / 2) by
        simp only [map_div₀, map_ofNat],
    mellin_conj_of_real]
  · change conj _ / 2 = conj (_ / 2)
    simp only [map_div₀, map_ofNat]
    rfl
  · intro t
    simp only [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
      Function.comp_apply, smul_eq_mul, one_mul]
    by_cases htTop : t ∈ Ioi (1 : ℝ) <;>
      by_cases htBottom : t ∈ Ioo (0 : ℝ) 1 <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, htTop, htBottom]

private theorem gamma_real_conj (s : ℂ) :
    Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul]
  have hhalf : conj s / 2 = conj (s / 2) := by
    simp only [map_div₀, map_ofNat]
  rw [hhalf, Gamma_conj]
  have hpiarg : ((Real.pi : ℂ).arg) ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg Real.pi_pos.le]
    exact ne_of_lt Real.pi_pos
  rw [show -(conj s) / 2 = conj (-s / 2) by
        simp only [map_div₀, map_neg, map_ofNat],
    cpow_conj (Real.pi : ℂ) (-s / 2) hpiarg]
  simp

/-- The completed Riemann zeta function commutes with complex conjugation. -/
theorem completed_riemann_zeta_conj (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq,
    completed_riemann_zeta_zero_conj]
  simp

/-- Reflection and conjugation combine to give the completed Riemann zeta
function's antiunitary covariance. -/
theorem completed_riemann_zeta_one_sub_conj (s : ℂ) :
    completedRiemannZeta (1 - conj s) = conj (completedRiemannZeta s) := by
  rw [completedRiemannZeta_one_sub, completed_riemann_zeta_conj]

/-- The Riemann zeta function commutes with complex conjugation on all of `ℂ`. -/
theorem riemann_zeta_conj (s : ℂ) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [show conj (0 : ℂ) = 0 by simp, riemannZeta_zero]
    simp only [map_neg, map_one, map_div₀, map_ofNat]
  · have hconj : conj s ≠ 0 := by simpa using hs
    rw [riemannZeta_def_of_ne_zero hconj, riemannZeta_def_of_ne_zero hs,
      completed_riemann_zeta_conj, gamma_real_conj]
    simp

/-- The entire xi reading commutes with complex conjugation. -/
theorem xi_reading_conj (s : ℂ) :
    xiReading (conj s) = conj (xiReading s) := by
  unfold xiReading
  rw [completed_riemann_zeta_zero_conj]
  simp only [map_mul, map_add, map_sub, map_one, map_div₀, map_ofNat]

/-- The entire xi reading satisfies the same antiunitary covariance. -/
theorem xi_reading_one_sub_conj (s : ℂ) :
    xiReading (1 - conj s) = conj (xiReading s) := by
  rw [xi_reading_reflection, xi_reading_conj]

/-- The complex parameter domain is inhabited. -/
example : Nonempty ℂ := ⟨0⟩

end D5.S3.Zeros.Symmetry.ZetaConjugationCovariance
