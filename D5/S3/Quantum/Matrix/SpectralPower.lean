/- GID: D5/S3/Quantum/Matrix/SpectralPower
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/SpectralPower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Real spectral powers, Log-Euclidean means and two-dimensional positivity. -/

import D5.S3.Quantum.FiniteDimensional
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.SpectralPower
open D5.S3.Quantum.FiniteDimensional (QubitMatrix)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real matrix power through the continuous functional calculus. -/
noncomputable def mpow (X : Matrix n n ℂ) (p : ℝ) : Matrix n n ℂ := cfc (fun t : ℝ => t ^ p) X

/-- The Log-Euclidean mean `LEα(A,B) = exp((1 - α) log A + α log B)`. -/
noncomputable def LE (α : ℝ) (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc Real.exp ((1 - α) • cfc Real.log A + α • cfc Real.log B)

lemma mpow_one {X : Matrix n n ℂ} (hX : X.IsHermitian) : mpow X 1 = X := by
  simpa [mpow, Real.rpow_one] using cfc_id' ℝ X hX.isSelfAdjoint

lemma mpow_two {X : Matrix n n ℂ} (hX : X.IsHermitian) : mpow X 2 = X * X := by
  simp only [mpow, Real.rpow_two]
  rw [cfc_pow_id X 2 hX.isSelfAdjoint, pow_two]

lemma posDef_two (a b c : ℝ) (ha : 0 < a) (hd : 0 < a * c - b ^ 2) :
    (!![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)] : QubitMatrix).PosDef := by
  let U : QubitMatrix := !![1, 0; (b / a : ℝ), 1]
  let D : QubitMatrix := Matrix.diagonal ![(a : ℂ), ((c - b ^ 2 / a : ℝ) : ℂ)]
  have hD : D.PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    fin_cases i
    · change (0 : ℂ) < (a : ℂ)
      exact_mod_cast ha
    · have : 0 < c - b ^ 2 / a := by
        apply (sub_pos.mpr ((div_lt_iff₀ ha).mpr ?_))
        nlinarith
      change (0 : ℂ) < ((c - b ^ 2 / a : ℝ) : ℂ)
      exact_mod_cast this
  have hU : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    norm_num [U, Matrix.det_fin_two]
  have heq : U * D * star U = !![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)] := by
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, D, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, Matrix.star_apply,
        Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_pow] <;>
      field_simp <;> ring
  rw [← heq]
  exact hU.posDef_star_right_conjugate_iff.mpr hD

end D5.S3.Quantum.Matrix.SpectralPower
