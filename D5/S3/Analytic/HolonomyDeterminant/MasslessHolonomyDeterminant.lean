/- GID: D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant
   generality: G
   mirror-B: D5/B/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Lerch data give a sine chord; endpoints fail and zero values are insufficient. -/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * D5 searches by object name, conventional name, digest, neighboring declarations,
     generalized shape, and alternate vocabulary found no holonomy determinant owner.
   * Pinned Mathlib provides `HurwitzZeta.hurwitzZetaEven_eq`,
     `HurwitzZeta.hurwitzZetaEven_apply_zero`, and
     `Real.Gamma_mul_Gamma_one_sub`; all are used below.
   * Pinned source and local smart-search queries `deriv_hurwitz` and
     `deriv (hurwitzZeta a) 0` found no Hurwitz derivative-at-zero formula.
     `HurwitzZetaValues.lean` explicitly leaves the `s = 0` case unproved.
   * NyxID service discovery found no Loogle or LeanSearch endpoint, so those services
     were unavailable and are not counted as negative searches.
   * `ModFiveObserverDiagonalization` owns specialized residue channels, while
     `ObserverScaleDivisorNonidentifiability` owns a scaled Riemann-zeta function;
     neither defines the reflected Hurwitz sum or its zeta determinant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.HolonomyDeterminant.MasslessHolonomyDeterminant

open Complex HurwitzZeta Set

noncomputable section

/-- Reflection of a real holonomy parameter in Mathlib's periodic additive circle. -/
def reflectedHolonomy (alpha : Real) : UnitAddCircle :=
  -((alpha : Real) : UnitAddCircle)

/-- The sum of the Hurwitz zeta functions in two reflected holonomy sectors. -/
noncomputable def holonomyHurwitzSum (alpha : Real) (s : Complex) : Complex :=
  hurwitzZeta (alpha : UnitAddCircle) s + hurwitzZeta (reflectedHolonomy alpha) s

/-- Zeta regularization assigns `exp (-Z'(0))` to a spectral zeta function `Z`. -/
noncomputable def zetaRegularizedDeterminant (Z : Complex -> Complex) : Complex :=
  Complex.exp (-deriv Z 0)

/-- The zeta-regularized determinant of the reflected massless holonomy spectrum. -/
noncomputable def masslessHolonomyDeterminant (alpha : Real) : Complex :=
  zetaRegularizedDeterminant (holonomyHurwitzSum alpha)

/-- Chord length from one to the unit-circle point with holonomy `alpha`. -/
noncomputable def holonomyChordLength (alpha : Real) : Real :=
  ‖Complex.exp (Complex.I * (2 * Real.pi * alpha : Real)) - 1‖

/-- Multiplication of a spectral zeta function by an overall real spectral scale. -/
noncomputable def scaledSpectralZeta
    (scale : Real) (Z : Complex -> Complex) (s : Complex) : Complex :=
  Complex.exp (-s * (Real.log scale : Complex)) * Z s

/-- The unavailable Lerch formula, recorded explicitly as a proof-interface predicate. -/
def HasReflectedHurwitzDerivativeAtZeroFormula (alpha : Real) : Prop :=
  deriv (hurwitzZeta (alpha : UnitAddCircle)) 0 =
      (Real.log (Real.Gamma alpha) - Real.log (2 * Real.pi) / 2 : Real) ∧
    deriv (hurwitzZeta (reflectedHolonomy alpha)) 0 =
      (Real.log (Real.Gamma (1 - alpha)) - Real.log (2 * Real.pi) / 2 : Real)

private lemma holonomy_parameter_ne_zero
    {alpha : Real} (hAlpha : alpha ∈ Ioo 0 1) :
    (alpha : UnitAddCircle) ≠ 0 := by
  rw [ne_eq, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hAlpha.1.le, hAlpha.2⟩]
  exact hAlpha.1.ne'

/-- The reflected Hurwitz sum vanishes at zero for every nontrivial holonomy parameter. -/
theorem holonomy_hurwitz_sum_at_zero
    (alpha : Real) (hAlpha : alpha ∈ Ioo 0 1) :
    holonomyHurwitzSum alpha 0 = 0 := by
  have hNonzero := holonomy_parameter_ne_zero hAlpha
  rw [holonomyHurwitzSum, reflectedHolonomy]
  calc
    hurwitzZeta (↑alpha) 0 + hurwitzZeta (-↑alpha) 0 =
        2 * hurwitzZetaEven (↑alpha) 0 := by
      rw [hurwitzZetaEven_eq]
      ring
    _ = 0 := by simp [hurwitzZetaEven_apply_zero, hNonzero]

#print axioms holonomy_hurwitz_sum_at_zero

private lemma hasDerivAt_scaleFactor (scale : Real) :
    HasDerivAt
      (fun s : Complex => Complex.exp (-s * (Real.log scale : Complex)))
      (-(Real.log scale : Complex)) 0 := by
  have hLinear : HasDerivAt
      (fun s : Complex => -s * (Real.log scale : Complex))
      (-(Real.log scale : Complex)) 0 := by
    simpa only [Pi.neg_apply, id_eq, neg_one_mul] using
      (hasDerivAt_id (𝕜 := Complex) (0 : Complex)).neg.mul_const
        (Real.log scale : Complex)
  simpa using hLinear.cexp

/-- An overall real scale parameter cancels because the zeta value is zero. -/
theorem holonomy_determinant_scale_invariant
    (alpha : Real) (hAlpha : alpha ∈ Ioo 0 1) (scale : Real) :
    zetaRegularizedDeterminant
        (scaledSpectralZeta scale (holonomyHurwitzSum alpha)) =
      masslessHolonomyDeterminant alpha := by
  have hZero := holonomy_hurwitz_sum_at_zero alpha hAlpha
  have hDifferentiable : DifferentiableAt Complex (holonomyHurwitzSum alpha) 0 := by
    exact (differentiableAt_hurwitzZeta _ (by norm_num)).add
      (differentiableAt_hurwitzZeta _ (by norm_num))
  have hProduct := (hasDerivAt_scaleFactor scale).mul hDifferentiable.hasDerivAt
  have hDerivative :
      deriv (scaledSpectralZeta scale (holonomyHurwitzSum alpha)) 0 =
        deriv (holonomyHurwitzSum alpha) 0 := by
    change deriv
      ((fun s : Complex => Complex.exp (-s * (Real.log scale : Complex))) *
        holonomyHurwitzSum alpha) 0 = deriv (holonomyHurwitzSum alpha) 0
    simpa [hZero] using hProduct.deriv
  simp only [zetaRegularizedDeterminant, masslessHolonomyDeterminant, hDerivative]

#print axioms holonomy_determinant_scale_invariant

private lemma reflected_gamma_log_identity
    (alpha : Real) (hAlpha : alpha ∈ Ioo 0 1) :
    Real.log (Real.Gamma alpha) + Real.log (Real.Gamma (1 - alpha)) -
        Real.log (2 * Real.pi) =
      -Real.log (2 * Real.sin (Real.pi * alpha)) := by
  have hOneSub : 0 < 1 - alpha := sub_pos.mpr hAlpha.2
  have hSin : 0 < Real.sin (Real.pi * alpha) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos hAlpha.1
    · simpa only [mul_one] using mul_lt_mul_of_pos_left hAlpha.2 Real.pi_pos
  have hReflection := Real.Gamma_mul_Gamma_one_sub alpha
  have hLogReflection := congrArg Real.log hReflection
  rw [Real.log_mul (Real.Gamma_pos_of_pos hAlpha.1).ne'
      (Real.Gamma_pos_of_pos hOneSub).ne',
    Real.log_div Real.pi_ne_zero hSin.ne'] at hLogReflection
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) Real.pi_ne_zero,
    Real.log_mul (by norm_num : (2 : Real) ≠ 0) hSin.ne']
  linarith

/-- Conditional closure of the missing Lerch input gives the massless holonomy determinant. -/
theorem massless_holonomy_determinant
    (alpha : Real) (hAlpha : alpha ∈ Ioo 0 1)
    (hLerch : HasReflectedHurwitzDerivativeAtZeroFormula alpha) :
    masslessHolonomyDeterminant alpha =
      (2 * Real.sin (Real.pi * alpha) : Real) := by
  have hDerivativeAdd :
      deriv (holonomyHurwitzSum alpha) 0 =
        deriv (hurwitzZeta (alpha : UnitAddCircle)) 0 +
          deriv (hurwitzZeta (reflectedHolonomy alpha)) 0 := by
    change deriv
      (fun s : Complex =>
        hurwitzZeta (↑alpha) s + hurwitzZeta (reflectedHolonomy alpha) s) 0 = _
    exact deriv_fun_add (differentiableAt_hurwitzZeta _ (by norm_num))
      (differentiableAt_hurwitzZeta _ (by norm_num))
  have hDerivative :
      deriv (holonomyHurwitzSum alpha) 0 =
        (Real.log (Real.Gamma alpha) + Real.log (Real.Gamma (1 - alpha)) -
          Real.log (2 * Real.pi) : Real) := by
    rw [hDerivativeAdd, hLerch.1, hLerch.2]
    push_cast
    ring
  have hSin : 0 < 2 * Real.sin (Real.pi * alpha) := by
    refine mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
    · exact mul_pos Real.pi_pos hAlpha.1
    · simpa only [mul_one] using mul_lt_mul_of_pos_left hAlpha.2 Real.pi_pos
  rw [masslessHolonomyDeterminant, zetaRegularizedDeterminant, hDerivative,
    reflected_gamma_log_identity alpha hAlpha]
  simp only [Complex.ofReal_neg, neg_neg]
  rw [← Complex.ofReal_exp, Real.exp_log hSin]

#print axioms massless_holonomy_determinant

/-- The sine determinant is the chord from one to the holonomy point on the unit circle. -/
theorem holonomy_sine_eq_chord_length
    (alpha : Real) (hAlpha : alpha ∈ Icc 0 1) :
    holonomyChordLength alpha = 2 * Real.sin (Real.pi * alpha) := by
  rw [holonomyChordLength, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hAngleNonneg : 0 ≤ Real.pi * alpha :=
    mul_nonneg Real.pi_pos.le hAlpha.1
  have hAngleLe : Real.pi * alpha ≤ Real.pi := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hAlpha.2 Real.pi_pos.le
  have hSinNonneg : 0 ≤ Real.sin (Real.pi * alpha) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hAngleNonneg hAngleLe
  rw [show (2 * Real.pi * alpha) / 2 = Real.pi * alpha by ring,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hSinNonneg)]

#print axioms holonomy_sine_eq_chord_length

/-- Points below zero and above one show that both chord-interval bounds are necessary. -/
theorem chord_interval_is_necessary :
    holonomyChordLength (-1 / 2) ≠ 2 * Real.sin (Real.pi * (-1 / 2)) ∧
      holonomyChordLength (3 / 2) ≠ 2 * Real.sin (Real.pi * (3 / 2)) := by
  constructor
  · rw [holonomyChordLength, Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * Real.pi * (-1 / 2)) / 2 = -(Real.pi / 2) by ring,
      show Real.pi * (-1 / 2) = -(Real.pi / 2) by ring,
      Real.sin_neg, Real.sin_pi_div_two, Real.norm_eq_abs]
    norm_num
  · rw [holonomyChordLength, Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * Real.pi * (3 / 2)) / 2 = Real.pi / 2 + Real.pi by ring,
      show Real.pi * (3 / 2) = Real.pi / 2 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_two, Real.norm_eq_abs]
    norm_num

#print axioms chord_interval_is_necessary

/-- Concrete endpoint witnesses show why the open holonomy interval cannot include its boundary. -/
theorem holonomy_interval_is_necessary :
    masslessHolonomyDeterminant 0 ≠
        (2 * Real.sin (Real.pi * 0) : Real) ∧
      masslessHolonomyDeterminant 1 ≠
        (2 * Real.sin (Real.pi * 1) : Real) := by
  constructor <;>
    simp only [masslessHolonomyDeterminant, zetaRegularizedDeterminant,
      mul_zero, mul_one, Real.sin_zero, Real.sin_pi, ofReal_zero]
  · exact Complex.exp_ne_zero _
  · exact Complex.exp_ne_zero _

#print axioms holonomy_interval_is_necessary

/-- A constant-zero mock zeta has value zero at zero but has the wrong determinant at one half. -/
theorem derivative_formula_is_necessary :
    let zeroZeta : Complex -> Complex := fun _ => 0
    zeroZeta 0 = 0 ∧
      zetaRegularizedDeterminant zeroZeta ≠
        (2 * Real.sin (Real.pi * (1 / 2 : Real)) : Real) := by
  rw [show Real.pi * (1 / 2 : Real) = Real.pi / 2 by ring,
    Real.sin_pi_div_two]
  norm_num [zetaRegularizedDeterminant]

#print axioms derivative_formula_is_necessary

end

end D5.S3.Analytic.HolonomyDeterminant.MasslessHolonomyDeterminant
