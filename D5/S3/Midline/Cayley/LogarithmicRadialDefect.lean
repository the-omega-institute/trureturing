/- GID: D5/S3/Midline/Cayley/LogarithmicRadialDefect
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/LogarithmicRadialDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relate the logarithmic Cayley radius to the midline and conjugate reflection. -/

/- Library-search audit trail (2026-08-22):
   * The repository supplies `ZeroData`, `cayleyCoefficient`, `AllZerosOnMidline`,
     `cayley_unitarity_defect_formula`, and the canonical `mirror` operation.
   * Pinned Mathlib supplies the exact identities `Real.log_pow`, `Real.log_inv`,
     `norm_div`, `norm_inv`, and `Complex.norm_conj` used below.
   * Repository and pinned-Mathlib searches found no packaged theorem combining the
     logarithmic radius formula, the global midline criterion, and mirror reversal.
-/

import D5.S3.Midline.Cayley.CayleyUnitarityDefect
import D5.S3.Weil.ReflectionLedger

namespace D5.S3.Midline.Cayley.LogarithmicRadialDefect

open D5.S3.Midline.Cayley.CayleyUnitarityDefect
open D5.S3.Weil.ReflectionLedger D5.S3.Weil.ZeroSum
open scoped ComplexConjugate

/-- The logarithm of the norm of the canonical Cayley coefficient. -/
noncomputable def logarithmicRadialDefect (rho : Complex) : Real :=
  Real.log ‖cayleyCoefficient rho‖

private theorem zero_ne_zero (Z : ZeroData) (n : Nat) : Z.zero n ≠ 0 := by
  intro hzero
  have hpositive := (Z.zero_isNontrivial n).2.1
  rw [hzero] at hpositive
  norm_num at hpositive

private theorem zero_ne_one (Z : ZeroData) (n : Nat) : Z.zero n ≠ 1 := by
  intro hone
  have hless := (Z.zero_isNontrivial n).2.2
  rw [hone] at hless
  norm_num at hless

private theorem coefficient_ne_zero (Z : ZeroData) (n : Nat) :
    cayleyCoefficient (Z.zero n) ≠ 0 := by
  rw [cayleyCoefficient]
  exact div_ne_zero (sub_ne_zero.mpr (zero_ne_one Z n)) (zero_ne_zero Z n)

private theorem logarithmic_radial_formula (rho : Complex) :
    logarithmicRadialDefect rho =
      (1 / 2 : Real) * Real.log (‖rho - 1‖ ^ 2 / ‖rho‖ ^ 2) := by
  rw [logarithmicRadialDefect, cayleyCoefficient, norm_div, ← div_pow,
    Real.log_pow]
  ring

private theorem mirror_coefficient_norm (rho : Complex) :
    ‖cayleyCoefficient (mirror rho)‖ = ‖cayleyCoefficient rho‖⁻¹ := by
  have hdenominator : ‖1 - conj rho‖ = ‖rho - 1‖ := by
    calc
      ‖1 - conj rho‖ = ‖-conj (rho - 1)‖ := by simp
      _ = ‖rho - 1‖ := by rw [norm_neg, Complex.norm_conj]
  simp [cayleyCoefficient, mirror, reflection, hdenominator]

/--
The logarithmic Cayley radius has the squared-modulus formula, vanishes on
every source zero exactly when all source zeros lie on the midline, and is
negated by conjugate reflection through reciprocal Cayley norm.
-/
theorem logarithmic_radial_defect_and_mirror (Z : ZeroData) :
    (∀ n, logarithmicRadialDefect (Z.zero n) =
      (1 / 2 : Real) * Real.log
        (‖Z.zero n - 1‖ ^ 2 / ‖Z.zero n‖ ^ 2)) ∧
    (AllZerosOnMidline Z ↔
      ∀ n, logarithmicRadialDefect (Z.zero n) = 0) ∧
    (∀ n, ‖cayleyCoefficient (mirror (Z.zero n))‖ =
      ‖cayleyCoefficient (Z.zero n)‖⁻¹) ∧
    (∀ n, logarithmicRadialDefect (mirror (Z.zero n)) =
      -logarithmicRadialDefect (Z.zero n)) := by
  have hmidline :
      AllZerosOnMidline Z ↔ ∀ n, ‖cayleyCoefficient (Z.zero n)‖ = 1 :=
    (cayley_unitarity_defect_formula Z).2.1
  refine ⟨fun n => logarithmic_radial_formula (Z.zero n), ?_,
    fun n => mirror_coefficient_norm (Z.zero n), ?_⟩
  · constructor
    · intro h n
      rw [logarithmicRadialDefect, (hmidline.mp h) n, Real.log_one]
    · intro h
      apply hmidline.mpr
      intro n
      have hpositive : 0 < ‖cayleyCoefficient (Z.zero n)‖ :=
        norm_pos_iff.mpr (coefficient_ne_zero Z n)
      calc
        ‖cayleyCoefficient (Z.zero n)‖ =
            Real.exp (Real.log ‖cayleyCoefficient (Z.zero n)‖) :=
          (Real.exp_log hpositive).symm
        _ = 1 := by rw [← logarithmicRadialDefect, h n, Real.exp_zero]
  · intro n
    change Real.log ‖cayleyCoefficient (mirror (Z.zero n))‖ =
      -Real.log ‖cayleyCoefficient (Z.zero n)‖
    rw [mirror_coefficient_norm, Real.log_inv]

#print axioms logarithmic_radial_defect_and_mirror

end D5.S3.Midline.Cayley.LogarithmicRadialDefect
