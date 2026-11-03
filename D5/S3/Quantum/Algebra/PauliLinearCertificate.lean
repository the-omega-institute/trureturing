/- GID: D5/S3/Quantum/Algebra/PauliLinearCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PauliLinearCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: A quantitative strict comparison of the linear and quadratic root certificates. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
namespace D5.S3.Quantum.Algebra.PauliLinearCertificate

/-- The source constant for unit spin products. -/
def constant : ℝ := 1 + 2 * Real.sqrt 2
/-- The linear certificate with the original denominator. -/
def linear (eps d : ℝ) : ℝ :=
  2 * constant * d * eps / (Real.sqrt 2 - 2 * constant * eps)
/-- The original quadratic root, including its independent cap. -/
def old (eps d : ℝ) : ℝ :=
  min d ((constant * eps + Real.sqrt (constant^2*eps^2+4*constant*d*eps))/2)

private theorem sqrt_two : 1 ≤ Real.sqrt 2 ∧ (Real.sqrt 2)^2 = 2 := by
  constructor
  · exact Real.one_le_sqrt.mpr (by norm_num)
  · exact Real.sq_sqrt (by norm_num)

private theorem constant_pos : 0 < constant := by
  unfold constant
  positivity

/-- The strict comparison uses the original cap and is uniform over the stated d range. -/
theorem strict_comparison (eps d : ℝ) (heps : 0 < eps)
    (hsmall : eps < 1 / (16 * constant)) (hd : 1 ≤ d) (hdtop : d ≤ Real.sqrt 2) :
    0 < Real.sqrt 2 - 2 * constant * eps ∧
    linear eps d < old eps d := by
  have hc := constant_pos
  have hs := sqrt_two
  have hx : 0 < constant * eps := mul_pos hc heps
  have hxsmall : constant * eps < 1/16 := by
    have hh := (lt_div_iff₀ (show 0 < 16*constant by positivity)).mp hsmall
    nlinarith
  have hden : 0 < Real.sqrt 2 - 2*constant*eps := by nlinarith [hs.1]
  have hlin : linear eps d ≤ 4*(constant*eps) := by
    unfold linear
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (le_of_lt hx) (sub_nonneg.mpr hdtop)]
  have hxroot : 4*(constant*eps) < Real.sqrt (constant*eps) := by
    have hsq := Real.sq_sqrt (le_of_lt hx)
    have hnonneg := Real.sqrt_nonneg (constant*eps)
    nlinarith
  have hroot : Real.sqrt (constant*eps) ≤
      (constant*eps + Real.sqrt (constant^2*eps^2+4*constant*d*eps))/2 := by
    have hr : 0 ≤ constant^2*eps^2+4*constant*d*eps := by positivity
    have hsqr := Real.sq_sqrt hr
    have hsr := Real.sq_sqrt (le_of_lt hx)
    have hn := Real.sqrt_nonneg (constant^2*eps^2+4*constant*d*eps)
    have hn' := Real.sqrt_nonneg (constant*eps)
    have hmul : constant*eps ≤ constant*d*eps := by nlinarith
    have : 2*Real.sqrt (constant*eps) ≤
        Real.sqrt (constant^2*eps^2+4*constant*d*eps) := by nlinarith [sq_nonneg (constant*eps)]
    linarith
  refine ⟨hden, lt_min ?_ ?_⟩
  · have : linear eps d < 1 := by linarith
    linarith
  · exact lt_of_le_of_lt hlin (lt_of_lt_of_le hxroot hroot)

end D5.S3.Quantum.Algebra.PauliLinearCertificate
