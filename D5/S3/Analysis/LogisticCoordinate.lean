/- GID: D5/S3/Analysis/LogisticCoordinate
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-de-sitter-kernel-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Change of variables and the logarithmic separation formula for the logistic coordinate on the open unit interval. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
Omega original.

Change of variables and the logarithmic separation formula for the logistic
coordinate on the open unit interval.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace Omega

/-- The logistic map at a fixed radial rate. -/
def logistic (b s : ℝ) : ℝ := Real.sigmoid (b * s)

theorem logistic_eq_exp (b s : ℝ) :
    logistic b s = Real.exp (b * s) / (1 + Real.exp (b * s)) := by
  unfold logistic Real.sigmoid
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero (b * s), show 1 + Real.exp (b * s) ≠ 0 by positivity]
  ring

theorem hasDerivAt_logistic (b s : ℝ) :
    HasDerivAt (logistic b) (b * (logistic b s * (1 - logistic b s))) s := by
  have h : HasDerivAt (fun x : ℝ => b * x) b s := by
    simpa using (hasDerivAt_id s).const_mul b
  have hd := (Real.hasDerivAt_sigmoid (b * s)).comp s h
  convert hd using 1
  · rfl
  · unfold logistic
    ring

theorem strictMono_logistic {b : ℝ} (hb : 0 < b) : StrictMono (logistic b) :=
  fun _ _ h => Real.sigmoid_strictMono (mul_lt_mul_of_pos_left h hb)

theorem range_logistic {b : ℝ} (hb : 0 < b) : range (logistic b) = Ioo 0 1 := by
  change range (Real.sigmoid ∘ fun x : ℝ => b * x) = _
  have hs : Function.Surjective (fun x : ℝ => b * x) :=
    fun y => ⟨y / b, by field_simp [hb.ne']⟩
  rw [range_comp, hs.range_eq, image_univ, Real.range_sigmoid]

/-- The Jacobian transports a radial integral on the open unit interval. -/
theorem integral_logistic_substitution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b : ℝ} (hb : 0 < b) (g : ℝ → E) :
    (∫ u in Ioo (0 : ℝ) 1, g u) =
      ∫ s : ℝ, (b * (logistic b s * (1 - logistic b s))) • g (logistic b s) := by
  rw [← range_logistic hb, ← image_univ]
  simpa only [Measure.restrict_univ] using
    integral_image_eq_integral_deriv_smul_of_monotoneOn (f := logistic b)
      (f' := fun s => b * (logistic b s * (1 - logistic b s)))
      MeasurableSet.univ (fun s _ => (hasDerivAt_logistic b s).hasDerivWithinAt)
      ((strictMono_logistic hb).monotone.monotoneOn univ) g

/-- Logarithmic separation in the affine variable differs from the hyperbolic
logarithm by terms in the individual modular coordinates. -/
theorem log_logistic_sub {b r s : ℝ} (hb : 0 < b) (hrs : r ≠ s) :
    Real.log |logistic b r - logistic b s| =
      b / 2 * (r + s) + Real.log (2 * |Real.sinh (b / 2 * (r - s))|) -
        Real.log (1 + Real.exp (b * r)) - Real.log (1 + Real.exp (b * s)) := by
  let p := Real.exp (b * r)
  let q := Real.exp (b * s)
  have hp : 0 < p := Real.exp_pos _
  have hq : 0 < q := Real.exp_pos _
  have he : logistic b r - logistic b s = (p - q) / ((1 + p) * (1 + q)) := by
    rw [logistic_eq_exp, logistic_eq_exp]
    change p / (1 + p) - q / (1 + q) = _
    field_simp
    ring
  have hh : p - q =
      Real.exp (b / 2 * (r + s)) * (2 * Real.sinh (b / 2 * (r - s))) := by
    simp only [p, q, Real.sinh_eq]
    rw [show ∀ x y z : ℝ, x * (2 * ((y - z) / 2)) = x * y - x * z by intros; ring]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 2 <;> ring
  have hs : Real.sinh (b / 2 * (r - s)) ≠ 0 := by
    exact Real.sinh_ne_zero.mpr (mul_ne_zero (by positivity) (sub_ne_zero.mpr hrs))
  rw [he, hh, abs_div, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (show (0 : ℝ) < 2 by norm_num),
    abs_of_pos (by positivity : 0 < (1 + p) * (1 + q)),
    Real.log_div (by positivity) (by positivity), Real.log_mul (Real.exp_ne_zero _)
      (mul_ne_zero (by norm_num) (abs_ne_zero.mpr hs)),
    Real.log_exp]
  rw [Real.log_mul (show 1 + p ≠ 0 by positivity) (show 1 + q ≠ 0 by positivity)]
  dsimp [p, q]
  ring

/-- The complex logistic expression and its Jacobian on the real line. -/
theorem logistic_complex_coordinates (s : ℝ) :
    (Complex.exp (2 * Real.pi * (s : ℂ)) /
      (1 + Complex.exp (2 * Real.pi * (s : ℂ)))).re = logistic (2 * Real.pi) s ∧
      (2 * Real.pi * Complex.exp (2 * Real.pi * (s : ℂ))) /
        (1 + Complex.exp (2 * Real.pi * (s : ℂ))) ^ 2 =
        ((2 * Real.pi * (logistic (2 * Real.pi) s *
          (1 - logistic (2 * Real.pi) s)) : ℝ) : ℂ) := by
  have he : Complex.exp (2 * Real.pi * (s : ℂ)) =
      (Real.exp (2 * Real.pi * s) : ℂ) := by rw [Complex.ofReal_exp]; push_cast; rfl
  rw [he, logistic_eq_exp]
  constructor
  · rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re]
  · simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_ofNat]
    have hn : (1 + (Real.exp (2 * Real.pi * s) : ℂ)) ≠ 0 := by
      exact_mod_cast (show 1 + Real.exp (2 * Real.pi * s) ≠ 0 by positivity)
    generalize Real.exp (2 * Real.pi * s) = E at hn ⊢
    field_simp [hn]
    ring

end Omega

