/- GID: D5/S3/Quantum/StaticExchange/DipoleTwoDistance
   generality: G
   mirror-B: D5/B/S3/Quantum/StaticExchange/DipoleTwoDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.MeanValue]
   utility: none
   digest: Two positive distances separate two dipole spectral responses. -/

module
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Strict separation of scaled static dipole profiles. -/

@[expose] public section
namespace D5.S3.Quantum.StaticExchange.DipoleTwoDistance

open Real Finset Set
noncomputable section

/-- The normalized radial dipole profile, equal to one at zero. -/
def profile (s : ℝ) : ℝ := (1 + s + s ^ 2 / 3) * exp (-s)

private theorem profile_pos {s : ℝ} (hs : 0 ≤ s) : 0 < profile s := by
  unfold profile
  positivity

private theorem profile_scaled_deriv (t a : ℝ) :
    HasDerivAt (fun z => profile (z * a))
      (-(a * (t * a) * (1 + t * a) / 3) * exp (-(t * a))) t := by
  have d := (hasDerivAt_id t).mul_const a
  have poly := ((hasDerivAt_const t (1 : ℝ)).add d).add ((d.pow 2).div_const 3)
  convert poly.mul d.neg.exp using 1
  · rfl
  · simp
    ring

/-- The two-by-two minor is strictly negative for strictly increasing positive
distances and positive scales. -/
theorem profile_minor {x y a b : ℝ} (hx : 0 < x) (hxy : x < y)
    (ha : 0 < a) (hab : a < b) :
    profile (x * a) * profile (y * b) < profile (x * b) * profile (y * a) := by
  have hb := lt_trans ha hab
  let f := fun t => profile (t * b) / profile (t * a)
  have hd (t : ℝ) (ht : 0 < t) :=
    (profile_scaled_deriv t b).div (profile_scaled_deriv t a)
      (profile_pos (mul_pos ht ha).le).ne'
  have hanti : StrictAntiOn f (Ioi 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi _)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      change 0 < t at ht
      rw [show deriv f t = _ from (hd t ht).deriv]
      apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (profile_pos (mul_pos ht ha).le))
      have hpoly : 0 < t * (b - a) *
          ((a * b * t) ^ 2 * t + 3 * a * b * (a + b) * t ^ 2 +
            3 * (a + b) ^ 2 * t + 3 * (a + b)) := by
        have : 0 < b - a := sub_pos.mpr hab
        positivity
      unfold profile
      have hfactor : (-(b * (t * b) * (1 + t * b) / 3) * exp (-(t * b))) *
          ((1 + t * a + (t * a) ^ 2 / 3) * exp (-(t * a))) -
          ((1 + t * b + (t * b) ^ 2 / 3) * exp (-(t * b))) *
          (-(a * (t * a) * (1 + t * a) / 3) * exp (-(t * a))) =
          -(t * (b - a) * ((a * b * t) ^ 2 * t + 3 * a * b * (a + b) * t ^ 2 +
              3 * (a + b) ^ 2 * t + 3 * (a + b))) * exp (-(t * b)) * exp (-(t * a)) / 9 := by
        ring
      rw [hfactor]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hpoly) (exp_pos _))
          (exp_pos _)) (by norm_num)
  have hrat := hanti hx (lt_trans hx hxy) hxy
  have h := (div_lt_div_iff₀ (profile_pos (mul_pos (lt_trans hx hxy) ha).le)
    (profile_pos (mul_pos hx ha).le)).mp hrat
  simpa only [mul_comm] using h

end
end D5.S3.Quantum.StaticExchange.DipoleTwoDistance
