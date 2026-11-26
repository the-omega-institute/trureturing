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
import Mathlib.Tactic.LinearCombination
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

/-- The weighted response of spectral order k at a positive or zero distance. -/
def moment {n : ℕ} (p g : Fin n → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ i, p i * g i ^ k * profile (t * g i)

/-- Two distances identify two linear response coefficients when the finite positive-scale
spectrum has nonnegative weights and at least two different scales with positive weight. -/
theorem finite_spectral_separation {n : ℕ} (p g : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hg : ∀ i, 0 < g i) (support : ∃ i j, 0 < p i ∧ 0 < p j ∧ g i < g j)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    moment p g 2 x * moment p g 4 y < moment p g 4 x * moment p g 2 y ∧
    Function.Injective (fun c : ℝ × ℝ =>
      (c.1 * moment p g 2 x + c.2 * moment p g 4 x,
       c.1 * moment p g 2 y + c.2 * moment p g 4 y)) := by
  let w := fun i => p i * g i ^ 2
  let h := fun t i => w i * profile (t * g i)
  let d := fun i j => (g i ^ 2 - g j ^ 2) * (h x i * h y j - h y i * h x j)
  have hf (i j) : d i j = w i * w j * ((g j ^ 2 - g i ^ 2) *
      (profile (x * g j) * profile (y * g i) - profile (x * g i) * profile (y * g j))) := by
    dsimp [d, h]
    ring
  have hsym (i j) : d i j = d j i := by dsimp [d]; ring
  have hpos (i j) (hij : g i < g j) : 0 < (g j ^ 2 - g i ^ 2) *
      (profile (x * g j) * profile (y * g i) - profile (x * g i) * profile (y * g j)) := by
    apply mul_pos
    · exact sub_pos.mpr (pow_lt_pow_left₀ hij (hg i).le (by decide))
    · exact sub_pos.mpr (profile_minor hx hxy (hg i) hij)
  have hw (i) : 0 ≤ w i := mul_nonneg (hp i) (sq_nonneg _)
  have ordered (i j) (hij : g i < g j) : 0 ≤ d i j := by
    rw [hf]
    exact mul_nonneg (mul_nonneg (hw i) (hw j)) (hpos i j hij).le
  have nonneg (i j) : 0 ≤ d i j := by
    rcases lt_trichotomy (g i) (g j) with hij | hij | hji
    · exact ordered i j hij
    · simp [d, hij]
    · rw [hsym]; exact ordered j i hji
  obtain ⟨i, j, hpi, hpj, hij⟩ := support
  have positive : 0 < d i j := by
    rw [hf]
    exact mul_pos (mul_pos (mul_pos hpi (sq_pos_of_pos (hg i)))
      (mul_pos hpj (sq_pos_of_pos (hg j)))) (hpos i j hij)
  have total : 0 < ∑ i, ∑ j, d i j := by
    apply (sum_pos_iff_of_nonneg (fun i _ => sum_nonneg (fun j _ => nonneg i j))).mpr
    exact ⟨i, mem_univ _, (sum_pos_iff_of_nonneg (fun j _ => nonneg i j)).mpr
      ⟨j, mem_univ _, positive⟩⟩
  have m2 (t) : moment p g 2 t = ∑ i, h t i := rfl
  have m4 (t) : moment p g 4 t = ∑ i, g i ^ 2 * h t i := by
    apply sum_congr rfl
    intro k _
    dsimp [h, w]
    ring
  have sumprod (a b : Fin n → ℝ) : (∑ i, ∑ j, a i * b j) = (∑ i, a i) * ∑ j, b j := by
    simp only [sum_mul, mul_sum]
    exact sum_comm
  have symdet : (∑ i, ∑ j, d i j) =
       2 * (moment p g 4 x * moment p g 2 y - moment p g 2 x * moment p g 4 y) := by
    have expand (i j) : d i j = (g i ^ 2 * h x i) * h y j -
        (g i ^ 2 * h y i) * h x j - h x i * (g j ^ 2 * h y j) +
        h y i * (g j ^ 2 * h x j) := by dsimp [d]; ring
    simp only [expand, sum_add_distrib, sum_sub_distrib, sumprod, m4, m2]
    ring
  rw [symdet] at total
  have strict : moment p g 2 x * moment p g 4 y < moment p g 4 x * moment p g 2 y := by
    linarith only [total]
  refine ⟨strict, ?_⟩
  rintro ⟨a,b⟩ ⟨a',b'⟩ eq
  obtain ⟨ex,ey⟩ := Prod.mk.inj eq
  have ha : (a - a') * (moment p g 4 x * moment p g 2 y -
      moment p g 2 x * moment p g 4 y) = 0 := by
    linear_combination moment p g 4 x * ey - moment p g 4 y * ex
  have hb : (b - b') * (moment p g 4 x * moment p g 2 y -
      moment p g 2 x * moment p g 4 y) = 0 := by
    linear_combination moment p g 2 y * ex - moment p g 2 x * ey
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp ha).resolve_right (sub_pos.mpr strict).ne'))
    (sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right (sub_pos.mpr strict).ne'))

end
end D5.S3.Quantum.StaticExchange.DipoleTwoDistance
