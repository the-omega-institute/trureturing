/- GID: D5/S3/Analytic/SeriesInequalities/TwoModeEnvelopePeriodEscape
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/TwoModeEnvelopePeriodEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The first-mode period defeats a locally flat two-mode envelope contact. -/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Analytic.SeriesInequalities.TwoModeEnvelopePeriodEscape

private def da (b g : ℝ) : ℝ := g ^ 2 + (1 - b) ^ 2
private def db (b g : ℝ) : ℝ := g ^ 2 + b ^ 2
private def c (b g : ℝ) : ℝ := 2 * ((1 - b) / da b g + b / db b g)
private def d (b g : ℝ) : ℝ := 2 * g * (2 * b - 1) / (da b g * db b g)
private def a (b g : ℝ) : ℝ := 2 * b / db b g

/-- One damped oscillatory mode with its exponentially decaying lag. -/
def mode (b g v : ℝ) : ℝ :=
  Real.exp (-(1 - b) * v) * (c b g * Real.cos (g * v) - d b g * Real.sin (g * v)) -
    a b g * Real.exp (-v)

/-- The opposite-phase two-frequency profile. -/
def profile (b g₁ g₂ v : ℝ) : ℝ := mode b g₁ v - mode b g₂ v

private theorem exp_neg_quadratic {v : ℝ} (hv : 0 ≤ v) :
    Real.exp (-v) ≤ 1 - v + v ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hd (x : ℝ) : HasDerivAt f (-1 + x + Real.exp (-x)) x := by
    dsimp [f]
    exact ((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
      ((hasDerivAt_id x).pow 2 |>.div_const 2)).sub
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg)).congr_deriv (by
        simp only [id_eq]
        ring)
  have hm : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (by fun_prop)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x _ => by linarith [Real.one_sub_le_exp_neg x])
  have h := hm (by simp) (show v ∈ Set.Ici 0 from hv) hv
  simpa [f] using h

private theorem exp_margin {b v : ℝ} (hb : (7 / 10 : ℝ) ≤ b) (hb1 : b < 1)
    (hv : 0 < v) (hv1 : v < 9 / 20) :
    v / 6 < b * (Real.exp (-(1 - b) * v) - Real.exp (-v)) -
      (51 / 50 : ℝ) * (1 - b) * (1 - Real.exp (-(1 - b) * v)) := by
  have ha : 0 ≤ 1 - b := by linarith
  have ha1 : 1 - b ≤ (3 / 10 : ℝ) := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hlo := Real.one_sub_le_exp_neg ((1 - b) * v)
  have hhi := exp_neg_quadratic hv.le
  have heq : -((1 - b) * v) = -(1 - b) * v := by ring
  rw [heq] at hlo
  have hq : b * v - v ^ 2 / 2 ≤ Real.exp (-(1 - b) * v) - Real.exp (-v) := by
    linarith
  have hu : 1 - Real.exp (-(1 - b) * v) ≤ (1 - b) * v := by linarith
  have hqm := mul_le_mul_of_nonneg_left hq hb0
  have hum := mul_le_mul_of_nonneg_left hu (show 0 ≤ (51 / 50 : ℝ) * (1 - b) by positivity)
  have hb2 : (49 / 100 : ℝ) ≤ b ^ 2 := by nlinarith
  have ha2 : (1 - b) ^ 2 ≤ (9 / 100 : ℝ) := by nlinarith
  have hcoeff : (1991 / 5000 : ℝ) ≤ b ^ 2 - (51 / 50 : ℝ) * (1 - b) ^ 2 := by
    linarith
  have hcm := mul_le_mul_of_nonneg_right hcoeff hv.le
  have hv2 := mul_lt_mul_of_pos_left hv1 hv
  have hv3 := mul_le_mul_of_nonneg_right (show b ≤ 1 by linarith) (sq_nonneg v)
  nlinarith

private theorem denom_pos {b g : ℝ} (hg : 0 < g) : 0 < da b g ∧ 0 < db b g := by
  dsimp [da, db]
  constructor <;> nlinarith [sq_pos_of_pos hg, sq_nonneg (1 - b), sq_nonneg b]

private theorem denom_bounds {b g : ℝ} (hb : (7 / 10 : ℝ) ≤ b) (hb1 : b < 1)
    (hg : 14 ≤ g) : db b g ≤ (197 / 196 : ℝ) * da b g ∧
      db b g ≤ (197 / 196 : ℝ) * g ^ 2 := by
  have hb0 : 0 ≤ b := by linarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hg2 : 196 ≤ g ^ 2 := by nlinarith
  dsimp [da, db]
  constructor <;> nlinarith [sq_nonneg (1 - b)]

private theorem phase_bound {c d t : ℝ} (hc : 0 < c) :
    c * Real.cos t - d * Real.sin t ≤ c + d ^ 2 / (2 * c) := by
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 2 * c)).mp
  rw [add_mul, div_mul_cancel₀ _ (by positivity)]
  have h := Real.sin_sq_add_cos_sq t
  have hsq := sq_nonneg (c * Real.sin t + d)
  have hcos := sq_nonneg (1 - Real.cos t)
  have hcircle := congrArg (fun x : ℝ => c ^ 2 * x) h
  nlinarith [mul_nonneg (sq_nonneg c) hcos]

private theorem c_pos {b g : ℝ} (hb : (7 / 10 : ℝ) ≤ b) (hb1 : b < 1)
    (hg : 0 < g) : 0 < c b g := by
  obtain ⟨ha, hb'⟩ := denom_pos (b := b) hg
  unfold c
  have : 0 < b / db b g := div_pos (by linarith) hb'
  have : 0 ≤ (1 - b) / da b g := div_nonneg (by linarith) ha.le
  linarith

private theorem d_nonneg {b g : ℝ} (hb : (7 / 10 : ℝ) ≤ b) (hg : 0 < g) :
    0 ≤ d b g := by
  obtain ⟨ha, hb'⟩ := denom_pos (b := b) hg
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hg.le) (by linarith))
    (mul_pos ha hb').le

private theorem angular_excess {b g : ℝ} (hb : (7 / 10 : ℝ) ≤ b) (hb1 : b < 1)
    (hg : 0 < g) : d b g ^ 2 / (2 * c b g) ≤ 1 / g ^ 4 := by
  obtain ⟨hda, hdb⟩ := denom_pos (b := b) hg
  have hab : 0 ≤ (1 - b) * b := mul_nonneg (by linarith) (by linarith)
  have hgs : 0 < g ^ 2 := sq_pos_of_pos hg
  have hthird : 0 < g ^ 2 + (1 - b) * b := by linarith
  have hceq : c b g = 2 * (g ^ 2 + (1 - b) * b) / (da b g * db b g) := by
    unfold c
    field_simp [hda.ne', hdb.ne']
    dsimp [da, db]
    ring
  have hval : d b g ^ 2 / (2 * c b g) =
      g ^ 2 * (2 * b - 1) ^ 2 /
        (da b g * db b g * (g ^ 2 + (1 - b) * b)) := by
    rw [hceq]
    unfold d
    field_simp [hda.ne', hdb.ne', hthird.ne']
  rw [hval]
  have hdab : g ^ 4 ≤ da b g * db b g := by
    have h1 : g ^ 2 ≤ da b g := by dsimp [da]; nlinarith [sq_nonneg (1 - b)]
    have h2 : g ^ 2 ≤ db b g := by dsimp [db]; nlinarith [sq_nonneg b]
    calc
      g ^ 4 = g ^ 2 * g ^ 2 := by ring
      _ ≤ da b g * db b g := mul_le_mul h1 h2 hgs.le hda.le
  have hnum : (2 * b - 1) ^ 2 ≤ 1 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hdab hgs.le
  have hprod2 := mul_le_mul_of_nonneg_left hab (mul_pos hda hdb).le
  have hn := mul_le_mul_of_nonneg_left hnum (by positivity : 0 ≤ g ^ 6)
  apply (div_le_div_iff₀ (by positivity) (by positivity : 0 < g ^ 4)).mpr
  nlinarith

private def jump (b g v : ℝ) : ℝ :=
  2 * b * (Real.exp (-(1 - b) * v) - Real.exp (-v)) / db b g -
    2 * (1 - b) * (1 - Real.exp (-(1 - b) * v)) / da b g

private theorem mode_same_phase (b g v : ℝ) :
    Real.exp (-(1 - b) * v) * c b g - a b g * Real.exp (-v) - mode b g 0 =
      jump b g v := by
  simp [mode, jump, c, a]
  ring

private theorem mode_general_bound {b g v : ℝ}
    (hb : (7 / 10 : ℝ) ≤ b) (hb1 : b < 1) (hg : 0 < g) (hv : 0 ≤ v) :
    mode b g v - mode b g 0 ≤ jump b g v + 1 / g ^ 4 := by
  have he : 0 ≤ Real.exp (-(1 - b) * v) := (Real.exp_pos _).le
  have he1 : Real.exp (-(1 - b) * v) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hv)
  have hph := phase_bound (t := g * v) (d := d b g) (c_pos hb hb1 hg)
  have hm := mul_le_mul_of_nonneg_left hph he
  have hex := angular_excess hb hb1 hg
  have hc := c_pos hb hb1 hg
  have hex0 : 0 ≤ d b g ^ 2 / (2 * c b g) := by positivity
  have heex := mul_le_mul_of_nonneg_right he1 hex0
  calc
    mode b g v - mode b g 0 ≤
        Real.exp (-(1 - b) * v) * (c b g + d b g ^ 2 / (2 * c b g)) -
          a b g * Real.exp (-v) - mode b g 0 := by
      exact sub_le_sub_right (sub_le_sub_right hm _) _
    _ = jump b g v + Real.exp (-(1 - b) * v) * (d b g ^ 2 / (2 * c b g)) := by
      rw [← mode_same_phase b g v]
      ring
    _ ≤ jump b g v + d b g ^ 2 / (2 * c b g) :=
      add_le_add le_rfl (by simpa using heex)
    _ ≤ jump b g v + 1 / g ^ 4 := add_le_add le_rfl hex


private theorem mode_nonnegative_sine {b g v : ℝ}
    (hb : (7 / 10 : ℝ) ≤ b) (hb1 : b < 1) (hg : 0 < g)
    (hs : 0 ≤ Real.sin (g * v)) :
    mode b g v - mode b g 0 ≤ jump b g v := by
  have hc := c_pos hb hb1 hg
  have hd := d_nonneg hb hg
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one (g * v)) hc.le
  have hsin := mul_nonneg hd hs
  have hphase : c b g * Real.cos (g * v) - d b g * Real.sin (g * v) ≤ c b g := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hphase (Real.exp_pos (-(1 - b) * v)).le
  have hj := mode_same_phase b g v
  unfold mode at *
  linarith

private theorem mode_period {b g : ℝ} (hg : 0 < g) :
    mode b g (2 * Real.pi / g) - mode b g 0 = jump b g (2 * Real.pi / g) := by
  have hp : g * (2 * Real.pi / g) = 2 * Real.pi := by field_simp
  have hj := mode_same_phase b g (2 * Real.pi / g)
  unfold mode at *
  simpa [hp, Real.cos_two_pi, Real.sin_two_pi] using hj

private theorem period_bounds {g : ℝ} (hg : 14 ≤ g) :
    0 < 2 * Real.pi / g ∧ 2 * Real.pi / g < 9 / 20 := by
  have hg0 : 0 < g := by linarith
  constructor
  · positivity
  · apply (div_lt_iff₀ hg0).mpr
    linarith [Real.pi_lt_d2]

private theorem product_bound {A₁ A₂ B₁ B₂ : ℝ}
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hB₂ : 0 < B₂)
    (h₁ : B₁ ≤ (197 / 196 : ℝ) * A₁) (h₂ : B₂ ≤ (197 / 196 : ℝ) * A₂) :
    B₁ * B₂ ≤ (51 / 50 : ℝ) * (A₁ * A₂) := by
  calc
    B₁ * B₂ ≤ ((197 / 196 : ℝ) * A₁) * ((197 / 196 : ℝ) * A₂) :=
      mul_le_mul h₁ h₂ hB₂.le (by positivity)
    _ = (197 / 196 : ℝ) ^ 2 * (A₁ * A₂) := by ring
    _ ≤ (51 / 50 : ℝ) * (A₁ * A₂) :=
      mul_le_mul_of_nonneg_right (by norm_num) (mul_pos hA₁ hA₂).le

private theorem jump_gap {b g₁ g₂ v : ℝ}
    (hb : (7 / 10 : ℝ) ≤ b) (hb1 : b < 1) (hg₁ : 14 ≤ g₁) (hg₂ : g₁ < g₂)
    (hv : 0 < v) (hv1 : v < 9 / 20) :
    v * (g₂ ^ 2 - g₁ ^ 2) / (3 * (db b g₁ * db b g₂)) <
      jump b g₁ v - jump b g₂ v := by
  have hg₁0 : 0 < g₁ := by linarith
  have hg₂0 : 0 < g₂ := by linarith
  obtain ⟨ha₁, hb₁⟩ := denom_pos (b := b) hg₁0
  obtain ⟨ha₂, hb₂⟩ := denom_pos (b := b) hg₂0
  have hA := mul_pos ha₁ ha₂
  have hB := mul_pos hb₁ hb₂
  have hD : 0 < g₂ ^ 2 - g₁ ^ 2 := by nlinarith
  let q := Real.exp (-(1 - b) * v) - Real.exp (-v)
  let u := 1 - Real.exp (-(1 - b) * v)
  have hu : 0 ≤ u := by
    dsimp [u]
    have : Real.exp (-(1 - b) * v) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hv.le)
    linarith
  have hau : 0 ≤ (1 - b) * u := mul_nonneg (by linarith) hu
  have hden := product_bound ha₁ ha₂ hb₂
    (denom_bounds hb hb1 hg₁).1 (denom_bounds hb hb1 (by linarith : 14 ≤ g₂)).1
  have hn : (1 - b) * u / (da b g₁ * da b g₂) ≤
      ((51 / 50 : ℝ) * ((1 - b) * u)) / (db b g₁ * db b g₂) := by
    apply (div_le_div_iff₀ hA hB).mpr
    convert mul_le_mul_of_nonneg_left hden hau using 1
    ring
  have hsmall := (div_lt_div_iff_of_pos_right hB).mpr (exp_margin hb hb1 hv hv1)
  simp only [mul_assoc] at hsmall
  change (v / 6) / (db b g₁ * db b g₂) <
    (b * q - (51 / 50 : ℝ) * ((1 - b) * u)) / (db b g₁ * db b g₂) at hsmall
  rw [div_div, sub_div] at hsmall
  have hbracket : v / (6 * (db b g₁ * db b g₂)) <
      b * q / (db b g₁ * db b g₂) - (1 - b) * u / (da b g₁ * da b g₂) := by
    linarith
  have hid : jump b g₁ v - jump b g₂ v =
      2 * (g₂ ^ 2 - g₁ ^ 2) *
        (b * q / (db b g₁ * db b g₂) - (1 - b) * u / (da b g₁ * da b g₂)) := by
    dsimp [jump, q, u]
    field_simp [ha₁.ne', ha₂.ne', hb₁.ne', hb₂.ne']
    dsimp [da, db]
    ring
  rw [hid]
  calc
    v * (g₂ ^ 2 - g₁ ^ 2) / (3 * (db b g₁ * db b g₂)) =
        2 * (g₂ ^ 2 - g₁ ^ 2) * (v / (6 * (db b g₁ * db b g₂))) := by
          field_simp [hB.ne']
          ring
    _ < _ := mul_lt_mul_of_pos_left hbracket (by positivity)

private theorem far_gap {b g₁ g₂ v : ℝ}
    (hb : (7 / 10 : ℝ) ≤ b) (hb1 : b < 1) (hg₁ : 14 ≤ g₁)
    (hg₂ : 3 / 2 * g₁ ≤ g₂) (hv : 0 < v) :
    v / (6 * g₁ ^ 2) <
      v * (g₂ ^ 2 - g₁ ^ 2) / (3 * (db b g₁ * db b g₂)) := by
  have hg₁0 : 0 < g₁ := by linarith
  have hg₂0 : 0 < g₂ := by linarith
  have h₁ := sq_pos_of_pos hg₁0
  have h₂ := sq_pos_of_pos hg₂0
  have h₂p := (denom_pos (b := b) hg₂0).2
  have hprod := product_bound h₁ h₂ h₂p
    (denom_bounds hb hb1 hg₁).2 (denom_bounds hb hb1 (by linarith : 14 ≤ g₂)).2
  have hdelta : (5 / 9 : ℝ) * g₂ ^ 2 ≤ g₂ ^ 2 - g₁ ^ 2 := by nlinarith
  have hD := mul_le_mul_of_nonneg_right hdelta h₁.le
  have hpos := mul_pos h₁ h₂
  have hBgap : db b g₁ * db b g₂ < 2 * (g₂ ^ 2 - g₁ ^ 2) * g₁ ^ 2 := by
    nlinarith only [hprod, hD, hpos]
  have hB := mul_pos (denom_pos (b := b) hg₁0).2 h₂p
  apply (div_lt_div_iff₀ (by positivity : 0 < 6 * g₁ ^ 2) (by positivity)).mpr
  convert mul_lt_mul_of_pos_left hBgap (show 0 < 3 * v by positivity) using 1 <;> ring

private theorem period_beats_quartic {g : ℝ} (hg : 14 ≤ g) :
    1 / g ^ 4 < (2 * Real.pi / g) / (6 * g ^ 2) := by
  have hg0 : 0 < g := by linarith
  have hg2 := sq_pos_of_pos hg0
  have hpg : 3 < Real.pi * g := by nlinarith [Real.pi_gt_three]
  have hvt : 6 < (2 * Real.pi / g) * g ^ 2 := by
    have hvg : (2 * Real.pi / g) * g = 2 * Real.pi := div_mul_cancel₀ _ hg0.ne'
    nlinarith [congrArg (fun x : ℝ => x * g) hvg]
  apply (div_lt_div_iff₀ (pow_pos hg0 4) (by positivity)).mpr
  convert mul_lt_mul_of_pos_right hvt hg2 using 1 <;> ring

/-- The positive first-frequency period is a strict global-envelope competitor.
The frequencies and real part range over unbounded real parameter families. -/
theorem result {b g₁ g₂ : ℝ} (hb : (7 / 10 : ℝ) ≤ b) (hb1 : b < 1)
    (hg₁ : 14 ≤ g₁) (hg₂ : g₁ < g₂) :
    profile b g₁ g₂ 0 < profile b g₁ g₂ (2 * Real.pi / g₁) := by
  have hg₁0 : 0 < g₁ := by linarith
  have hg₂0 : 0 < g₂ := by linarith
  obtain ⟨hv, hv1⟩ := period_bounds hg₁
  have hgap := jump_gap hb hb1 hg₁ hg₂ hv hv1
  have hp := mode_period (b := b) hg₁0
  by_cases hnear : g₂ ≤ 3 / 2 * g₁
  · have hgv : g₁ * (2 * Real.pi / g₁) = 2 * Real.pi := by field_simp
    have hlow := mul_le_mul_of_nonneg_right hg₂.le hv.le
    have hhigh := mul_le_mul_of_nonneg_right hnear hv.le
    have hs : 0 ≤ Real.sin (g₂ * (2 * Real.pi / g₁)) := by
      have h := Real.sin_nonneg_of_nonneg_of_le_pi
        (show 0 ≤ g₂ * (2 * Real.pi / g₁) - 2 * Real.pi by nlinarith)
        (show g₂ * (2 * Real.pi / g₁) - 2 * Real.pi ≤ Real.pi by nlinarith)
      simpa only [Real.sin_sub_two_pi] using h
    have hm := mode_nonnegative_sine hb hb1 hg₂0 hs
    have hnum : 0 < (2 * Real.pi / g₁) * (g₂ ^ 2 - g₁ ^ 2) /
        (3 * (db b g₁ * db b g₂)) := by
      have hsq : 0 < g₂ ^ 2 - g₁ ^ 2 := by nlinarith
      have hB := mul_pos (denom_pos (b := b) hg₁0).2 (denom_pos (b := b) hg₂0).2
      positivity
    unfold profile
    linarith
  · have hfar : 3 / 2 * g₁ ≤ g₂ := (lt_of_not_ge hnear).le
    have hf := far_gap hb hb1 hg₁ hfar hv
    have hq := period_beats_quartic hg₁
    have hpow : g₁ ^ 4 < g₂ ^ 4 := pow_lt_pow_left₀ hg₂ hg₁0.le (by decide)
    have hrec := one_div_lt_one_div_of_lt (pow_pos hg₁0 4) hpow
    have hm := mode_general_bound hb hb1 hg₂0 hv.le
    unfold profile
    linarith

#print axioms result

end D5.S3.Analytic.SeriesInequalities.TwoModeEnvelopePeriodEscape
