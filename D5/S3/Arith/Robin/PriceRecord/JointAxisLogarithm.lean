/- GID: D5/S3/Arith/Robin/PriceRecord/JointAxisLogarithm
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/JointAxisLogarithm
   mirror-E: none(waiver:elementary-logarithmic-arithmetic)
   anchors: []
   utility: none
   digest: Nonvanishing, sensitivity and root cancellation for the joint Robin logarithm. -/
import D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! The joint logarithmic form for the first two axes of the three-axis Robin budget. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm

open Real Set
open D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation
  (cutoff_resonance_separation)

/-- The joint logarithmic form for axes zero and one of the three-axis budget. -/
def omegaThree (h p q : ℝ) : ℝ :=
  h * log (3 * p / (p + q)) - q * log (2 * p / (p + h))

/-- The specified two rational logarithms cannot cancel with coefficients h and q. -/
theorem omegaThree_ne_zero {p h q : ℕ} (hh : 0 < h) (hp : h < p)
    (hlo : 11 * h < 7 * q) (hhi : 5 * q < 8 * h) :
    omegaThree (h : ℝ) (p : ℝ) (q : ℝ) ≠ 0 := by
  intro hz
  have hp0 : 0 < p := hh.trans hp
  have hq : h < q := by omega
  have hq0 : 0 < q := hh.trans hq
  have hq3 : q < 3 * h := by omega
  have hseparation := (cutoff_resonance_separation hh hp hq hq3
    (j := 3) (by decide)).2
  simp only [Nat.cast_ofNat] at hseparation
  have hsign :
      (q : ℝ) * log (2 * (p : ℝ) / ((p : ℝ) + h)) -
        (h : ℝ) * log (3 * (p : ℝ) / ((p : ℝ) + q)) =
        -omegaThree (h : ℝ) (p : ℝ) (q : ℝ) := by
    unfold omegaThree
    ring
  rw [hsign, hz, neg_zero, abs_zero] at hseparation
  have hW : 0 < (3 : ℕ) ^ h * (p + h) ^ q := by positivity
  have hN : 0 < max (2 ^ q * p ^ (q - h) * (p + q) ^ h) (3 ^ h * (p + h) ^ q) :=
    hW.trans_le (le_max_right _ _)
  exact (not_le_of_gt (one_div_pos.mpr (Nat.cast_pos.mpr hN))) hseparation

private theorem hasDerivAt_log_scaled_ratio {k p b : ℝ} (hk : 0 < k)
    (hp : 0 < p) (hpb : 0 < p + b) :
    HasDerivAt (fun x : ℝ => log (k * x / (x + b))) (b / (p * (p + b))) p := by
  have harg : 0 < k * p / (p + b) := by positivity
  have h := (((hasDerivAt_id p).const_mul k).div ((hasDerivAt_id p).add_const b)
    hpb.ne').log harg.ne'
  simp only [id_eq, Pi.div_apply, mul_one] at h
  convert h using 1
  field_simp [hk.ne', hp.ne', hpb.ne']
  ring

/-- The first partial derivative includes the cancellation of the inverse-square terms. -/
theorem omegaThree_hasDerivAt_p {h p q : ℝ} (hp : 0 < p) (hh : 0 < h) (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => omegaThree h x q)
      (-(h * q * (q - h) / (p * (p + h) * (p + q)))) p := by
  have hph : 0 < p + h := by positivity
  have hpq : 0 < p + q := by positivity
  have h₃ := hasDerivAt_log_scaled_ratio (k := 3) (by norm_num) hp hpq
  have h₂ := hasDerivAt_log_scaled_ratio (k := 2) (by norm_num) hp hph
  unfold omegaThree
  convert (h₃.const_mul h).sub (h₂.const_mul q) using 1
  field_simp [hp.ne', hph.ne', hpq.ne']
  ring

private theorem log_two_ratio {h p : ℝ} (hp : 0 < p) (hh : 0 < h) :
    log (2 * p / (p + h)) = log 2 - log (1 + h / p) := by
  have hph : 0 < p + h := by positivity
  have harg : 0 < 1 + h / p := by positivity
  rw [show 2 * p / (p + h) = 2 / (1 + h / p) by
    field_simp [hp.ne', hph.ne', harg.ne']]
  exact log_div (by norm_num) harg.ne'

/-- The second partial derivative of the same joint form. -/
theorem omegaThree_hasDerivAt_q {h p q : ℝ} (hp : 0 < p) (hh : 0 < h) (hq : 0 < q) :
    HasDerivAt (fun y : ℝ => omegaThree h p y)
      (-log 2 + log (1 + h / p) - h / (p + q)) q := by
  have hpq : 0 < p + q := by positivity
  have harg : 0 < 3 * p / (p + q) := by positivity
  have h₃ : HasDerivAt (fun y : ℝ => log (3 * p / (p + y))) (-(1 / (p + q))) q := by
    have hd := (((hasDerivAt_const q (3 * p)).div
      ((hasDerivAt_id q).const_add p) hpq.ne')).log harg.ne'
    simp only [id_eq, Pi.div_apply, zero_mul, mul_one, zero_sub] at hd
    convert hd using 1
    field_simp [hp.ne', hpq.ne']
  have h₂ : HasDerivAt (fun y : ℝ => y * log (2 * p / (p + h)))
      (log (2 * p / (p + h))) q := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id q).mul_const (log (2 * p / (p + h)))
  unfold omegaThree
  rw [show -log 2 + log (1 + h / p) - h / (p + q) =
      h * -(1 / (p + q)) - log (2 * p / (p + h)) by
    rw [log_two_ratio hp hh]
    ring]
  exact (h₃.const_mul h).sub h₂

private theorem p_bound {h p q X : ℝ} (hh : 0 < h) (hX : 0 < X)
    (hp : h * X / 2 ≤ p) (hq₁ : h ≤ q) (hq₂ : q ≤ 3 * h) :
    |-(h * q * (q - h) / (p * (p + h) * (p + q)))| ≤ 48 / X ^ 3 := by
  have hbase : 0 < h * X / 2 := by positivity
  have hp0 : 0 < p := hbase.trans_le hp
  have hq0 : 0 < q := hh.trans_le hq₁
  have hdiff : 0 ≤ q - h := sub_nonneg.mpr hq₁
  have hden : 0 < p * (p + h) * (p + q) := by positivity
  have hnum : h * q * (q - h) ≤ h * (3 * h) * (2 * h) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hq₂ hh.le) (by linarith only [hq₂])
      hdiff (by positivity)
  have hden' : (h * X / 2) ^ 3 ≤ p * (p + h) * (p + q) := calc
    _ ≤ p ^ 3 := pow_le_pow_left₀ hbase.le hp 3
    _ = p * p * p := by ring
    _ ≤ _ :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith only [hh]) hp0.le)
        (by linarith only [hq0]) hp0.le (by positivity)
  rw [abs_neg, abs_div, abs_of_nonneg (by positivity : 0 ≤ h * q * (q - h)), abs_of_pos hden]
  calc
    _ ≤ (h * (3 * h) * (2 * h)) / (p * (p + h) * (p + q)) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (h * (3 * h) * (2 * h)) / (h * X / 2) ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hbase 3) hden'
    _ = 48 / X ^ 3 := by
      field_simp [hh.ne', hX.ne']
      ring

private theorem q_bound {h p q : ℝ} (hh : 0 < h) (hp : 2 * h ≤ p) (hq : 0 < q) :
    |-log 2 + log (1 + h / p) - h / (p + q)| ≤ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hpq : 0 < p + q := by positivity
  have hratio : h / p ≤ 1 / 2 := (div_le_iff₀ hp0).2 (by linarith only [hp])
  have hterm : h / (p + q) ≤ 1 / 2 :=
    (div_le_iff₀ hpq).2 (by linarith only [hp, hq])
  have hlog : log (1 + h / p) ≤ 1 / 2 := by
    have := log_le_sub_one_of_pos (show 0 < 1 + h / p by positivity)
    linarith only [this, hratio]
  have hlog0 : 0 ≤ log (1 + h / p) :=
    log_nonneg (by linarith only [div_pos hh hp0])
  have hlog2 : log 2 < 1 := by
    have := log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith only [this]
  have hlog20 : 0 < log 2 := log_pos (by norm_num)
  have hterm0 : 0 ≤ h / (p + q) := by positivity
  exact abs_le.mpr ⟨by linarith only [hlog0, hlog2, hterm],
    by linarith only [hlog, hlog20, hterm0]⟩

/-- On the rectangle around the scaled phases, the first error has coefficient
at most 48/X³ and the second error has coefficient at most 2. -/
theorem abs_omegaThree_sub_le {h p q s r X : ℝ} (hh : 1 ≤ h)
    (hX : 4 ≤ X) (hs : X ≤ s) (hr₁ : 3 / 2 ≤ r) (hr₂ : r ≤ 2)
    (hp : |p - h * s| ≤ 1 / 2) (hq : |q - h * r| ≤ 1 / 2) :
    |omegaThree h p q - omegaThree h (h * s) (h * r)| ≤
      48 / X ^ 3 * |p - h * s| + 2 * |q - h * r| := by
  have hh0 : 0 < h := by linarith only [hh]
  have hX0 : 0 < X := by linarith only [hX]
  have hXh : 4 * h ≤ h * X := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hX hh0.le
  have hXs : h * X ≤ h * s := mul_le_mul_of_nonneg_left hs hh0.le
  have hp₀ : h * X / 2 ≤ h * s := by linarith only [hXs, hXh, hh]
  have hp₁ : h * X / 2 ≤ p := by
    have := (abs_le.mp hp).1
    linarith only [this, hXs, hXh, hh]
  have hrlo := mul_le_mul_of_nonneg_left hr₁ hh0.le
  have hrhi := mul_le_mul_of_nonneg_left hr₂ hh0.le
  have hq₀ : h * r ∈ Icc h (3 * h) := ⟨by linarith only [hrlo, hh], by linarith only [hrhi, hh]⟩
  have hq₁ : q ∈ Icc h (3 * h) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hq
    exact ⟨by linarith only [hlo, hrlo, hh], by linarith only [hhi, hrhi, hh]⟩
  have hq0 : 0 < q := hh0.trans_le hq₁.1
  have hpMove :
      |omegaThree h p q - omegaThree h (h * s) q| ≤ 48 / X ^ 3 * |p - h * s| := by
    have h := (convex_Ici (h * X / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (𝕜 := ℝ) (f := fun x : ℝ => omegaThree h x q)
      (f' := fun x : ℝ => -(h * q * (q - h) / (x * (x + h) * (x + q))))
      (C := 48 / X ^ 3)
      (fun x hx => (omegaThree_hasDerivAt_p
        ((show 0 < h * X / 2 by positivity).trans_le hx) hh0 hq0).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact p_bound hh0 hX0 hx hq₁.1 hq₁.2)
      hp₀ hp₁
    simpa only [Real.norm_eq_abs] using h
  have hqMove :
      |omegaThree h (h * s) q - omegaThree h (h * s) (h * r)| ≤ 2 * |q - h * r| := by
    have hps2 : 2 * h ≤ h * s := by linarith only [hXs, hXh, hh]
    have hps : 0 < h * s := lt_of_lt_of_le (by positivity) hps2
    have h := (convex_Icc h (3 * h)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (𝕜 := ℝ) (f := fun y : ℝ => omegaThree h (h * s) y)
      (f' := fun y : ℝ => -log 2 + log (1 + h / (h * s)) - h / (h * s + y))
      (C := 2)
      (fun y hy => (omegaThree_hasDerivAt_q hps hh0 (hh0.trans_le hy.1)).hasDerivWithinAt)
      (fun y hy => by rw [Real.norm_eq_abs]; exact q_bound hh0 hps2 (hh0.trans_le hy.1))
      hq₀ hq₁
    simpa only [Real.norm_eq_abs] using h
  calc
    |omegaThree h p q - omegaThree h (h * s) (h * r)| =
        |(omegaThree h p q - omegaThree h (h * s) q) +
          (omegaThree h (h * s) q - omegaThree h (h * s) (h * r))| := by
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hpMove hqMove)

/-- At the scaled phases the two root offsets cancel. The exact remainder
depends solely on the residuals in the two root equations. -/
theorem omegaThree_at_root_phases {h L a b e₂ e₃ : ℝ}
    (hh : 0 < h) (hL : 0 < L) (ha : 0 < a) (hb : 0 < b)
    (haEq : a + log (1 + a / L) = log 2 + e₂)
    (hbEq : b + log (1 + b / L) = log 3 + e₃) :
    omegaThree h (h * (L / a)) (h * (b / a)) = h * ((b / a) * e₂ - e₃) := by
  have harg₂ : 0 < 1 + a / L := by positivity
  have harg₃ : 0 < 1 + b / L := by positivity
  have hden₂ : 0 < h * (L / a) + h := by positivity
  have hden₃ : 0 < h * (L / a) + h * (b / a) := by positivity
  have h₂ : 2 * (h * (L / a)) / (h * (L / a) + h) = 2 / (1 + a / L) := by
    apply (div_eq_div_iff hden₂.ne' harg₂.ne').2
    field_simp [hL.ne', ha.ne']
  have h₃ : 3 * (h * (L / a)) / (h * (L / a) + h * (b / a)) = 3 / (1 + b / L) := by
    apply (div_eq_div_iff hden₃.ne' harg₃.ne').2
    field_simp [hL.ne', ha.ne']
  unfold omegaThree
  rw [h₃, h₂, log_div (by norm_num : (3 : ℝ) ≠ 0) harg₃.ne',
    log_div (by norm_num : (2 : ℝ) ≠ 0) harg₂.ne']
  rw [show log 3 - log (1 + b / L) = b - e₃ by linarith only [hbEq],
    show log 2 - log (1 + a / L) = a - e₂ by linarith only [haEq]]
  field_simp [ha.ne']
  ring

/-- Integer labels in the positive-denominator convention satisfy the same obstruction. -/
theorem omegaThree_ne_zero_int {p h q : ℤ} (hh : 0 < h) (hp : h < p)
    (hlo : 11 * h < 7 * q) (hhi : 5 * q < 8 * h) :
    omegaThree (h : ℝ) (p : ℝ) (q : ℝ) ≠ 0 := by
  have hcH := Int.toNat_of_nonneg hh.le
  have hcP := Int.toNat_of_nonneg (show 0 ≤ p by omega)
  have hcQ := Int.toNat_of_nonneg (show 0 ≤ q by omega)
  have hh' : 0 < h.toNat := by
    exact_mod_cast (show (0 : ℤ) < (h.toNat : ℤ) by rwa [hcH])
  have hp' : h.toNat < p.toNat := by
    exact_mod_cast (show (h.toNat : ℤ) < (p.toNat : ℤ) by rwa [hcH, hcP])
  have hlo' : 11 * h.toNat < 7 * q.toNat := by
    exact_mod_cast (show 11 * (h.toNat : ℤ) < 7 * (q.toNat : ℤ) by rwa [hcH, hcQ])
  have hhi' : 5 * q.toNat < 8 * h.toNat := by
    exact_mod_cast (show 5 * (q.toNat : ℤ) < 8 * (h.toNat : ℤ) by rwa [hcH, hcQ])
  have hn := omegaThree_ne_zero hh' hp' hlo' hhi'
  rwa [← Int.cast_natCast, hcH, ← Int.cast_natCast, hcP, ← Int.cast_natCast, hcQ] at hn

end D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm
