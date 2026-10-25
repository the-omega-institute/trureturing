import CFMPOriginalForward427

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawCos)
open CFMPOriginalForward390 (angle angleD)

namespace CFMPOriginalAngleWindow491Transient

private theorem quotient_window (X z p q r t k : ℝ)
    (hX : 1 < X) (hz : (4:ℝ)/5 < z ∧ z ≤ 1)
    (hp : (4:ℝ)/5 < p ∧ p ≤ 1) (hq : (4:ℝ)/5 < q ∧ q ≤ 1)
    (hr : (4:ℝ)/5 < r ∧ r ≤ 1) (ht : (1:ℝ)/2 ≤ t ∧ t ≤ 1)
    (hk : k ≤ 1)
    (hquot : X = ((1-z^2)*k+p*r+q*t+z*(p*t+q*r)) /
      Real.sqrt (angleD z p q * angleD z t r)) :
    X < Real.sqrt ((237620:ℝ)/28431) ∧
      Real.sqrt ((237620:ℝ)/28431) < 3 := by
  have hz0 : 0 < z := by linarith only [hz.1]
  have hp0 : 0 < p := by linarith only [hp.1]
  have hq0 : 0 < q := by linarith only [hq.1]
  have hr0 : 0 < r := by linarith only [hr.1]
  have ht0 : 0 < t := by linarith only [ht.1]
  have hzsq : (16:ℝ)/25 < z^2 := by nlinarith only [hz.1, hz0, sq_nonneg (z-(4:ℝ)/5)]
  have hpsq : (16:ℝ)/25 < p^2 := by nlinarith only [hp.1, hp0, sq_nonneg (p-(4:ℝ)/5)]
  have hqsq : (16:ℝ)/25 < q^2 := by nlinarith only [hq.1, hq0, sq_nonneg (q-(4:ℝ)/5)]
  have hrsq : (16:ℝ)/25 < r^2 := by nlinarith only [hr.1, hr0, sq_nonneg (r-(4:ℝ)/5)]
  have htsq : (1:ℝ)/4 ≤ t^2 := by nlinarith only [ht.1, ht0, sq_nonneg (t-(1:ℝ)/2)]
  have hzp : (16:ℝ)/25 < z*p := by
    calc
      (16:ℝ)/25 = ((4:ℝ)/5)*((4:ℝ)/5) := by norm_num
      _ < z*p := mul_lt_mul hz.1 hp.1.le (by norm_num) hz0.le
  have hprod1 : (64:ℝ)/125 < z*p*q := by
    calc
      (64:ℝ)/125 = ((16:ℝ)/25)*((4:ℝ)/5) := by norm_num
      _ < (z*p)*q := mul_lt_mul hzp hq.1.le (by norm_num) (mul_pos hz0 hp0).le
  have hzr : (16:ℝ)/25 < z*r := by
    calc
      (16:ℝ)/25 = ((4:ℝ)/5)*((4:ℝ)/5) := by norm_num
      _ < z*r := mul_lt_mul hz.1 hr.1.le (by norm_num) hz0.le
  have hprod2 : (8:ℝ)/25 < z*t*r := by
    have hb := mul_lt_mul_of_pos_right hzr ht0
    have ha := mul_le_mul_of_nonneg_left ht.1 (show (0:ℝ) ≤ 16/25 by norm_num)
    nlinarith only [hb, ha]
  have hD1 : (243:ℝ)/125 < angleD z p q := by
    dsimp only [angleD]
    nlinarith only [hzsq, hpsq, hqsq, hprod1]
  have hD2 : (117:ℝ)/100 < angleD z t r := by
    dsimp only [angleD]
    nlinarith only [hzsq, htsq, hrsq, hprod2]
  have hD10 : 0 < angleD z p q := by linarith only [hD1]
  have hD20 : 0 < angleD z t r := by linarith only [hD2]
  have hden0 : 0 < Real.sqrt (angleD z p q * angleD z t r) :=
    Real.sqrt_pos.mpr (mul_pos hD10 hD20)
  let N := (1-z^2)*k+p*r+q*t+z*(p*t+q*r)
  have hpr : p*r ≤ 1 := by nlinarith only [mul_le_mul hp.2 hr.2 hr0.le (by norm_num : (0:ℝ) ≤ 1)]
  have hqt : q*t ≤ 1 := by nlinarith only [mul_le_mul hq.2 ht.2 ht0.le (by norm_num : (0:ℝ) ≤ 1)]
  have hpt : p*t ≤ 1 := by nlinarith only [mul_le_mul hp.2 ht.2 ht0.le (by norm_num : (0:ℝ) ≤ 1)]
  have hqr : q*r ≤ 1 := by nlinarith only [mul_le_mul hq.2 hr.2 hr0.le (by norm_num : (0:ℝ) ≤ 1)]
  have hsum : 0 ≤ p*t+q*r := (add_pos (mul_pos hp0 ht0) (mul_pos hq0 hr0)).le
  have hzz : z*(p*t+q*r) ≤ 2 := by
    have ha := mul_le_mul_of_nonneg_right hz.2 hsum
    nlinarith only [ha, hpt, hqr]
  have hsin0 : 0 ≤ 1-z^2 := by
    have ha := mul_nonneg (sub_nonneg.mpr hz.2) (show 0 ≤ 1+z by linarith only [hz0])
    nlinarith only [ha]
  have hsk : (1-z^2)*k ≤ 1-z^2 := mul_le_of_le_one_right hsin0 hk
  have hN : N < (109:ℝ)/25 := by
    dsimp only [N]
    nlinarith only [hsk, hzsq, hpr, hqt, hzz]
  have hXN : X * Real.sqrt (angleD z p q * angleD z t r) = N :=
    (eq_div_iff hden0.ne').mp hquot
  have hN0 : 0 < N := hXN ▸ mul_pos (by linarith only [hX]) hden0
  have hN2 : N^2 < ((109:ℝ)/25)^2 :=
    (sq_lt_sq₀ hN0.le (by norm_num : (0:ℝ) ≤ 109/25)).mpr hN
  have hprod : ((243:ℝ)/125)*((117:ℝ)/100) < angleD z p q * angleD z t r :=
    mul_lt_mul hD1 hD2.le (by norm_num) hD10.le
  have hXs : 0 < X^2 := sq_pos_of_pos (by linarith only [hX])
  have hsq : X^2*(angleD z p q * angleD z t r) = N^2 := by
    calc
      _ = (X * Real.sqrt (angleD z p q * angleD z t r))^2 := by
        rw [mul_pow, Real.sq_sqrt (mul_pos hD10 hD20).le]
      _ = _ := congrArg (fun v : ℝ => v^2) hXN
  have hbound : X^2 * (((243:ℝ)/125)*((117:ℝ)/100)) < ((109:ℝ)/25)^2 := by
    calc
      _ < X^2*(angleD z p q * angleD z t r) := mul_lt_mul_of_pos_left hprod hXs
      _ = N^2 := hsq
      _ < _ := hN2
  have hX2 : X^2 < (237620:ℝ)/28431 := by nlinarith only [hbound]
  refine ⟨Real.lt_sqrt_of_sq_lt hX2, ?_⟩
  apply (Real.sqrt_lt' (by norm_num : (0:ℝ) < 3)).mpr
  norm_num

private theorem cos_small (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ Real.pi/5) :
    (4:ℝ)/5 < Real.cos a ∧ Real.cos a ≤ 1 := by
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi ha
    (show Real.pi/5 ≤ Real.pi by linarith [Real.pi_pos]) hb
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hsn := Real.sqrt_nonneg (5:ℝ)
  rw [Real.cos_pi_div_five] at hm
  exact ⟨by nlinarith only [hm, hs, hsn], Real.cos_le_one a⟩

private theorem cos_medium (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ Real.pi/3) :
    (1:ℝ)/2 ≤ Real.cos a ∧ Real.cos a ≤ 1 := by
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi ha
    (show Real.pi/3 ≤ Real.pi by linarith [Real.pi_pos]) hb
  rw [Real.cos_pi_div_three] at hm
  exact ⟨hm, Real.cos_le_one a⟩

/-- Original same-input window, with the medium neighbour in original slot4. -/
theorem original_window_slot4 (x : Fin 6 → ℝ)
    (hx : ∀ q, 1 < x q) (hc : ∀ q, -1 < rawCos x q ∧ rawCos x q < 1)
    (h0 : angle x 0 ≤ Real.pi/5) (h1 : angle x 1 ≤ Real.pi/5)
    (h2 : angle x 2 ≤ Real.pi/5) (h5 : angle x 5 ≤ Real.pi/5)
    (h4 : angle x 4 ≤ Real.pi/3) :
    x 0 < Real.sqrt ((237620:ℝ)/28431) ∧
      Real.sqrt ((237620:ℝ)/28431) < 3 := by
  have ha (q : Fin 6) : 0 ≤ angle x q := Real.arccos_nonneg _
  obtain ⟨_, _, _, _, _, _, hquot⟩ := CFMPOriginalForward390.forward x hx hc
  have hsin : Real.sin (angle x 0)^2 = 1-Real.cos (angle x 0)^2 := by
    nlinarith only [Real.sin_sq_add_cos_sq (angle x 0)]
  rw [hsin] at hquot
  exact quotient_window (x 0) (Real.cos (angle x 0)) (Real.cos (angle x 1))
    (Real.cos (angle x 2)) (Real.cos (angle x 5)) (Real.cos (angle x 4))
    (Real.cos (angle x 3)) (hx 0) (cos_small _ (ha 0) h0)
    (cos_small _ (ha 1) h1) (cos_small _ (ha 2) h2) (cos_small _ (ha 5) h5)
    (cos_medium _ (ha 4) h4) (Real.cos_le_one _) hquot

end CFMPOriginalAngleWindow491Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPOriginalAngleWindow491Transient.original_window_slot4
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP491 missing declaration {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP491 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP491 CHECKED {name} axioms={axioms}"
