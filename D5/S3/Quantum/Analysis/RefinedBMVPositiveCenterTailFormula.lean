/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterTailFormula
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact divided differences for the large positive-center spectral gap. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailAverage
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailLinear
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenter
import D5.S3.Quantum.Analysis.RefinedBMVUniformDiscriminant

namespace RefinedBMV.PositiveCenter

open DividedDifference (homogeneousThree clear_distinct clear_repeat_first)

/-- Multiplying out the two normalizing gaps leaves a single correction
to the leading divided difference. -/
private theorem tail_distinct_clear (p : ℕ) {q r : ℝ} (hq : q < r) :
    (1-q)*(1-r)*homogeneousThree p q r 1 =
      1 - (r^(p+2) + (1-r)*(r^(p+2)-q^(p+2))/(r-q)) := by
  have hg := sub_pos.mpr hq
  have h := clear_distinct p q r (1 : ℝ)
  rw [one_pow] at h
  apply (mul_right_cancel₀ hg.ne')
  field_simp [hg.ne']
  linear_combination h

private theorem tail_exp_pow (t : ℝ) (n : ℕ) :
    (Real.exp t)^n = Real.exp ((n : ℝ)*t) :=
  (Real.exp_nat_mul t n).symm

private theorem tail_gap_pos {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    0 < upperTailGap h t := by
  have he := Real.exp_lt_exp.mpr (neg_lt_zero.mpr (mul_pos hh ht))
  rw [Real.exp_zero] at he
  exact div_pos (sub_pos.mpr he) hh

private theorem tail_add_gap {h : ℝ} (hh : 0 < h) (u d : ℝ) :
    upperTailGap h (d+u) = upperTailGap h u + Real.exp (-(h*u))*upperTailGap h d := by
  unfold upperTailGap
  rw [show -(h*(d+u)) = -(h*u) + -(h*d) by ring, Real.exp_add]
  field_simp [hh.ne']
  ring

/-- The distinct-node exponential correction written without a finite sum. -/
noncomputable def upperTailCrossCorrection (h u d : ℝ) : ℝ :=
  Real.exp (-((3+h)*d)) *
    (Real.exp (-(h*d)) + upperTailGap h d * (1-Real.exp (-((3+2*h)*u))) / upperTailGap h u)

/-- The small exponential part of a repeated-node correction. -/
noncomputable def upperTailRepeatCorrection (h t : ℝ) : ℝ :=
  (1 + (3+h)*upperTailGap h t)*Real.exp (-((3+h)*t))

theorem upperTail_distinct_nodes {p : ℕ} (hp : 0 < p) {u d : ℝ} (hu : 0 < u) :
    let h : ℝ := 3 / (p : ℝ)
    let q := Real.exp (-(h*(d+u)))
    let r := Real.exp (-(h*d))
    (1-q)*(1-r)*homogeneousThree p q r 1 = 1 - upperTailCrossCorrection h u d := by
  let h : ℝ := 3/(p : ℝ)
  let q := Real.exp (-(h*(d+u)))
  let r := Real.exp (-(h*d))
  let g : ℝ := 3+h
  let k : ℝ := 3+2*h
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hmul : (p : ℝ)*h = 3 := by
    dsimp [h]
    field_simp
  have hg : ((p : ℝ)+1)*h = g := by dsimp [g]; linarith only [hmul]
  have hk : ((p : ℝ)+2)*h = k := by dsimp [k]; linarith only [hmul]
  have hqr : q < r := Real.exp_lt_exp.mpr (by nlinarith only [mul_pos hh hu])
  have hq : q = r*Real.exp (-(h*u)) := by
    dsimp [q, r]
    rw [← Real.exp_add]
    congr 1
    ring
  have hrpow : r^(p+2) = Real.exp (-(k*d)) := by
    rw [show r = Real.exp (-(h*d)) from rfl, tail_exp_pow, Nat.cast_add, Nat.cast_ofNat]
    congr 1
    linear_combination -d*hk
  have hqp : q^(p+2) = Real.exp (-(k*d))*Real.exp (-(k*u)) := by
    rw [show q = Real.exp (-(h*(d+u))) from rfl, tail_exp_pow, Nat.cast_add, Nat.cast_ofNat,
      ← Real.exp_add]
    congr 1
    linear_combination -(d+u)*hk
  have ha (t : ℝ) : 1-Real.exp (-(h*t)) = h*upperTailGap h t := by
    unfold upperTailGap
    field_simp
  have hgap : r-q = r*(h*upperTailGap h u) := by
    rw [hq, ← ha]
    ring
  have hfac : Real.exp (-(k*d)) = r*Real.exp (-(g*d)) := by
    dsimp [r]
    rw [← Real.exp_add]
    dsimp [k, g]
    congr 1
    ring
  have hquot : (r^(p+2)-q^(p+2))/(r-q) =
      Real.exp (-(g*d))*(1-Real.exp (-(k*u)))/(h*upperTailGap h u) := by
    rw [hrpow, hqp, hgap]
    have hquot' : Real.exp (-(k*d)) - Real.exp (-(k*d))*Real.exp (-(k*u)) =
        r*(Real.exp (-(g*d))*(1-Real.exp (-(k*u)))) := by rw [hfac]; ring
    rw [hquot']
    exact mul_div_mul_left _ _ (Real.exp_pos _).ne'
  change (1-q)*(1-r)*homogeneousThree p q r 1 =
    1 - Real.exp (-(g*d))*(r + upperTailGap h d*(1-Real.exp (-(k*u)))/upperTailGap h u)
  rw [tail_distinct_clear p hqr]
  congr 1
  rw [show (1-r)*(r^(p+2)-q^(p+2))/(r-q) =
      (1-r)*((r^(p+2)-q^(p+2))/(r-q)) by ring, hquot, hrpow, hfac, show 1-r = _ from ha d]
  field_simp [hh.ne', (tail_gap_pos hh hu).ne']

theorem upperTail_repeated_nodes {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    let q := Real.exp (-(h*t))
    (1-q)^2 * homogeneousThree p q q 1 = 1 - upperTailRepeatCorrection h t := by
  let h : ℝ := 3 / (p : ℝ)
  let q := Real.exp (-(h*t))
  let g : ℝ := 3+h
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hmul : (p : ℝ)*h = 3 := by dsimp [h]; field_simp
  have hg : ((p : ℝ)+1)*h = g := by dsimp [g]; linarith only [hmul]
  have ho : q^(p+1) = Real.exp (-(g*t)) := by
    rw [show q = _ from rfl, tail_exp_pow, Nat.cast_add, Nat.cast_one]
    congr 1
    linear_combination -t*hg
  have hq : 1-q = h*upperTailGap h t := by
    dsimp [q, upperTailGap]
    field_simp
  have hnext : q^(p+2) = q^(p+1)*q := pow_succ _ _
  change (1-q)^2 * homogeneousThree p q q 1 =
    1 - (1+g*upperTailGap h t)*Real.exp (-(g*t))
  rw [clear_repeat_first p q 1, one_pow, mul_one, hnext, ho]
  calc
    _ = 1 - (1+((p : ℝ)+1)*(1-q))*Real.exp (-(g*t)) := by ring
    _ = _ := by rw [hq, ← hg]; ring

theorem upperTail_linear_correction {h u d : ℝ} (hh : 0 < h) :
    let g : ℝ := 3+h
    let k : ℝ := 3+2*h
    let a := upperTailGap h
    upperTailRepeatCorrection h (d+u) + upperTailRepeatCorrection h d -
      2*upperTailCrossCorrection h u d = Real.exp (-(g*d)) *
        (upperTailRepeatCorrection h u - 1 + a d *
          (g*(Real.exp (-(k*u))-1) + 2*(k-(1-Real.exp (-(k*u)))/a u))) := by
  let g : ℝ := 3+h
  let k : ℝ := 3+2*h
  let a := upperTailGap h
  have hadd : a (d+u) = a u + Real.exp (-(h*u))*a d := tail_add_gap hh u d
  have h₁ : Real.exp (-(g*(d+u))) = Real.exp (-(g*d))*Real.exp (-(g*u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₂ : Real.exp (-(k*u)) = Real.exp (-(g*u))*Real.exp (-(h*u)) := by
    rw [← Real.exp_add]
    dsimp [g, k]
    congr 1
    ring
  have h₃ : Real.exp (-(h*d)) = 1-h*a d := by
    dsimp [a, upperTailGap]
    field_simp [hh.ne']
    ring
  dsimp only [upperTailRepeatCorrection, upperTailCrossCorrection]
  change (1+g*a (d+u))*Real.exp (-(g*(d+u))) + (1+g*a d)*Real.exp (-(g*d)) -
    2*(Real.exp (-(g*d))*(Real.exp (-(h*d)) + a d*(1-Real.exp (-(k*u)))/a u)) = _
  rw [hadd, h₁, h₂, h₃]
  dsimp [a, g, k]
  ring

private theorem tail_cube_pow {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let a := Real.exp (-t/(p : ℝ))
    a^3 = Real.exp (-((3/(p : ℝ))*t)) ∧ a^p = Real.exp (-t) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  dsimp only
  constructor
  · rw [tail_exp_pow]
    push_cast
    congr 1
    ring
  · rw [tail_exp_pow]
    congr 1
    field_simp

private theorem tail_choose_scale {p : ℕ} (hp : 0 < p) :
    let h : ℝ := 3/(p : ℝ)
    ((p+2).choose 2 : ℝ)*h^2 = (3+h)*(3+2*h)/2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  dsimp only
  rw [Nat.cast_choose_two]
  push_cast
  field_simp
  ring

private theorem tail_gap_factor {h t : ℝ} (hh : 0 < h) :
    1 - Real.exp (-(h*t)) = h*upperTailGap h t := by
  unfold upperTailGap
  field_simp

/-- The repeated-node defect after normalizing the larger cube root to one. -/
theorem upperTail_repeated_defect {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let h : ℝ := 3/(p : ℝ)
    let a := Real.exp (-t/(p : ℝ))
    (1-a^3)^2 * DimThree.defect p a a 1 = 1 - upperTailLambda h t := by
  let h : ℝ := 3/(p : ℝ)
  let a := Real.exp (-t/(p : ℝ))
  let q := Real.exp (-(h*t))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  obtain ⟨ha, hap⟩ := tail_cube_pow hp t
  change a^3 = q at ha
  change a^p = Real.exp (-t) at hap
  change (1-a^3)^2 * DimThree.defect p a a 1 = 1 - upperTailLambda h t
  rw [DividedDifference.defect_eq_homogeneous]
  simp only [ha, one_pow, mul_one, mul_sub, mul_pow, hap]
  have hRepeat : (1-q)^2 * homogeneousThree p q q 1 =
      1 - upperTailRepeatCorrection h t := upperTail_repeated_nodes hp t
  rw [hRepeat, show 1-q = _ from tail_gap_factor hh, show Real.exp (-t)*Real.exp (-t) =
    Real.exp (-(2*t)) by rw [← Real.exp_add]; congr 1; ring]
  rw [show (h*upperTailGap h t)^2*
       (((p+2).choose 2 : ℝ)*Real.exp (-(2*t))) =
       (((p+2).choose 2 : ℝ)*h^2)*(upperTailGap h t)^2*Real.exp (-(2*t)) by ring]
  rw [show ((p+2).choose 2 : ℝ)*h^2 = _ from tail_choose_scale hp]
  unfold upperTailRepeatCorrection upperTailLambda
  ring

/-- The mixed-node defect after normalizing the larger cube root to one. -/
theorem upperTail_distinct_defect {p : ℕ} (hp : 0 < p) {u d : ℝ} (hu : 0 < u) :
    let h : ℝ := 3/(p : ℝ)
    let a := Real.exp (-(d+u)/(p : ℝ))
    let x := Real.exp (-d/(p : ℝ))
    (1-a^3)*(1-x^3)*DimThree.defect p a x 1 =
      1 - upperTailCrossCorrection h u d -
        ((3+h)*(3+2*h)/2)*upperTailGap h (d+u)*upperTailGap h d*Real.exp (-(u+2*d)) := by
  let h : ℝ := 3/(p : ℝ)
  let a := Real.exp (-(d+u)/(p : ℝ))
  let x := Real.exp (-d/(p : ℝ))
  let q := Real.exp (-(h*(d+u)))
  let r := Real.exp (-(h*d))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  obtain ⟨ha, hap⟩ := tail_cube_pow hp (d+u)
  obtain ⟨hx, hxp⟩ := tail_cube_pow hp d
  change a^3=q at ha
  change x^3=r at hx
  change a^p = Real.exp (-(d+u)) at hap
  change x^p = Real.exp (-d) at hxp
  change (1-a^3)*(1-x^3)*DimThree.defect p a x 1 = _
  rw [DividedDifference.defect_eq_homogeneous, mul_sub]
  simp only [ha, hx, one_pow, mul_one, mul_pow, hap, hxp]
  have hDistinct : (1-q)*(1-r)*homogeneousThree p q r 1 =
      1 - upperTailCrossCorrection h u d := upperTail_distinct_nodes hp hu
  rw [hDistinct, show 1-q = _ from tail_gap_factor hh, show 1-r = _ from tail_gap_factor hh,
    show Real.exp (-(d+u))*Real.exp (-d) = Real.exp (-(u+2*d)) by
      rw [← Real.exp_add]; congr 1; ring]
  have hscale : ((p+2).choose 2 : ℝ)*h^2 = (3+h)*(3+2*h)/2 := tail_choose_scale hp
  linear_combination -(upperTailGap h (d+u)*upperTailGap h d*Real.exp (-(u+2*d)))*hscale

/-- The actual numerator from the positive-center kernel, in normalized
spectral coordinates, with both root factors separated. -/
theorem upperTail_defect_numerator {p : ℕ} (hp : 11 ≤ p) {u d : ℝ}
    (hu : 0 < u) (hd : 11 ≤ d) :
    let h : ℝ := 3/(p : ℝ)
    let a := Real.exp (-(d+u)/(p : ℝ))
    let x := Real.exp (-d/(p : ℝ))
    (1-a^3)*(1-x^3)*
        (DimThree.defect p a x 1 -
          Real.sqrt (DimThree.defect p a a 1 * DimThree.defect p x x 1)) =
      1 - upperTailCrossCorrection h u d -
        ((3+h)*(3+2*h)/2)*upperTailGap h (d+u)*upperTailGap h d*Real.exp (-(u+2*d)) -
        Real.sqrt (1-upperTailLambda h (d+u))*Real.sqrt (1-upperTailLambda h d) := by
  let h : ℝ := 3/(p : ℝ)
  let a := Real.exp (-(d+u)/(p : ℝ))
  let x := Real.exp (-d/(p : ℝ))
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hple : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3/11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hple
  have hd₀ : 0 < d := by linarith
  have hv₀ : 0 < d+u := by positivity
  have ha : a^3 = Real.exp (-(h*(d+u))) := (tail_cube_pow hp₀ (d+u)).1
  have hx : x^3 = Real.exp (-(h*d)) := (tail_cube_pow hp₀ d).1
  have ha₁ : 0 < 1-a^3 := by
    rw [ha, tail_gap_factor hh]
    exact mul_pos hh (tail_gap_pos hh hv₀)
  have hx₁ : 0 < 1-x^3 := by
    rw [hx, tail_gap_factor hh]
    exact mul_pos hh (tail_gap_pos hh hd₀)
  have hv : 11 ≤ d+u := by linarith
  have hb : 0 ≤ 1-upperTailLambda h (d+u) := (Real.sqrt_pos.mp
    ((by norm_num : (0 : ℝ) < 3/4).trans_le (upperTail_radical_lower hh hhmax hv))).le
  have hA : (1-a^3)^2 * DimThree.defect p a a 1 =
      1-upperTailLambda h (d+u) := upperTail_repeated_defect hp₀ (d+u)
  have hX : (1-x^3)^2 * DimThree.defect p x x 1 =
      1-upperTailLambda h d := upperTail_repeated_defect hp₀ d
  have hRoot : (1-a^3)*(1-x^3)*
      Real.sqrt (DimThree.defect p a a 1 * DimThree.defect p x x 1) =
      Real.sqrt (1-upperTailLambda h (d+u))*Real.sqrt (1-upperTailLambda h d) := calc
    _ = Real.sqrt (((1-a^3)*(1-x^3))^2 *
          (DimThree.defect p a a 1 * DimThree.defect p x x 1)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos ha₁ hx₁)]
    _ = Real.sqrt (((1-a^3)^2 * DimThree.defect p a a 1) *
          ((1-x^3)^2 * DimThree.defect p x x 1)) := congrArg Real.sqrt (by ring)
    _ = _ := by rw [hA, hX, Real.sqrt_mul hb]
  dsimp only
  change (1-a^3)*(1-x^3)*(DimThree.defect p a x 1 -
    Real.sqrt (DimThree.defect p a a 1 * DimThree.defect p x x 1)) = _
  rw [mul_sub, hRoot]
  have hD : (1-a^3)*(1-x^3)*DimThree.defect p a x 1 = _ :=
    upperTail_distinct_defect hp₀ hu
  rw [hD]

private theorem tail_leading_gap {h u d : ℝ} (hh : 0 < h) (hu : 0 < u) (hd : 0 < d) :
    let a := upperTailGap h
    let ell := 1-Real.exp (-u)
    a d-a (d+u)*Real.exp (-u) =
      a d*ell*(1-upperTailSlope h d*upperTailRatio h u) := by
  let a := upperTailGap h
  let ell := 1-Real.exp (-u)
  let e := Real.exp (-u)
  have hExp : Real.exp u*e = 1 := by dsimp [e]; rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hEll : ell = (Real.exp u-1)*e := by dsimp only [ell]; rw [sub_mul, one_mul, hExp]
  have hgap : 0 < Real.exp u-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hRatio : ell*upperTailRatio h u = e*a u := by
    rw [upperTailRatio, hEll]
    change (Real.exp u-1)*e*(a u/(Real.exp u-1)) = _
    field_simp [hgap.ne']
  have hL : upperTailSlope h d*a d = Real.exp (-(h*d)) := by
    rw [← (hasDerivAt_upperTailGap (t := d) hh).deriv]
    exact ((div_eq_iff (tail_gap_pos hh hd).ne').mp (upperTailGap_logDeriv hh hd)).symm
  have hAdd : a (d+u) = a d + Real.exp (-(h*d))*a u := by
    rw [add_comm d u]
    exact tail_add_gap hh d u
  change a d-a (d+u)*e = a d*ell*(1-upperTailSlope h d*upperTailRatio h u)
  calc
    _ = a d*ell - Real.exp (-(h*d))*(e*a u) := by rw [hAdd]; dsimp only [ell, e]; ring
    _ = _ := by rw [← hL, ← hRatio]; ring

/-- The exact upper-tail numerator is a leading square and the two
regularized errors whose derivatives are bounded in the companion modules. -/
theorem upperTail_numerator_decomposition {p : ℕ} (hp : 11 ≤ p) {u d : ℝ}
    (hu : 0 < u) (hd : 11 ≤ d) :
    let h : ℝ := 3/(p : ℝ)
    let a := Real.exp (-(d+u)/(p : ℝ))
    let x := Real.exp (-d/(p : ℝ))
    let c : ℝ := (3+h)*(3+2*h)/2
    let X := c*(upperTailGap h d)^2*Real.exp (-(2*d))
    let ell := 1-Real.exp (-u)
    let r := 1-upperTailSlope h d*upperTailRatio h u
    (1-a^3)*(1-x^3)*
        (DimThree.defect p a x 1 -
          Real.sqrt (DimThree.defect p a a 1 * DimThree.defect p x x 1)) =
      X*ell^2/2*(r^2 + upperTailLinearError h u d + upperTailQuadratic h u d) := by
  let h : ℝ := 3/(p : ℝ)
  let a := upperTailGap h
  let v := d+u
  let c : ℝ := (3+h)*(3+2*h)/2
  let B : ℝ → ℝ := fun t ↦ c*(a t)^2*Real.exp (-(2*t))
  let A := upperTailRepeatCorrection h
  let b : ℝ → ℝ := fun t ↦ Real.sqrt (1-upperTailLambda h t)
  let C := upperTailCrossCorrection h u d
  let G := c*a v*a d*Real.exp (-(u+2*d))
  let ell := 1-Real.exp (-u)
  let r := 1-upperTailSlope h d*upperTailRatio h u
  let P := B d * ell^2
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hple : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3/11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hple
  have hd₀ : 0 < d := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have ha : 0 < a d := tail_gap_pos hh hd₀
  have hB : 0 < B d := mul_pos (mul_pos hc (sq_pos_of_pos ha)) (Real.exp_pos _)
  have hell : 0 < ell := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))
  have hSq {t : ℝ} (ht : 11 ≤ t) : (b t)^2 = 1-A t-B t := by
    have hb := (by norm_num : (0 : ℝ) < 3/4).trans_le (upperTail_radical_lower hh hhmax ht)
    rw [show (b t)^2 = 1-upperTailLambda h t from Real.sq_sqrt (Real.sqrt_pos.mp hb).le]
    unfold upperTailLambda
    dsimp [A, upperTailRepeatCorrection, B, c, a]
    ring
  have hAGM : 2*(1-C-G-b v*b d) =
      (B v+B d-2*G)+(A v+A d-2*C)+(b v-b d)^2 := by
    have hv : 11 ≤ v := by dsimp [v]; linarith
    nlinarith only [hSq hv, hSq hd]
  have hLead : B v+B d-2*G = P*r^2 := by
    have hv : Real.exp (-(2*v)) = Real.exp (-(2*d))*(Real.exp (-u))^2 := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      dsimp [v]
      congr 1
      ring
    have hg : Real.exp (-(u+2*d)) = Real.exp (-(2*d))*Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = c*Real.exp (-(2*d))*(a d-a v*Real.exp (-u))^2 := by
        dsimp only [B, G]
        rw [hv, hg]
        ring
      _ = _ := by
        rw [show a d-a v*Real.exp (-u) = a d*ell*r from tail_leading_gap hh hu hd₀]
        dsimp [P, B]
        ring
  have hLin : A v+A d-2*C = P*upperTailLinearError h u d := by
    rw [upperTailLinearError_eq_regularized hh hu hd₀]
    have hf := upperTail_linear_correction (u := u) (d := d) hh
    change A v+A d-2*C = _ at hf
    rw [hf]
    have hExp : Real.exp (-((3+h)*d)) =
        Real.exp (-(2*d))*Real.exp (-((1+h)*d)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hExp]
    change _ = c*(a d)^2*Real.exp (-(2*d))*ell^2 *
      (Real.exp (-((1+h)*d))*(A u-1+a d*
        ((3+h)*(Real.exp (-((3+2*h)*u))-1) + 2*(3+2*h-(1-Real.exp (-((3+2*h)*u)))/a u))) /
          (c*(a d)^2*ell^2))
    field_simp [hc.ne', ha.ne', hell.ne']
    ring
  have hQuad : (b v-b d)^2 = P*upperTailQuadratic h u d := by
    change _ = B d*ell^2*(((b v-b d)/ell)^2*(B d)⁻¹)
    field_simp [hB.ne', hell.ne']
  have hn := upperTail_defect_numerator hp hu hd
  dsimp only at hn ⊢
  rw [hn]
  change 1-C-G-b v*b d = P/2*(r^2 + upperTailLinearError h u d + upperTailQuadratic h u d)
  rw [hLead, hLin, hQuad] at hAGM
  nlinarith only [hAGM]

private theorem tail_repeat_high_sum (p : ℕ) {q : ℝ} (hq : q < 1) :
    (1-q)*homogeneousThree p q 1 1 =
      (p+1 : ℝ) - ∑ i ∈ Finset.range (p+1), q^(i+1) := by
  have hsum : (∑ i ∈ Finset.range (p+1), q^(i+1)) =
      q*(∑ i ∈ Finset.range (p+1), q^i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ pow_succ' _ _
  have hgeom : (∑ i ∈ Finset.range (p+1), q^(i+1))*(1-q) = q*(1-q^(p+1)) := by
    rw [hsum, mul_assoc, geom_sum_mul_neg]
  apply mul_right_cancel₀ (sub_ne_zero.mpr hq.ne')
  conv_rhs => rw [sub_mul, hgeom]
  calc
    _ = (1-q)^2 * homogeneousThree p q 1 1 := by ring
    _ = _ := by
      rw [DividedDifference.clear_repeat_last p q 1, one_pow, mul_one, one_pow, mul_one]
      rw [show q^(p+2) = q^(p+1)*q from pow_succ _ _]
      ring

private theorem tail_logCoordinate {p : ℕ} (hp : 0 < p) (s t : ℝ) :
    logCoordinate p (Real.exp (-s/(p : ℝ))) (Real.exp (-t/(p : ℝ))) = s-t := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [logCoordinate, ← Real.exp_sub, Real.log_exp]
  field_simp
  ring

/-- The lower diagonal weight is the negative marginal composition moment
times its explicit exponential scale. -/
theorem upperTail_lower_weight {p : ℕ} (hp : 0 < p) (u d : ℝ) :
    let a := Real.exp (-(d+u)/(p : ℝ))
    let x := Real.exp (-d/(p : ℝ))
    DimThree.defect p a x x =
      ((p+2).choose 2 : ℝ)*Real.exp (-(3*d+u))*compositionMoment p 0 (-u) := by
  let a := Real.exp (-(d+u)/(p : ℝ))
  let x := Real.exp (-d/(p : ℝ))
  have hx : 0 < x := Real.exp_pos _
  have ha : 0 < a := Real.exp_pos _
  change DimThree.defect p a x x = _
  rw [← UniformThreeSpectrum.defect_cycle_all p a x x,
    defect_eq_compositionMoment hp hx hx ha, DimThree.gaps_length_eq_choose]
  rw [show logCoordinate p x x = 0 by
        change logCoordinate p (Real.exp (-d/(p : ℝ))) (Real.exp (-d/(p : ℝ))) = _
        rw [tail_logCoordinate hp, sub_self],
      show logCoordinate p x a = -u by
        change logCoordinate p (Real.exp (-d/(p : ℝ))) (Real.exp (-(d+u)/(p : ℝ))) = _
        rw [tail_logCoordinate hp]
        ring]
  have hap : a^p = Real.exp (-(d+u)) := (tail_cube_pow hp (d+u)).2
  have hxp : x^p = Real.exp (-d) := (tail_cube_pow hp d).2
  rw [mul_pow, mul_pow, hxp, hap, ← Real.exp_add, ← Real.exp_add]
  congr 3
  ring

/-- The upper diagonal weight gives the positive normalizer used in the
upper-tail derivative argument. -/
theorem upperTail_upper_weight {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    let h : ℝ := 3/(p : ℝ)
    let a := Real.exp (-v/(p : ℝ))
    let N : ℝ := (p+2).choose 2
    (1-a^3)*DimThree.defect p a 1 1 =
      (p+1 : ℝ)*upperTailNormalizer (p+1) h (N/(p+1)) v := by
  let h : ℝ := 3/(p : ℝ)
  let a := Real.exp (-v/(p : ℝ))
  let q := Real.exp (-(h*v))
  let N : ℝ := (p+2).choose 2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh hv))
  have ha : a^3 = q := (tail_cube_pow hp v).1
  have hap : a^p = Real.exp (-v) := (tail_cube_pow hp v).2
  have hpows : (∑ i ∈ Finset.range (p+1), q^(i+1)) =
      ∑ i ∈ Finset.range (p+1), Real.exp (-((i+1 : ℕ) : ℝ)*h*v) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp [q]
    rw [tail_exp_pow]
    congr 1
    ring
  change (1-a^3)*DimThree.defect p a 1 1 =
    (p+1 : ℝ)*upperTailNormalizer (p+1) h (N/(p+1)) v
  rw [DividedDifference.defect_eq_homogeneous, mul_sub]
  simp only [ha, one_pow, mul_one, hap]
  rw [tail_repeat_high_sum p hq, hpows]
  unfold upperTailNormalizer
  push_cast
  let S := ∑ i ∈ Finset.range (p+1), Real.exp (-((i : ℝ)+1)*h*v)
  change (p+1 : ℝ) - S - (1-q)*(N*Real.exp (-v)) =
    (p+1 : ℝ)*(1 - S/(p+1) - (N/(p+1))*((1-q)*Real.exp (-v)))
  field_simp

/-- The positive factor that carries the mixed-derivative sign in the upper tail. -/
noncomputable def upperTailBaseFactor (p : ℕ) (u d : ℝ) : ℝ :=
  let h : ℝ := 3/(p : ℝ)
  let N : ℝ := (p+2).choose 2
  Real.sqrt (N/(p+1))/2 * Real.exp (-d/2) *
    ((1-Real.exp (-(h*d)))/Real.sqrt (1-Real.exp (-(h*(d+u))))) *
      (Real.exp (u/2)*(1-Real.exp (-u))^2/Real.sqrt (compositionMoment p 0 (-u)))

/-- The exact normalized kernel on the upper-gap tail. -/
theorem upperTail_logKernel_decomposition {p : ℕ} (hp : 11 ≤ p) {u d : ℝ}
    (hu : 0 < u) (hd : 11 ≤ d) :
    let h : ℝ := 3/(p : ℝ)
    let N : ℝ := (p+2).choose 2
    let r := 1-upperTailSlope h d*upperTailRatio h u
    logKernel p u (d+u) =
      (1/Real.sqrt (upperTailNormalizer (p+1) h (N/(p+1)) (d+u))) *
        upperTailBaseFactor p u d *
        (r^2 + upperTailLinearError h u d + upperTailQuadratic h u d) := by
  let h : ℝ := 3/(p : ℝ)
  let n : ℝ := p+1
  let N : ℝ := (p+2).choose 2
  let v := d+u
  let a := Real.exp (-v/(p : ℝ))
  let x := Real.exp (-d/(p : ℝ))
  let A := upperTailNormalizer (p+1) h (N/n) v
  let C := compositionMoment p 0 (-u)
  let α := 1-Real.exp (-(h*v))
  let β := 1-Real.exp (-(h*d))
  let ell := 1-Real.exp (-u)
  let r := 1-upperTailSlope h d*upperTailRatio h u
  let W := r^2 + upperTailLinearError h u d + upperTailQuadratic h u d
  let base := upperTailBaseFactor p u d
  let Num := DimThree.defect p a x 1 -
    Real.sqrt (DimThree.defect p a a 1 * DimThree.defect p x x 1)
  let Lo := DimThree.defect p a x x
  let Hi := DimThree.defect p a 1 1
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp [h]; positivity
  have hd₀ : 0 < d := by linarith
  have hv : 0 < v := by dsimp [v]; positivity
  have hn : 0 < n := by dsimp [n]; positivity
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Nat.choose_pos (show 2 ≤ p+2 by omega))
  have ha : 0 < a := Real.exp_pos _
  have hx : 0 < x := Real.exp_pos _
  have hax : a < x := by
    apply Real.exp_lt_exp.mpr
    exact (div_lt_div_iff_of_pos_right hpR).mpr (by dsimp [v]; linarith)
  have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr hd₀) hpR)
  have ha1 : a < 1 := hax.trans hx1
  have hα : 0 < α := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh hv)))
  have hβ : 0 < β := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh hd₀)))
  have hα' : 1-a^3 = α := by rw [show a^3 = _ from (tail_cube_pow hp₀ v).1]
  have hβ' : 1-x^3 = β := by rw [show x^3 = _ from (tail_cube_pow hp₀ d).1]
  have hLo : Lo = N*Real.exp (-(3*d+u))*C := upperTail_lower_weight hp₀ u d
  have hHi_mul : α*Hi = n*A := by
    rw [← hα']
    exact upperTail_upper_weight hp₀ hv
  have hHi : Hi = n*A/α := (eq_div_iff hα.ne').mpr (by linarith only [hHi_mul])
  have hC : 0 < C := by
    have hl : 0 < Lo := weight_pos hp₀ ha.le hax
    rw [hLo] at hl
    exact (mul_pos_iff_of_pos_left (mul_pos hN (Real.exp_pos _))).mp hl
  have hA : 0 < A := by
    have hh' : 0 < α*Hi := mul_pos hα (weight_pos hp₀ ha.le ha1)
    rw [hHi_mul] at hh'
    exact (mul_pos_iff_of_pos_left hn).mp hh'
  have hCoord : logCoordinate p a x = u := by
    dsimp only [a, x]
    rw [tail_logCoordinate hp₀]
    dsimp [v]
    ring
  have hCoord' : logCoordinate p a 1 = v := by
    rw [show (1 : ℝ) = Real.exp (-(0 : ℝ)/(p : ℝ)) by simp]
    exact (tail_logCoordinate hp₀ v 0).trans (sub_zero _)
  have hKernel : Num/Real.sqrt (Lo*Hi) = logKernel p u v := by
    have hk := upperKernel_div_weights_eq_logKernel hp₀ ha hax ha1
    rw [min_eq_left hx1.le, max_eq_right hx1.le, hCoord, hCoord'] at hk
    simpa only [ExtremeWalk.upperKernel, Num, Lo, Hi, min_eq_left hx1.le, max_eq_right hx1.le] using hk
  have hNum : α*β*Num = N*β^2*Real.exp (-(2*d))*ell^2/2*W := by
    have hD := upperTail_numerator_decomposition hp hu hd
    change (1-a^3)*(1-x^3)*Num =
      ((3+h)*(3+2*h)/2)*(upperTailGap h d)^2*Real.exp (-(2*d))*ell^2/2*W at hD
    rw [hα', hβ'] at hD
    rw [hD, show β = h*upperTailGap h d from tail_gap_factor hh]
    have hs : N*h^2 = (3+h)*(3+2*h)/2 := tail_choose_scale hp₀
    linear_combination -(upperTailGap h d)^2*Real.exp (-(2*d))*ell^2/2*W*hs
  have hExp : Real.exp (-(3*d+u)) = (Real.exp (-(3*d+u)/2))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hSq : Real.sqrt (Lo*Hi) =
      Real.sqrt N*Real.sqrt n*Real.sqrt C*Real.sqrt A*Real.exp (-(3*d+u)/2)/Real.sqrt α := by
    rw [hLo, hHi]
    rw [show N*Real.exp (-(3*d+u))*C*(n*A/α) =
      (N*(n*(C*(A*Real.exp (-(3*d+u))))))/α by ring]
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hN.le, Real.sqrt_mul hn.le,
      Real.sqrt_mul hC.le, Real.sqrt_mul hA.le, hExp, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
    ring
  have hExp' : Real.exp (-(2*d)) =
      Real.exp (-(3*d+u)/2)*Real.exp (-d/2)*Real.exp (u/2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  dsimp only
  change logKernel p u v = (1/Real.sqrt A)*base*W
  rw [← hKernel]
  have hs : α*β ≠ 0 := (mul_pos hα hβ).ne'
  have hNum' : Num = (N*β^2*Real.exp (-(2*d))*ell^2/2*W)/(α*β) :=
    (eq_div_iff hs).mpr (by rwa [mul_comm Num])
  rw [hNum', hSq, hExp']
  change _ =
    (1/Real.sqrt A)*(Real.sqrt (N/n)/2*Real.exp (-d/2)*
      (β/Real.sqrt α)*(Real.exp (u/2)*ell^2/Real.sqrt C))*W
  rw [Real.sqrt_div hN.le, ← Real.sq_sqrt hN.le, ← Real.sq_sqrt hα.le]
  field_simp [(Real.sqrt_pos.mpr hN).ne', (Real.sqrt_pos.mpr hn).ne',
    (Real.sqrt_pos.mpr hα).ne', (Real.sqrt_pos.mpr hA).ne', (Real.sqrt_pos.mpr hC).ne',
    hβ.ne', (Real.exp_pos (-(3*d+u)/2)).ne']
  simp only [Real.sqrt_sq (Real.sqrt_nonneg N), Real.sqrt_sq (Real.sqrt_nonneg α)]
  ring

#print axioms upperTail_distinct_nodes
#print axioms upperTail_repeated_nodes
#print axioms upperTail_linear_correction
#print axioms upperTail_defect_numerator
#print axioms upperTail_numerator_decomposition
#print axioms upperTail_lower_weight
#print axioms upperTail_upper_weight
#print axioms upperTail_logKernel_decomposition

end RefinedBMV.PositiveCenter
