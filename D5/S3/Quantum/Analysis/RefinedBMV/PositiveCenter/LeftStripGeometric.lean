/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripGeometric
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One-sided finite geometric reduction of the exact left-strip weighted derivative. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripCollision

/-! The finite geometric correction and its endpoint bound for the left strip. -/

open Filter Set
open scoped BigOperators Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

open DividedDifference (homogeneousThree clear_distinct clear_repeat_first clear_repeat_last)

open private leftStripS leftStripE leftStripExpMoment leftStripReflectedSlope
  leftStrip_hasDerivAt_expMoment_left leftStrip_hasDerivAt_moment_left leftStrip_weightedThird_eq
  leftStrip_small_slope leftStrip_contDiffAt_S leftStrip_hasDerivAt_exp_sum
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripCollision
open private weightedThird leftStrip_logKernel_mixed_lt_of_weighted
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripKernel

open private hasDerivAt_negativeMarginal negativeMarginalDerivative compositionMoment_zero_zero
  exponent gapCount from D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftLimit

private abbrev spacing (p : ℕ) : ℝ := 3 / (p : ℝ)

private abbrev geometricScale (h : ℝ) : ℝ := (3+h)*(3+2*h)/2

private theorem spacing_pos {p : ℕ} (hp : 0 < p) : 0 < spacing p := by
  have : 0 < (p : ℝ) := by exact_mod_cast hp
  positivity

private theorem spacing_mul {p : ℕ} (hp : 0 < p) : spacing p * (p : ℝ) = 3 := by
  exact div_mul_cancel₀ _ (by exact_mod_cast hp.ne')

private def geometricProfile (h q scale t : ℝ) : ℝ :=
  Real.exp (logReciprocalGap h t - q*t) / scale

private abbrev f (h : ℝ) := geometricProfile h 0 (Real.sqrt (geometricScale h))
private abbrev H (h : ℝ) := geometricProfile h (3+2*h) 1

private theorem geometricProfile_eq {h t : ℝ} (hh : 0 < h) (ht : 0 < t) (q scale : ℝ) :
    geometricProfile h q scale t = Real.exp ((1-q)*t) / (scale*upperTailGap h t) := by
  unfold geometricProfile logReciprocalGap
  rw [show t-Real.log (upperTailGap h t)-q*t = (1-q)*t-Real.log (upperTailGap h t) by ring,
    Real.exp_sub, Real.exp_log (tail_gap_pos hh ht), div_div, mul_comm (upperTailGap h t)]

private theorem hasDerivAt_geometricProfile {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    (q scale : ℝ) :
    HasDerivAt (geometricProfile h q scale)
      (geometricProfile h q scale t * (profileSlope h t-q)) t := by
  unfold geometricProfile
  change HasDerivAt (fun x ↦ Real.exp (logReciprocalGap h x-q*x)/scale) _ t
  simpa only [mul_div_right_comm, Pi.sub_apply] using
    (((hasDerivAt_logReciprocalGap hh ht).sub (hasDerivAt_const_mul q)).exp.div_const scale)

private def profileSecond (h q t : ℝ) : ℝ :=
  (profileSlope h t-q)^2 + profileCurvature h t

private def profileThird (h q t : ℝ) : ℝ :=
  (profileSlope h t-q)^3 + 3*(profileSlope h t-q)*profileCurvature h t -
    profileCurvature h t*(h+2*upperTailSlope h t)

private theorem hasDerivAt_profileFirst {h t : ℝ} (hh : 0 < h) (ht : 0 < t) (q scale : ℝ) :
    HasDerivAt (fun x ↦ geometricProfile h q scale x * (profileSlope h x-q))
      (geometricProfile h q scale t * profileSecond h q t) t := by
  convert (hasDerivAt_geometricProfile hh ht q scale).mul
    ((hasDerivAt_profileSlope hh ht).sub_const q) using 1
  unfold profileSecond
  ring

private theorem hasDerivAt_profileSecond {h t : ℝ} (hh : 0 < h) (ht : 0 < t) (q scale : ℝ) :
    HasDerivAt (fun x ↦ geometricProfile h q scale x * profileSecond h q x)
      (geometricProfile h q scale t * profileThird h q t) t := by
  convert (hasDerivAt_geometricProfile hh ht q scale).mul
    ((((hasDerivAt_profileSlope hh ht).sub_const q).pow 2).add
      (hasDerivAt_profileCurvature hh ht)) using 1
  · rfl
  · simp only [profileThird, Pi.pow_apply, Pi.add_apply,
      Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring

private def geometricSum (p : ℕ) (a : ℝ) : ℝ :=
  spacing p * ∑ j ∈ Finset.range (p+2), Real.exp (-(spacing p*(j : ℝ)*a))

/-- The finite correction in the second partial in the first coordinate. -/
def leftStripGeometricG (p : ℕ) (a : ℝ) : ℝ :=
  let h := spacing p
  h * ∑ j ∈ Finset.range (p+2), (2+h-h*(j : ℝ))^2 * Real.exp (-(h*(j : ℝ)*a))

private def shiftedSum (p i : ℕ) (a : ℝ) : ℝ :=
  let h := spacing p
  h * ∑ j ∈ Finset.range (p+2), (2+h-h*(j : ℝ))^i * Real.exp ((2+h-h*(j : ℝ))*a)

private theorem hasDerivAt_shiftedSum (p i : ℕ) (a : ℝ) :
    HasDerivAt (shiftedSum p i) (shiftedSum p (i+1) a) a := by
  unfold shiftedSum
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro j _
  let r := 2+spacing p-spacing p*(j : ℝ)
  convert ((hasDerivAt_const_mul r (x := a)).exp.const_mul (r^i)) using 1
  rw [pow_succ]
  ring

private theorem shiftedSum_zero (p : ℕ) (a : ℝ) :
    shiftedSum p 0 a = Real.exp ((2+spacing p)*a)*geometricSum p a := by
  unfold shiftedSum geometricSum
  rw [mul_left_comm (Real.exp _), Finset.mul_sum (a := Real.exp _)]
  apply congrArg (fun z : ℝ ↦ spacing p*z)
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_zero, one_mul, ← Real.exp_add]
  congr 1
  ring

private theorem shiftedSum_two (p : ℕ) (a : ℝ) :
    shiftedSum p 2 a = Real.exp ((2+spacing p)*a)*leftStripGeometricG p a := by
  unfold shiftedSum leftStripGeometricG
  rw [mul_left_comm (Real.exp _), Finset.mul_sum (a := Real.exp _)]
  apply congrArg (fun z : ℝ ↦ spacing p*z)
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_left_comm, ← Real.exp_add]
  congr 2
  ring

private theorem sum_range_cast (n : ℕ) :
    (∑ j ∈ Finset.range n, (j : ℝ)) = (n : ℝ)*((n : ℝ)-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Nat.cast_succ]; ring

private theorem sum_range_cast_sq (n : ℕ) :
    (∑ j ∈ Finset.range n, (j : ℝ)^2) = (n : ℝ)*((n : ℝ)-1)*(2*(n : ℝ)-1)/6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Nat.cast_succ]; ring

private def geometricGEndpoint (h : ℝ) : ℝ := (h+1)*(h+2)*(2*h+3)/2

/-- The endpoint value of the finite second-partial correction. -/
theorem leftStripGeometricG_zero {p : ℕ} (hp : 0 < p) :
    leftStripGeometricG p 0 = geometricGEndpoint (spacing p) := by
  let h := spacing p
  let k := 2+h
  have hsum :
      (∑ j ∈ Finset.range (p+2), (k-h*(j : ℝ))^2) =
        ((p : ℝ)+2)*k^2 - 2*k*h*(((p : ℝ)+2)*((p : ℝ)+1)/2) +
          h^2*(((p : ℝ)+2)*((p : ℝ)+1)*(2*(p : ℝ)+3)/6) := by
    simp_rw [show ∀ z : ℝ, (k-h*z)^2 = k^2 - (2*k*h)*z + h^2*z^2 by intro z; ring,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_range_cast,
      sum_range_cast_sq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  change h * (∑ j ∈ Finset.range (p+2), (k-h*(j : ℝ))^2 *
      Real.exp (-(h*(j : ℝ)*0))) = _
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
  rw [hsum]
  calc
    _ = (h*(p : ℝ)+2*h) *
        (k^2-k*(h*(p : ℝ)+h)+(h*(p : ℝ)+h)*(2*(h*(p : ℝ))+3*h)/6) := by ring
    _ = _ := by
      rw [show h*(p : ℝ) = 3 from spacing_mul hp]
      unfold geometricGEndpoint
      dsimp [k]
      ring

private theorem geometricG_le_zero_value {p : ℕ} (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) :
    leftStripGeometricG p a ≤ leftStripGeometricG p 0 := by
  unfold leftStripGeometricG
  apply mul_le_mul_of_nonneg_left _ (spacing_pos hp).le
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  simpa only [mul_zero, neg_zero, neg_nonpos] using
    mul_nonneg (mul_nonneg (spacing_pos hp).le (Nat.cast_nonneg j)) ha

/-- The divided difference after removing the two denominators of the finite triangle. -/
private theorem geometric_homogeneous (p : ℕ) (r x : ℝ) :
    (1-r*x)*(1-r)*homogeneousThree p (r*x) r 1 =
      1-r^(p+2)-(1-r)*r^(p+1)*(∑ j ∈ Finset.range (p+2), x^j) := by
  by_cases hx : x = 1
  · subst x
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← pow_two, clear_repeat_first, one_pow, mul_one, pow_succ r (p+1)]
    push_cast
    ring
  by_cases hr : r = 0
  · subst r
    simp [homogeneousThree, DividedDifference.homogeneousTwo, Finset.sum_range_succ',
      zero_pow (Nat.succ_ne_zero _)]
  apply mul_right_cancel₀ (mul_ne_zero hr (sub_ne_zero.mpr (Ne.symm hx)))
  have hd := clear_distinct p (r*x) r (1 : ℝ)
  simp only [one_pow, mul_one, mul_pow] at hd
  have hs := geom_sum_mul_neg x (p+2)
  rw [show r^(p+2) = r^(p+1)*r from pow_succ _ _] at hd ⊢
  linear_combination hd + (1-r)*(r^(p+1)*r)*hs

private theorem scaled_moment {p : ℕ} (hp : 0 < p) (v w : ℝ) :
    geometricScale (spacing p) * upperTailGap (spacing p) v * upperTailGap (spacing p) w *
      Real.exp (-(v+w)) * (compositionMoment p (v-w) v+1) =
    (1-Real.exp (-(spacing p*v)))*(1-Real.exp (-(spacing p*w))) *
      homogeneousThree p (Real.exp (-(spacing p*v))) (Real.exp (-(spacing p*w))) 1 := by
  let x (t : ℝ) := Real.exp (-t/(p : ℝ))
  have hx (t : ℝ) : (x t)^3 = Real.exp (-(spacing p*t)) := (tail_cube_pow hp t).1
  have hxp (t : ℝ) : (x t)^p = Real.exp (-t) := (tail_cube_pow hp t).2
  have hcoord : logCoordinate p (x v) 1 = v := by
    simpa only [neg_zero, zero_div, Real.exp_zero, sub_zero, x] using tail_logCoordinate hp v 0
  have h := defect_eq_compositionMoment hp (Real.exp_pos (-v/(p : ℝ)))
    (Real.exp_pos (-w/(p : ℝ))) zero_lt_one
  change DimThree.defect p (x v) (x w) 1 = _ at h
  rw [DividedDifference.defect_eq_homogeneous, DimThree.gaps_length_eq_choose,
    tail_logCoordinate hp v w, hcoord, hx, hx, one_pow, mul_one, mul_pow, hxp, hxp,
    ← Real.exp_add, ← neg_add] at h
  have hscale : ((p+2).choose 2 : ℝ)*spacing p^2 = geometricScale (spacing p) :=
    tail_choose_scale hp
  rw [tail_gap_factor (spacing_pos hp), tail_gap_factor (spacing_pos hp),
    ← hscale, show homogeneousThree p (Real.exp (-(spacing p*v)))
      (Real.exp (-(spacing p*w))) 1 = ((p+2).choose 2 : ℝ)*Real.exp (-(v+w)) *
        (compositionMoment p (v-w) v+1) by linarith only [h]]
  ring

private theorem geometric_moment {p : ℕ} (hp : 0 < p) {a v : ℝ} (hv : 0 < v)
    (hav : a < v) :
    let h := spacing p
    let w := v-a
    compositionMoment p a v+1 = f h v *
      (f h w - (H h w+Real.exp (-((2+h)*w))*geometricSum p a) /
        Real.sqrt (geometricScale h)) := by
  let h := spacing p
  let w := v-a
  let c := geometricScale h
  let F := upperTailGap h
  let r := Real.exp (-(h*w))
  let x := Real.exp (-(h*a))
  have hh := spacing_pos hp
  have hw := sub_pos.mpr hav
  have hc : 0 < c := by dsimp [c, geometricScale]; positivity
  have hs := Real.sq_sqrt hc.le
  have hcv := tail_gap_pos hh hv
  have hcw := tail_gap_pos hh hw
  have hprod : Real.exp (-(h*v)) = r*x := by
    rw [← Real.exp_add]
    congr 1
    dsimp [r, x, w]
    ring
  have hsum : (∑ j ∈ Finset.range (p+2), x^j) =
      ∑ j ∈ Finset.range (p+2), Real.exp (-(h*(j : ℝ)*a)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hpow (i : ℕ) : r^(p+i) = Real.exp (-((3+(i : ℝ)*h)*w)) := by
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    linear_combination -w*(spacing_mul hp)
  have hM := scaled_moment hp v w
  rw [show v-w = a by dsimp [w]; ring, hprod, geometric_homogeneous, hpow, hpow, hsum] at hM
  have hgap : 1-r = h*F w := tail_gap_factor hh
  have hm : c*F v*F w*Real.exp (-(v+w))*(compositionMoment p a v+1) =
      1-Real.exp (-((3+2*h)*w))-F w*Real.exp (-((3+h)*w))*geometricSum p a := by
    rw [hgap] at hM
    norm_num only [Nat.cast_ofNat, Nat.cast_one, one_mul] at hM
    unfold geometricSum
    change _ = _ at hM
    linear_combination hM
  change _ = f h v * (f h w - (H h w+Real.exp (-((2+h)*w))*geometricSum p a) /
    Real.sqrt c)
  rw [show f h v = _ from geometricProfile_eq hh hv 0 _,
    show f h w = _ from geometricProfile_eq hh hw 0 _,
    show H h w = _ from geometricProfile_eq hh hw _ 1]
  simp only [sub_zero, one_mul]
  have he₀ : Real.exp (-(v+w))*Real.exp v*Real.exp w = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, show -(v+w)+v+w = 0 by ring, Real.exp_zero]
  have he₁ : Real.exp (-(v+w))*Real.exp v*Real.exp ((1-(3+2*h))*w) =
      Real.exp (-((3+2*h)*w)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have he₂ : Real.exp (-(v+w))*Real.exp v*Real.exp (-((2+h)*w)) =
      Real.exp (-((3+h)*w)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hFv : 0 < F v := hcv
  have hFw : 0 < F w := hcw
  have hs' := Real.sqrt_pos.mpr hc
  have hd : 0 < c*F v*F w*Real.exp (-(v+w)) := by positivity
  apply mul_left_cancel₀ hd.ne'
  rw [hm]
  change _ = c*F v*F w*Real.exp (-(v+w)) *
    (Real.exp v/(Real.sqrt c*F v) *
      (Real.exp w/(Real.sqrt c*F w) -
        (Real.exp ((1-(3+2*h))*w)/F w+
          Real.exp (-((2+h)*w))*geometricSum p a)/Real.sqrt c))
  conv_rhs =>
    congr
    · rw [← hs]
  have hr (s x y d X Y Z G : ℝ) (hs : s ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
      s^2*x*y*d*(X/(s*x)*(Y/(s*y)-(Z/y+G)/s)) =
        d*X*Y-d*X*Z-y*(d*X*G) := by
    field_simp
    ring
  rw [hr _ _ _ _ _ _ _ _ hs'.ne' hFv.ne' hFw.ne', he₀, he₁, ← mul_assoc
    (Real.exp (-(v+w))*Real.exp v) (Real.exp (-((2+h)*w))) (geometricSum p a), he₂]
  ring

private theorem hasDerivAt_decay (r t : ℝ) :
    HasDerivAt (fun x ↦ Real.exp (-(r*x))) (-r*Real.exp (-(r*t))) t := by
  simpa only [Pi.neg_apply, mul_comm] using (hasDerivAt_const_mul r (x := t)).neg.exp

private theorem geometric_second_moment {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    let h := spacing p
    let w := v-a
    leftStripExpMoment p 2 0 a v = f h v *
      (f h w*profileSecond h 0 w -
        (H h w*profileSecond h (3+2*h) w +
          Real.exp (-((2+h)*w))*leftStripGeometricG p a) / Real.sqrt (geometricScale h)) := by
  let h := spacing p
  let k := 2+h
  let c := Real.sqrt (geometricScale h)
  let A (t : ℝ) := f h (v-t) - (H h (v-t)+Real.exp (-(k*v))*shiftedSum p 0 t)/c
  have hh := spacing_pos hp
  have hgap (t : ℝ) : HasDerivAt (fun x : ℝ ↦ v-x) (-1) t :=
    (hasDerivAt_id' t).const_sub v
  have he (t : ℝ) (ht : t < v) : compositionMoment p t v+1 = f h v*A t := by
    dsimp only [A]
    rw [shiftedSum_zero, ← mul_assoc, ← Real.exp_add,
      show -(k*v)+k*t = -(k*(v-t)) by ring]
    exact geometric_moment hp hv ht
  have hfirst (t : ℝ) (ht : t < v) : leftStripExpMoment p 1 0 t v = f h v *
      (-(f h (v-t)*(profileSlope h (v-t)-0)) -
        (-(H h (v-t)*(profileSlope h (v-t)-(3+2*h))) +
          Real.exp (-(k*v))*shiftedSum p 1 t)/c) := by
    have hnear : (fun x ↦ compositionMoment p x v+1) =ᶠ[𝓝 t] fun x ↦ f h v*A x := by
      filter_upwards [eventually_lt_nhds ht] with x hx using he x hx
    have hf := (hasDerivAt_geometricProfile hh (sub_pos.mpr ht) 0 c).comp t (hgap t)
    have hH := (hasDerivAt_geometricProfile hh (sub_pos.mpr ht) (3+2*h) 1).comp t (hgap t)
    have hsum := (hasDerivAt_shiftedSum p 0 t).const_mul (Real.exp (-(k*v)))
    have hd : HasDerivAt (fun x ↦ f h v*A x) _ t :=
      (hf.sub ((hH.add hsum).div_const c)).const_mul (f h v)
    rw [← ((leftStrip_hasDerivAt_moment_left p t v).add_const 1).deriv,
      hnear.deriv_eq, hd.deriv]
    simp only [mul_neg, mul_one, Nat.zero_add]
    rfl
  have hnear : (fun t ↦ leftStripExpMoment p 1 0 t v) =ᶠ[𝓝 a]
      (fun t ↦ f h v * (-(f h (v-t)*(profileSlope h (v-t)-0)) -
        (-(H h (v-t)*(profileSlope h (v-t)-(3+2*h))) +
          Real.exp (-(k*v))*shiftedSum p 1 t)/c)) := by
    filter_upwards [eventually_lt_nhds hav] with t ht using hfirst t ht
  have hf := ((hasDerivAt_profileFirst hh (sub_pos.mpr hav) 0 c).comp a (hgap a)).neg
  have hH := ((hasDerivAt_profileFirst hh (sub_pos.mpr hav) (3+2*h) 1).comp a (hgap a)).neg
  have hsum := (hasDerivAt_shiftedSum p 1 a).const_mul (Real.exp (-(k*v)))
  have hd := (hf.sub ((hH.add hsum).div_const c)).const_mul (f h v)
  have hd' : HasDerivAt (fun t ↦ f h v * (-(f h (v-t)*(profileSlope h (v-t)-0)) -
        (-(H h (v-t)*(profileSlope h (v-t)-(3+2*h))) +
          Real.exp (-(k*v))*shiftedSum p 1 t)/c)) _ a := hd
  rw [← (leftStrip_hasDerivAt_expMoment_left p 1 0 a v).deriv, hnear.deriv_eq, hd'.deriv]
  simp only [mul_neg, mul_one, neg_neg]
  rw [shiftedSum_two, ← mul_assoc, ← Real.exp_add, show -(k*v)+k*a = -(k*(v-a)) by ring]

private def negativeMarginalFactor (h t : ℝ) : ℝ :=
  Real.exp (-((3+2*h)*t))-1+(3+2*h)*upperTailGap h t -
    geometricScale h*upperTailGap h t^2*Real.exp (-t)

private theorem negative_marginal_eq {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let h := spacing p
    geometricScale h*upperTailGap h t^2*Real.exp (-t)*compositionMoment p 0 (-t) =
      negativeMarginalFactor h t := by
  let h := spacing p
  let q := Real.exp (-(h*t))
  let x := Real.exp (-t/(p : ℝ))
  have hpow : q^(p+2) = Real.exp (-((3+2*h)*t)) := by
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    linear_combination -t*(spacing_mul hp)
  have hgap : 1-q = h*upperTailGap h t := tail_gap_factor (spacing_pos hp)
  have hx : x^3 = q := (tail_cube_pow hp t).1
  have hdef := upperTail_lower_weight hp t 0
  simp only [zero_add, neg_zero, zero_div, Real.exp_zero, mul_zero] at hdef
  change DimThree.defect p x 1 1 = _ at hdef
  rw [DividedDifference.defect_eq_homogeneous, hx, one_pow, mul_one, mul_one,
    show x^p = Real.exp (-t) from (tail_cube_pow hp t).2] at hdef
  have hclear := clear_repeat_last p q (1 : ℝ)
  simp only [one_pow] at hclear
  rw [hpow, hgap] at hclear
  have hq : q = 1-h*upperTailGap h t := by linarith only [hgap]
  have hscale := tail_choose_scale hp
  change ((p+2).choose 2 : ℝ)*h^2 = geometricScale h at hscale
  unfold negativeMarginalFactor
  calc
    _ = (h*upperTailGap h t)^2 *
        (((p+2).choose 2 : ℝ)*Real.exp (-t)*compositionMoment p 0 (-t)) := by
      rw [← hscale]
      ring
    _ = _ := by
      rw [← hdef]
      have hc' : (h*upperTailGap h t)^2*homogeneousThree p q 1 1 =
          Real.exp (-((3+2*h)*t))-1+((p : ℝ)+2)*h*upperTailGap h t := by
        linear_combination hclear - ((p : ℝ)+2)*hq
      linear_combination hc' + upperTailGap h t*(spacing_mul hp) -
        upperTailGap h t^2*Real.exp (-t)*hscale

private theorem negativeMarginalFactor_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    0 < negativeMarginalFactor (spacing p) t := by
  rw [← negative_marginal_eq hp]
  have hh := spacing_pos hp
  have hF := tail_gap_pos hh ht
  have hC := compositionMoment_marginal_pos hp (neg_ne_zero.mpr ht.ne')
  positivity

private theorem reflectedSlope_pos {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    0 < leftStripReflectedSlope p v := by
  let C (t : ℝ) := compositionMoment p 0 (-t)
  have hC := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne')
  have hD : ∀ t, HasDerivAt C (negativeMarginalDerivative p t) t :=
    hasDerivAt_negativeMarginal p
  have hderiv : 0 < negativeMarginalDerivative p v := by
    have hf' (t : ℝ) : HasDerivAt (negativeMarginalDerivative p)
        (((DimThree.gaps p).map fun g ↦ (-exponent p g.2.2)^2 *
          Real.exp (-exponent p g.2.2*t)).sum / gapCount p) t := by
      have hd := (leftStrip_hasDerivAt_exp_sum (DimThree.gaps p)
        (fun g ↦ -exponent p g.2.2) (fun g ↦ -exponent p g.2.2) (fun _ ↦ 0) t).div_const
        (gapCount p)
      simp only [add_zero, ← sq] at hd
      exact hd
    have hconv : ConvexOn ℝ univ C := by
      apply convexOn_of_deriv2_nonneg' convex_univ
        (fun t _ ↦ (hD t).differentiableAt.differentiableWithinAt)
      · rw [show deriv C = negativeMarginalDerivative p from funext fun t ↦ (hD t).deriv]
        exact fun t _ ↦ (hf' t).differentiableAt.differentiableWithinAt
      · intro t _
        change 0 ≤ deriv (deriv C) t
        rw [show deriv C = negativeMarginalDerivative p from funext fun t ↦ (hD t).deriv,
          (hf' t).deriv]
        apply div_nonneg _ (by unfold gapCount; positivity)
        exact List.sum_nonneg fun r hr ↦ by
          obtain ⟨g, _, rfl⟩ := List.mem_map.mp hr
          positivity
    have hs := hconv.slope_le_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ v) hv (hD v)
    rw [slope_def_field, sub_zero, show C 0 = 0 by simpa [C] using compositionMoment_zero_zero p,
      sub_zero] at hs
    exact (div_pos hC hv).trans_le hs
  change 0 < deriv (fun t ↦ Real.sqrt (C t)) v / Real.sqrt (C v)
  rw [((hD v).sqrt hC.ne').deriv]
  positivity

private def positiveRadical (h t : ℝ) : ℝ := Real.sqrt (1-upperTailLambda h t)

private theorem positive_marginal_eq {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    leftStripS p t = f (spacing p) t*positiveRadical (spacing p) t := by
  let h := spacing p
  let c := geometricScale h
  let F := upperTailGap h
  have hh := spacing_pos hp
  have hc : 0 < c := by dsimp [c, geometricScale]; positivity
  have hF := tail_gap_pos hh ht
  have hm := scaled_moment hp t t
  rw [sub_self, ← pow_two] at hm
  rw [show _ = 1-upperTailRepeatCorrection (spacing p) t from upperTail_repeated_nodes hp t] at hm
  change c*F t*F t*Real.exp (-(t+t))*(compositionMoment p 0 t+1) = _ at hm
  rw [show -(t+t) = -(2*t) by ring] at hm
  have hs : 1-upperTailLambda (spacing p) t =
      (Real.sqrt c*F t*Real.exp (-t))^2*compositionMoment p 0 t := by
    unfold upperTailLambda
    unfold upperTailRepeatCorrection at hm
    rw [mul_pow, mul_pow, Real.sq_sqrt hc.le, ← Real.exp_nat_mul]
    norm_num
    change 1-((1+(3+spacing p)*F t)*Real.exp (-((3+spacing p)*t))+
      c*F t^2*Real.exp (-(2*t))) = _
    linear_combination -hm
  unfold positiveRadical
  rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
    show f h t = _ from geometricProfile_eq hh ht 0 _]
  have hcancel : Real.exp t/(Real.sqrt c*F t)*(Real.sqrt c*F t*Real.exp (-t)) = 1 := by
    rw [← mul_assoc, div_mul_cancel₀ _ (mul_pos (Real.sqrt_pos.mpr hc) hF).ne',
      ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simp only [sub_zero, one_mul]
  change Real.sqrt (compositionMoment p 0 t) = _
  rw [← mul_assoc, hcancel, one_mul]

private def geomE (p : ℕ) (g a v : ℝ) : ℝ :=
  let h := spacing p
  let w := v-a
  f h v*(f h w*profileSecond h 0 w -
    (H h w*profileSecond h (3+2*h) w + Real.exp (-((2+h)*w))*g) /
      Real.sqrt (geometricScale h)) -
    leftStripS p v*deriv (deriv (leftStripS p)) w

private theorem leftStripE_eq_geomE {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    leftStripE p a v = geomE p (leftStripGeometricG p a) a v := by
  rw [leftStripE, geometric_second_moment hp hv hav]
  rfl

private theorem hasDerivAt_geomE {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) (g : ℝ) :
    let h := spacing p
    let w := v-a
    let α := profileSlope h v
    let corr := Real.exp (-((2+h)*w))*g
    HasDerivAt (geomE p g a)
      (α*f h v*(f h w*profileSecond h 0 w -
          (H h w*profileSecond h (3+2*h) w+corr)/Real.sqrt (geometricScale h)) +
        f h v*(f h w*profileThird h 0 w -
          (H h w*profileThird h (3+2*h) w-(2+h)*corr)/Real.sqrt (geometricScale h)) -
        (deriv (leftStripS p) v*deriv (deriv (leftStripS p)) w +
          leftStripS p v*deriv (deriv (deriv (leftStripS p))) w)) v := by
  let h := spacing p
  have hS := (leftStrip_contDiffAt_S hp (sub_pos.mpr hav).ne').derivWithin
    (show (2 : WithTop ℕ∞)+1 ≤ 3 by decide) |>.derivWithin
    (show (1 : WithTop ℕ∞)+1 ≤ 2 by decide)
  have hf := hasDerivAt_geometricProfile (spacing_pos hp) hv 0 (Real.sqrt (geometricScale h))
  have hf2 := hasDerivAt_profileSecond (spacing_pos hp) (sub_pos.mpr hav) 0
    (Real.sqrt (geometricScale h))
  have hH2 := hasDerivAt_profileSecond (spacing_pos hp) (sub_pos.mpr hav) (3+2*h) 1
  have hdec := hasDerivAt_decay (2+h) (v-a)
  have hgap := (hasDerivAt_id' v).sub_const a
  have hSv := (leftStrip_contDiffAt_S hp hv.ne').differentiableAt (by decide)
  have hcorr := ((hH2.comp v hgap).add ((hdec.comp v hgap).mul_const g)).div_const
    (Real.sqrt (geometricScale h))
  have hd := (hf.mul ((hf2.comp v hgap).sub hcorr)).sub
    (hSv.hasDerivAt.mul ((hS.differentiableAt (by decide)).hasDerivAt.comp v hgap))
  have hd' : HasDerivAt (geomE p g a) _ v := hd
  apply hd'.congr_deriv
  simp only [Function.comp_apply, Pi.sub_apply, Pi.add_apply, sub_zero, mul_one]
  simp only [f, H, h]
  ring

private def endpointWeighted (p : ℕ) (a v : ℝ) : ℝ :=
  leftStripReflectedSlope p v * geomE p (geometricGEndpoint (spacing p)) a v -
    deriv (geomE p (geometricGEndpoint (spacing p)) a) v

private def correctionCoefficient (h a v : ℝ) : ℝ :=
  f h v * Real.exp (-((2+h)*(v-a))) / Real.sqrt (geometricScale h)

private theorem hasDerivAt_correctionCoefficient {h a v : ℝ} (hh : 0 < h) (hv : 0 < v) :
    HasDerivAt (correctionCoefficient h a)
      (correctionCoefficient h a v*(profileSlope h v-(2+h))) v := by
  have hgap := (hasDerivAt_id' v).sub_const a
  convert ((hasDerivAt_geometricProfile hh hv 0 (Real.sqrt (geometricScale h))).mul
    ((hasDerivAt_decay (2+h) (v-a)).comp v hgap)).div_const
      (Real.sqrt (geometricScale h)) using 1
  · rfl
  · simp only [correctionCoefficient, Function.comp_apply, sub_zero, mul_one]
    ring

/-- The exact change in the genuine weighted third derivative when the finite
second-partial correction is replaced by its value at the collision. -/
theorem leftStrip_geometric_endpoint_difference {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    let h := spacing p
    let γ := leftStripReflectedSlope p v
    let N (x y : ℝ) := compositionMoment p x y -
      Real.sqrt (compositionMoment p 0 y*compositionMoment p 0 (y-x));
    (-weightedThird N a v γ) - endpointWeighted p a v =
      correctionCoefficient h a v*(2+h+γ-profileSlope h v) *
        (geometricGEndpoint h-leftStripGeometricG p a) := by
  let h := spacing p
  let γ := leftStripReflectedSlope p v
  let δ := geometricGEndpoint h-leftStripGeometricG p a
  let W := geomE p (geometricGEndpoint h) a
  have he : leftStripE p a =ᶠ[𝓝 v] fun t ↦ W t+correctionCoefficient h a t*δ := by
    filter_upwards [eventually_gt_nhds hv, eventually_gt_nhds hav] with t ht hat
    rw [leftStripE_eq_geomE hp ht hat]
    unfold W geomE correctionCoefficient δ
    ring
  have hW := hasDerivAt_geomE hp hv hav (geometricGEndpoint h)
  have hweighted := leftStrip_weightedThird_eq (γ := γ) hp hv hav
  change weightedThird (fun x y ↦ compositionMoment p x y -
    Real.sqrt (compositionMoment p 0 y*compositionMoment p 0 (y-x))) a v γ = _ at hweighted
  dsimp only
  rw [hweighted]
  change -(deriv (leftStripE p a) v-γ*leftStripE p a v) -
    (γ*W v-deriv W v) = _
  have hD : HasDerivAt (fun t ↦ W t+correctionCoefficient h a t*δ)
      (deriv W v + correctionCoefficient h a v*(profileSlope h v-(2+h))*δ) v :=
    hW.differentiableAt.hasDerivAt.add
      ((hasDerivAt_correctionCoefficient (a := a) (spacing_pos hp) hv).mul_const δ)
  rw [he.deriv_eq, he.eq_of_nhds, hD.deriv]
  change -(deriv W v+correctionCoefficient h a v*(profileSlope h v-(2+h))*δ -
    γ*(W v+correctionCoefficient h a v*δ))-(γ*W v-deriv W v) =
      correctionCoefficient h a v*(2+h+γ-profileSlope h v)*δ
  ring

/-- Replacing the finite sum by its value at zero gives a lower bound for
the weighted derivative. This comparison also holds at the collision. -/
theorem leftStrip_geometric_endpoint_le {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (ha : 0 ≤ a) (hav : a < v) :
    let N (x y : ℝ) := compositionMoment p x y -
      Real.sqrt (compositionMoment p 0 y*compositionMoment p 0 (y-x))
    endpointWeighted p a v ≤ -weightedThird N a v (leftStripReflectedSlope p v) := by
  let h := spacing p
  have hv : 0 < v := ha.trans_lt hav
  have hh := spacing_pos hp
  have hgamma := reflectedSlope_pos hp hv
  have hs : profileSlope h v < 1 := by
    unfold profileSlope
    linarith only [(upperTailSlope_bounds hh hv).1]
  have hc : 0 < correctionCoefficient h a v := by
    simp only [correctionCoefficient, f, geometricProfile]
    positivity
  have hG : 0 ≤ geometricGEndpoint h-leftStripGeometricG p a := by
    rw [← leftStripGeometricG_zero hp]
    exact sub_nonneg.mpr (geometricG_le_zero_value hp ha)
  apply sub_nonneg.mp
  rw [leftStrip_geometric_endpoint_difference hp hv hav]
  exact mul_nonneg (mul_nonneg hc.le (by linarith)) hG

private theorem reflectedSlope_sub {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    let h := spacing p
    let V := negativeMarginalFactor h
    profileSlope h v-leftStripReflectedSlope p v = (V v-deriv V v)/(2*V v) := by
  let h := spacing p
  let F := upperTailGap h
  let c := geometricScale h
  let C (t : ℝ) := compositionMoment p 0 (-t)
  let K (t : ℝ) := c*F t^2*Real.exp (-t)
  let V := negativeMarginalFactor h
  have hh := spacing_pos hp
  have hvF := tail_gap_pos hh hv
  have hc := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne')
  have hK : 0 < K v := by dsimp [K, c, geometricScale]; positivity
  have hC := hasDerivAt_negativeMarginal p v
  have hs : leftStripReflectedSlope p v = negativeMarginalDerivative p v/(2*C v) := by
    unfold leftStripReflectedSlope
    rw [((hC.sqrt hc.ne')).deriv]
    have hroot : 0 < Real.sqrt (C v) := Real.sqrt_pos.mpr hc
    change negativeMarginalDerivative p v/(2*Real.sqrt (C v))/Real.sqrt (C v) = _
    rw [div_div, mul_assoc, ← sq, Real.sq_sqrt hc.le]
  have hrate := (div_eq_iff hvF.ne').mp (upperTailGap_logDeriv hh hv)
  rw [(hasDerivAt_upperTailGap hh).deriv] at hrate
  have hdK : HasDerivAt K (K v*(2*upperTailSlope h v-1)) v := by
    have hdec : HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (-1*Real.exp (-v)) v := by
      simpa only [one_mul] using hasDerivAt_decay 1 v
    have hd := (((hasDerivAt_upperTailGap hh (t := v)).pow 2).const_mul c).mul hdec
    change HasDerivAt K _ v at hd
    apply hd.congr_deriv
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, neg_mul, K, Pi.pow_apply]
    rw [hrate]
    change c*(2*F v*(upperTailSlope h v*F v))*Real.exp (-v) +
      c*F v^2*(-(1*Real.exp (-v))) = c*F v^2*Real.exp (-v)*(2*upperTailSlope h v-1)
    ring
  have he : V = fun t ↦ K t*C t := funext fun t ↦ (negative_marginal_eq hp t).symm
  change profileSlope h v-leftStripReflectedSlope p v = (V v-deriv V v)/(2*V v)
  have hd : HasDerivAt (fun t ↦ K t*C t)
      (K v*(2*upperTailSlope h v-1)*C v+K v*negativeMarginalDerivative p v) v := hdK.mul hC
  have hc' : C v ≠ 0 := hc.ne'
  rw [hs, he, hd.deriv]
  unfold profileSlope
  dsimp only
  field_simp [hc', hK.ne']
  ring

private def marginalFactorFirst (h t : ℝ) : ℝ :=
  let F := upperTailGap h t
  let e := Real.exp (-(h*t))
  let r := 3+2*h
  r*(e-Real.exp (-(r*t))) -
    geometricScale h*Real.exp (-t)*(2*F*e-F^2)

private theorem deriv_negativeMarginalFactor {h : ℝ} (hh : 0 < h) (t : ℝ) :
    deriv (negativeMarginalFactor h) t = marginalFactorFirst h t := by
  let c := geometricScale h
  let F := upperTailGap h
  let r := 3+2*h
  have hF := hasDerivAt_upperTailGap (t := t) hh
  have hdec : HasDerivAt (fun x : ℝ ↦ Real.exp (-x)) (-1*Real.exp (-t)) t := by
    simpa only [one_mul] using hasDerivAt_decay 1 t
  have hd := (((hasDerivAt_decay r t).sub_const 1).add (hF.const_mul r)).sub
    (((hF.pow 2).const_mul c).mul hdec)
  have hd' : HasDerivAt (negativeMarginalFactor h) _ t := hd
  rw [hd'.deriv]
  simp only [marginalFactorFirst, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
  dsimp only [F, r, c]
  ring

-- The radicand derivatives are factored using the same gap identity as upperTailLambda.
private def radicandJet (h t : ℝ) : ℝ × ℝ × ℝ :=
  let j := 1+h
  let F := upperTailGap h t
  let e := Real.exp (-(h*t))
  let E := Real.exp (-(j*t))
  let R := j*F-1+E
  let R₁ := j*(e-E)
  let R₂ := j*(-h*e+j*E)
  let K := F*R
  let K₁ := e*R+F*R₁
  let K₂ := (-h*e)*R+2*e*R₁+F*R₂
  let prefactor := 2*geometricScale h*Real.exp (-(2*t))
  (prefactor*K, prefactor*(K₁-2*K), prefactor*(K₂-4*K₁+4*K))

private theorem hasDerivAt_radicandJet {h : ℝ} (hh : 0 < h) (t : ℝ) :
    HasDerivAt (fun x ↦ 1-upperTailLambda h x) (radicandJet h t).1 t ∧
    HasDerivAt (fun x ↦ (radicandJet h x).1) (radicandJet h t).2.1 t ∧
    HasDerivAt (fun x ↦ (radicandJet h x).2.1) (radicandJet h t).2.2 t := by
  let j := 1+h
  let F := upperTailGap h
  let e (x : ℝ) := Real.exp (-(h*x))
  let E (x : ℝ) := Real.exp (-(j*x))
  let R (x : ℝ) := j*F x-1+E x
  let R₁ (x : ℝ) := j*(e x-E x)
  let R₂ (x : ℝ) := j*(-h*e x+j*E x)
  let K (x : ℝ) := F x*R x
  let K₁ (x : ℝ) := e x*R x+F x*R₁ x
  let K₂ (x : ℝ) := (-h*e x)*R x+2*e x*R₁ x+F x*R₂ x
  let c := 2*geometricScale h
  have hF := hasDerivAt_upperTailGap (t := t) hh
  have hR : HasDerivAt R (R₁ t) t := by
    apply (((hF.const_mul j).sub_const 1).add (hasDerivAt_decay j t)).congr_deriv
    change j*e t + -j*E t = j*(e t-E t)
    ring
  have hR₁ : HasDerivAt R₁ (R₂ t) t := by
    apply (((hasDerivAt_decay h t).sub (hasDerivAt_decay j t)).const_mul j).congr_deriv
    change j*(-h*e t - -j*E t) = j*(-h*e t+j*E t)
    ring
  have hK : HasDerivAt K (K₁ t) t := hF.mul hR
  have hK₁ : HasDerivAt K₁ (K₂ t) t := by
    apply (((hasDerivAt_decay h t).mul hR).add (hF.mul hR₁)).congr_deriv
    change (-h*e t)*R t+e t*R₁ t+(e t*R₁ t+F t*R₂ t) = _
    unfold K₂
    ring
  have hP := (hasDerivAt_decay 2 t).const_mul c
  refine ⟨?_, ?_, ?_⟩
  · have hd := (hasDerivAt_upperTailLambda (t := t) hh).const_sub 1
    apply hd.congr_deriv
    change -(-(3+h)*(3+2*h)*Real.exp (-(2*t))*F t*R t) =
      c*Real.exp (-(2*t))*K t
    unfold c geometricScale K
    ring
  · apply (hP.mul hK).congr_deriv
    change c*(-2*Real.exp (-(2*t)))*K t+
      c*Real.exp (-(2*t))*K₁ t = c*Real.exp (-(2*t))*(K₁ t-2*K t)
    ring
  · apply (hP.mul (hK₁.sub (hK.const_mul 2))).congr_deriv
    change c*(-2*Real.exp (-(2*t)))*(K₁ t-2*K t)+
      c*Real.exp (-(2*t))*(K₂ t-2*K₁ t) = c*Real.exp (-(2*t))*(K₂ t-4*K₁ t+4*K t)
    ring

private def radicalFirst (h t : ℝ) : ℝ :=
  (radicandJet h t).1/(2*positiveRadical h t)

private def radicalSecond (h t : ℝ) : ℝ :=
  ((radicandJet h t).2.1-2*radicalFirst h t^2)/(2*positiveRadical h t)

private def radicalThird (h t : ℝ) : ℝ :=
  ((radicandJet h t).2.2-6*radicalFirst h t*radicalSecond h t)/(2*positiveRadical h t)

private theorem hasDerivAt_positiveRadical {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let h := spacing p
    let b := positiveRadical h
    HasDerivAt b (radicalFirst h t) t ∧
    HasDerivAt (radicalFirst h) (radicalSecond h t) t ∧
    HasDerivAt (radicalSecond h) (radicalThird h t) t := by
  let h := spacing p
  let b := positiveRadical h
  have hh := spacing_pos hp
  have hf : 0 < f h t := by
    simp only [f, geometricProfile, geometricScale]
    positivity
  have hs : 0 < leftStripS p t := Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp ht.ne')
  rw [positive_marginal_eq hp ht] at hs
  have hb : 0 < b t := pos_of_mul_pos_right hs hf.le
  have hpos : 0 < 1-upperTailLambda h t := Real.sqrt_pos.mp hb
  have hden := (mul_pos zero_lt_two hb).ne'
  obtain ⟨hR, hR₁, hR₂⟩ := hasDerivAt_radicandJet hh t
  change HasDerivAt (fun x ↦ (radicandJet h x).1) (radicandJet h t).2.1 t at hR₁
  change HasDerivAt (fun x ↦ (radicandJet h x).2.1) (radicandJet h t).2.2 t at hR₂
  have hb₁ : HasDerivAt b (radicalFirst h t) t := hR.sqrt hpos.ne'
  have hn₁ : (radicandJet h t).1 = radicalFirst h t*(2*b t) :=
    (div_mul_cancel₀ _ hden).symm
  have hb₂ : HasDerivAt (radicalFirst h) (radicalSecond h t) t := by
    apply (hR₁.fun_div (hb₁.const_mul 2) hden).congr_deriv
    change _ = ((radicandJet h t).2.1-2*radicalFirst h t^2)/(2*b t)
    rw [hn₁]
    field_simp [hb.ne']
  have hn₂ : (radicandJet h t).2.1-2*radicalFirst h t^2 = radicalSecond h t*(2*b t) :=
    (div_mul_cancel₀ _ hden).symm
  refine ⟨hb₁, hb₂, ?_⟩
  apply ((hR₂.sub ((hb₂.pow 2).const_mul 2)).fun_div (hb₁.const_mul 2) hden).congr_deriv
  change _ = ((radicandJet h t).2.2-6*radicalFirst h t*radicalSecond h t)/(2*b t)
  simp only [Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [hn₂]
  field_simp [hb.ne']
  ring

private theorem positiveRadical_deriv_eq {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let h := spacing p
    let b := positiveRadical h
    deriv b t = radicalFirst h t ∧
    deriv (deriv b) t = radicalSecond h t ∧
    deriv (deriv (deriv b)) t = radicalThird h t := by
  let h := spacing p
  let b := positiveRadical h
  have h₁ {x : ℝ} (hx : 0 < x) : deriv b x = radicalFirst h x :=
    (hasDerivAt_positiveRadical hp hx).1.deriv
  have h₂ {x : ℝ} (hx : 0 < x) : deriv (deriv b) x = radicalSecond h x := by
    have he : deriv b =ᶠ[𝓝 x] radicalFirst h := by
      filter_upwards [eventually_gt_nhds hx] with y hy using h₁ hy
    rw [he.deriv_eq, (hasDerivAt_positiveRadical hp hx).2.1.deriv]
  refine ⟨h₁ ht, h₂ ht, ?_⟩
  have he : deriv (deriv b) =ᶠ[𝓝 t] radicalSecond h := by
    filter_upwards [eventually_gt_nhds ht] with y hy using h₂ hy
  rw [he.deriv_eq, (hasDerivAt_positiveRadical hp ht).2.2.deriv]

private def marginalSecond (h t : ℝ) : ℝ :=
  profileSecond h 0 t*positiveRadical h t +
    2*profileSlope h t*deriv (positiveRadical h) t +
    deriv (deriv (positiveRadical h)) t

private def marginalThird (h t : ℝ) : ℝ :=
  profileThird h 0 t*positiveRadical h t +
    3*profileSecond h 0 t*deriv (positiveRadical h) t +
    3*profileSlope h t*deriv (deriv (positiveRadical h)) t +
    deriv (deriv (deriv (positiveRadical h))) t

private theorem positive_marginal_derivatives {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let h := spacing p
    deriv (leftStripS p) t =
      f h t*(profileSlope h t*positiveRadical h t+deriv (positiveRadical h) t) ∧
    deriv (deriv (leftStripS p)) t = f h t*marginalSecond h t ∧
    deriv (deriv (deriv (leftStripS p))) t = f h t*marginalThird h t := by
  let h := spacing p
  let b := positiveRadical h
  let F := f h
  let c := Real.sqrt (geometricScale h)
  let α := profileSlope h
  have hh := spacing_pos hp
  have hb {x : ℝ} (hx : 0 < x) : ContDiffAt ℝ 3 b x := by
    have hf : 0 < F x := by
      simp only [F, f, geometricProfile, geometricScale]
      positivity
    have hs : 0 < leftStripS p x := Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp hx.ne')
    rw [positive_marginal_eq hp hx] at hs
    have hpos : 0 < 1-upperTailLambda h x :=
      Real.sqrt_pos.mp (pos_of_mul_pos_right hs hf.le)
    have hd : ContDiff ℝ 3 (fun t : ℝ ↦ 1-upperTailLambda h t) := by
      unfold upperTailLambda upperTailGap
      fun_prop
    exact hd.contDiffAt.sqrt hpos.ne'
  have hb₁ {x : ℝ} (hx : 0 < x) : HasDerivAt b (deriv b x) x :=
    ((hb hx).differentiableAt (by decide)).hasDerivAt
  have hb₂ {x : ℝ} (hx : 0 < x) : HasDerivAt (deriv b) (deriv (deriv b) x) x :=
    (((hb hx).derivWithin (show (2 : WithTop ℕ∞)+1 ≤ 3 by decide)).differentiableAt
      (by decide)).hasDerivAt
  have hb₃ {x : ℝ} (hx : 0 < x) :
      HasDerivAt (deriv (deriv b)) (deriv (deriv (deriv b)) x) x :=
    ((((hb hx).derivWithin (show (2 : WithTop ℕ∞)+1 ≤ 3 by decide)).derivWithin
      (show (1 : WithTop ℕ∞)+1 ≤ 2 by decide)).differentiableAt (by decide)).hasDerivAt
  have hs₁ {x : ℝ} (hx : 0 < x) :
      deriv (leftStripS p) x = (F x*(α x-0))*b x+F x*deriv b x := by
    have he : leftStripS p =ᶠ[𝓝 x] fun y ↦ F y*b y := by
      filter_upwards [eventually_gt_nhds hx] with y hy using positive_marginal_eq hp hy
    exact (((hasDerivAt_geometricProfile hh hx 0 c).mul (hb₁ hx)).congr_of_eventuallyEq he).deriv
  have hs₂ {x : ℝ} (hx : 0 < x) :
      deriv (deriv (leftStripS p)) x =
        (F x*profileSecond h 0 x)*b x+2*((F x*(α x-0))*deriv b x)+F x*deriv (deriv b) x := by
    have he : deriv (leftStripS p) =ᶠ[𝓝 x]
        fun y ↦ (F y*(α y-0))*b y+F y*deriv b y := by
      filter_upwards [eventually_gt_nhds hx] with y hy using hs₁ hy
    have hd := ((hasDerivAt_profileFirst hh hx 0 c).mul (hb₁ hx)).add
      ((hasDerivAt_geometricProfile hh hx 0 c).mul (hb₂ hx))
    have hd' : HasDerivAt (fun y ↦ F y*(α y-0)*b y+F y*deriv b y) _ x := hd
    rw [he.deriv_eq, hd'.deriv]
    simp only [F, h, α, c, f]
    ring
  have he : deriv (deriv (leftStripS p)) =ᶠ[𝓝 t]
      fun y ↦ (F y*profileSecond h 0 y)*b y+2*((F y*(α y-0))*deriv b y)+F y*deriv (deriv b) y := by
    filter_upwards [eventually_gt_nhds ht] with y hy using hs₂ hy
  refine ⟨?_, ?_, ?_⟩
  · rw [hs₁ ht]
    change _ = F t*(α t*b t+deriv b t)
    ring
  · rw [hs₂ ht]
    unfold marginalSecond
    change _ = F t*(profileSecond h 0 t*b t+2*α t*deriv b t+deriv (deriv b) t)
    ring
  · have hd := (((hasDerivAt_profileSecond hh ht 0 c).mul (hb₁ ht)).add
        (((hasDerivAt_profileFirst hh ht 0 c).mul (hb₂ ht)).const_mul 2)).add
        ((hasDerivAt_geometricProfile hh ht 0 c).mul (hb₃ ht))
    change HasDerivAt (fun y ↦ (F y*profileSecond h 0 y)*b y+
        2*((F y*(α y-0))*deriv b y)+F y*deriv (deriv b) y) _ t at hd
    rw [he.deriv_eq, hd.deriv]
    unfold marginalThird
    change _ = F t*(profileThird h 0 t*b t+3*profileSecond h 0 t*deriv b t+
      3*α t*deriv (deriv b) t+deriv (deriv (deriv b)) t)
    simp only [F, h, α, c, f]
    ring

/-- The denominator-cleared scalar expression for the endpoint comparison. -/
def leftStripGeometricScalar (h a w : ℝ) : ℝ :=
  let v := w+a
  let V := negativeMarginalFactor h v
  let A := V-marginalFactorFirst h v
  let b := positiveRadical h
  let r := 3+2*h
  let k := 2+h
  let B₂ := profileSecond h 0 w*b w+2*profileSlope h w*radicalFirst h w+radicalSecond h w
  let B₃ := profileThird h 0 w*b w+3*profileSecond h 0 w*radicalFirst h w+
    3*profileSlope h w*radicalSecond h w+radicalThird h w
  2*V*(b v*B₃+radicalFirst h v*B₂-profileThird h 0 w) +
    A*(b v*B₂-profileSecond h 0 w) +
    Real.exp (-(r*w))*(2*V*profileThird h r w+A*profileSecond h r w) +
    upperTailGap h w*Real.exp (-((3+h)*w))*(A-2*k*V)*geometricGEndpoint h

private theorem endpointWeighted_eq_scalar {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    let h := spacing p
    let w := v-a
    endpointWeighted p a v =
      f h v*f h w/(2*negativeMarginalFactor h v)*leftStripGeometricScalar h a w := by
  let h := spacing p
  let w := v-a
  let c := Real.sqrt (geometricScale h)
  let V := negativeMarginalFactor h
  let A := V v-deriv V v
  let γ := leftStripReflectedSlope p v
  let α := profileSlope h
  let r := 3+2*h
  let k := 2+h
  let b := positiveRadical h
  have hh := spacing_pos hp
  have hw := sub_pos.mpr hav
  have hV := negativeMarginalFactor_pos hp hv
  have hα := reflectedSlope_sub hp hv
  change α v-γ = A/(2*V v) at hα
  have hH : H h w/c = f h w*Real.exp (-(r*w)) := by
    change Real.exp (logReciprocalGap h w-r*w)/1/c =
      Real.exp (logReciprocalGap h w-0*w)/c*Real.exp (-(r*w))
    rw [div_one, zero_mul, sub_zero, Real.exp_sub, Real.exp_neg]
    ring
  have hG : Real.exp (-(k*w))/c =
      f h w*(upperTailGap h w*Real.exp (-((3+h)*w))) := by
    rw [show f h w = _ from geometricProfile_eq hh hw 0 c]
    simp only [sub_zero, one_mul]
    have hFw := tail_gap_pos hh hw
    have hc : 0 < c := by dsimp [c, geometricScale]; positivity
    have he : Real.exp w*Real.exp (-((3+h)*w)) = Real.exp (-(k*w)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [k]
      ring
    have hFw' : upperTailGap h w ≠ 0 := hFw.ne'
    change _ = Real.exp w/(c*upperTailGap h w)*
      (upperTailGap h w*Real.exp (-((3+h)*w)))
    calc
      _ = (Real.exp w*Real.exp (-((3+h)*w)))/c := by rw [he]
      _ = _ := by field_simp [hc.ne', hFw']
  unfold endpointWeighted
  rw [(hasDerivAt_geomE hp hv hav (geometricGEndpoint h)).deriv]
  unfold geomE
  dsimp only
  rw [positive_marginal_eq hp hv, (positive_marginal_derivatives hp hv).1,
    (positive_marginal_derivatives hp hw).2.1, (positive_marginal_derivatives hp hw).2.2]
  change _ = f h v*f h w/(2*V v)*leftStripGeometricScalar h a w
  unfold leftStripGeometricScalar
  rw [show w+a = v by dsimp [w]; ring]
  dsimp only
  have hr := positiveRadical_deriv_eq hp hw
  have hv' := (positiveRadical_deriv_eq hp hv).1
  rw [← show deriv V v = marginalFactorFirst h v from deriv_negativeMarginalFactor hh v,
    ← show deriv b v = radicalFirst h v from hv',
    ← show deriv b w = radicalFirst h w from hr.1,
    ← show deriv (deriv b) w = radicalSecond h w from hr.2.1,
    ← show deriv (deriv (deriv b)) w = radicalThird h w from hr.2.2]
  have hγ : γ = α v-A/(2*V v) := by linarith only [hα]
  have hcoeff := show leftStripReflectedSlope p v = _ from hγ
  rw [hcoeff]
  change _ = f h v*f h w/(2*V v)*
    (2*V v*(b v*marginalThird h w+deriv b v*marginalSecond h w-profileThird h 0 w) +
      A*(b v*marginalSecond h w-profileSecond h 0 w) +
      Real.exp (-(r*w))*(2*V v*profileThird h r w+A*profileSecond h r w) +
      upperTailGap h w*Real.exp (-((3+h)*w))*(A-2*k*V v)*geometricGEndpoint h)
  have hx2 : f h w*profileSecond h 0 w -
      (H h w*profileSecond h r w+Real.exp (-(k*w))*geometricGEndpoint h)/c =
      f h w*(profileSecond h 0 w-Real.exp (-(r*w))*profileSecond h r w-
        upperTailGap h w*Real.exp (-((3+h)*w))*geometricGEndpoint h) := by
    rw [add_div, mul_div_right_comm (H h w), mul_div_right_comm (Real.exp (-(k*w))), hH, hG]
    ring
  have hx3 : f h w*profileThird h 0 w -
      (H h w*profileThird h r w-k*(Real.exp (-(k*w))*geometricGEndpoint h))/c =
      f h w*(profileThird h 0 w-Real.exp (-(r*w))*profileThird h r w+
        k*upperTailGap h w*Real.exp (-((3+h)*w))*geometricGEndpoint h) := by
    rw [sub_div, mul_div_right_comm (H h w), mul_div_assoc,
      mul_div_right_comm (Real.exp (-(k*w))), hH, hG]
    ring
  change (α v-A/(2*V v))*(f h v*(f h w*profileSecond h 0 w -
      (H h w*profileSecond h r w+Real.exp (-(k*w))*geometricGEndpoint h)/c) -
      (f h v*b v)*(f h w*marginalSecond h w)) -
    (α v*f h v*(f h w*profileSecond h 0 w -
        (H h w*profileSecond h r w+Real.exp (-(k*w))*geometricGEndpoint h)/c) +
      f h v*(f h w*profileThird h 0 w -
        (H h w*profileThird h r w-k*(Real.exp (-(k*w))*geometricGEndpoint h))/c) -
      (f h v*(α v*b v+deriv b v)*(f h w*marginalSecond h w) +
        f h v*b v*(f h w*marginalThird h w))) = _
  rw [hx2, hx3]
  have hV' : V v ≠ 0 := hV.ne'
  field_simp [hV']
  ring

/-- The exact lower comparison, expressed entirely in scalar profiles. -/
theorem leftStrip_geometric_scalar_le {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (ha : 0 ≤ a) (hav : a < v) :
    let h := spacing p
    let w := v-a
    let N (x y : ℝ) := compositionMoment p x y -
      Real.sqrt (compositionMoment p 0 y*compositionMoment p 0 (y-x))
    f h v*f h w/(2*negativeMarginalFactor h v)*leftStripGeometricScalar h a w ≤
      -weightedThird N a v (leftStripReflectedSlope p v) := by
  dsimp only
  rw [← endpointWeighted_eq_scalar hp (ha.trans_lt hav) hav]
  exact leftStrip_geometric_endpoint_le hp ha hav

/-- A positive scalar certificate over the integration strip implies the mixed
derivative sign of the original kernel. -/
theorem leftStrip_logKernel_mixed_lt_of_geometric_scalar {p : ℕ} (hp : 11 ≤ p)
    {u v : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1 / 2) (huv : u < v)
    (hscalar : ∀ a ∈ Ioo 0 u, 0 < leftStripGeometricScalar (spacing p) a (v - a)) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  refine leftStrip_logKernel_mixed_lt_of_weighted hp₀ hu huv
    (leftStrip_small_slope hp hu hu₁) ?_
  dsimp only
  intro a ha
  have hav := ha.2.trans huv
  have hV := negativeMarginalFactor_pos hp₀ (hu.trans huv)
  have hh := spacing_pos hp₀
  have hfv : 0 < f (spacing p) v := by simp only [f, geometricProfile, geometricScale]; positivity
  have hfw : 0 < f (spacing p) (v-a) := by
    simp only [f, geometricProfile, geometricScale]
    positivity
  have hpos := mul_pos (div_pos (mul_pos hfv hfw) (mul_pos zero_lt_two hV)) (hscalar a ha)
  exact neg_pos.mp (hpos.trans_le (leftStrip_geometric_scalar_le hp₀ ha.1.le hav))

#print axioms leftStripGeometricG_zero
#print axioms leftStrip_geometric_endpoint_difference
#print axioms leftStrip_geometric_endpoint_le
#print axioms leftStrip_geometric_scalar_le
#print axioms leftStrip_logKernel_mixed_lt_of_geometric_scalar

end RefinedBMV.PositiveCenter
