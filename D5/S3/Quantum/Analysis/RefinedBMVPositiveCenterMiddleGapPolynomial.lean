/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterMiddleGapPolynomial
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial formulas for the two middle-gap inequalities. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMiddleGapRemainder

/-! # Polynomial inequalities controlling the compact part of the middle gap -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

private noncomputable def rootFiveFactor (x : ℝ) : ℝ := 1 / 2 + x * (1 / 8 + x *
  (1 / 16 + x * (5 / 128 + x * (7 / 256))))

private noncomputable def rootFiveDeriv (x : ℝ) : ℝ := 1 / 2 + x * (1 / 4 + x *
  (3 / 16 + x * (5 / 32 + x * (35 / 256))))

private noncomputable def rootFiveSecond (x : ℝ) : ℝ := 1 / 4 + x * (3 / 8 + x * (15 / 32 + x * (35 / 64)))

private theorem hasDerivAt_rootFive (x : ℝ) :
    HasDerivAt middleGapRootTaylorFive (rootFiveDeriv x) x := by
  have d := hasDerivAt_id' x
  have hd := ((((d.div_const 2).fun_add ((d.pow 2).div_const 8)).fun_add
      ((d.pow 3).div_const 16)).fun_add (((d.pow 4).const_mul 5).div_const 128)).fun_add
        (((d.pow 5).const_mul 7).div_const 256)
  refine hd.congr_deriv ?_
  dsimp [rootFiveDeriv]
  ring

private theorem hasDerivAt_rootFiveDeriv (x : ℝ) :
    HasDerivAt rootFiveDeriv (rootFiveSecond x) x := by
  have d := hasDerivAt_id' x
  have hd := (((d.const_mul (1 / 4)).fun_add ((d.pow 2).const_mul (3 / 16))).fun_add
      ((d.pow 3).const_mul (5 / 32))).fun_add ((d.pow 4).const_mul (35 / 256))
  convert hd.const_add (1 / 2) using 1
  · funext t
    dsimp [rootFiveDeriv]
    ring
  · dsimp [rootFiveSecond]
    ring

private noncomputable def lambdaFactored (h a rho y : ℝ) : ℝ :=
  y * rho * (1 + (3 + h) * a) + (3 + h) * (3 + 2 * h) / 2 * a ^ 2

private noncomputable def lambdaDerivFactored (h a rho y : ℝ) : ℝ :=
  (3 + h) * (3 + 2 * h) * a * (rho * (1 - y) - a)

private noncomputable def lambdaSecondFactored (h a rho y : ℝ) : ℝ :=
  (3 + h) * (3 + 2 * h) *
    (2 * a ^ 2 - a * rho + rho * (1 - y) * (rho - (3 + h) * a))

/-- The negative-slope margin after multiplication by its positive denominator. -/
noncomputable def middleGapSlopePolynomial (h t a rho y : ℝ) : ℝ :=
  let w := 4 + t
  let m := 3 / 2 + h
  let U := y ^ 2 * lambdaFactored h a rho y
  (-w) * ((3 / 2 * a - rho) * lambdaFactored h a rho y * rootFiveFactor U +
      a * lambdaDerivFactored h a rho y * rootFiveDeriv U + y * rho * (a * m + rho)) -
    (11 / 4 + 1 / 25000) * (m * w + 1) * (1 + a / 4) * a ^ 2 * y

/-- The curvature after multiplication by its positive denominator. -/
noncomputable def middleGapCurvaturePolynomial (h a rho y : ℝ) : ℝ :=
  let m := 3 / 2 + h
  let U := y ^ 2 * lambdaFactored h a rho y
  a ^ 2 * (rootFiveSecond U * y ^ 2 * (lambdaDerivFactored h a rho y) ^ 2 +
      rootFiveDeriv U * lambdaSecondFactored h a rho y) +
    a * (3 * a - 2 * rho) * rootFiveDeriv U * lambdaDerivFactored h a rho y +
    (9 / 4 * a ^ 2 - 3 * a * rho + 2 * rho ^ 2 + h * a * rho) *
      lambdaFactored h a rho y * rootFiveFactor U -
    y * rho * (a ^ 2 * m ^ 2 + (2 * m + h) * a * rho + 2 * rho ^ 2)

private theorem exp_decay_hasDerivAt (k t : ℝ) :
    HasDerivAt (fun x ↦ Real.exp (-(k * x))) (-k * Real.exp (-(k * t))) t := by
  have h := ((hasDerivAt_id' t).const_mul k).neg.exp
  convert h using 1
  simp [mul_comm]

private theorem gap_pos {h t : ℝ} (hh : 0 < h) (ht : 0 < t) : 0 < upperTailGap h t := by
  rw [expGapMean_eq hh]
  exact mul_pos ht (expGapMean_pos _ _)

private theorem middleGapLambda_jets {h : ℝ} (hh : 0 < h) (t : ℝ) :
    let a := upperTailGap h t
    let rho := Real.exp (-(h * t))
    let y := Real.exp (-t)
    upperTailLambda h t = y ^ 2 * lambdaFactored h a rho y ∧
      HasDerivAt (upperTailLambda h) (y ^ 2 * lambdaDerivFactored h a rho y) t ∧
      HasDerivAt (deriv (upperTailLambda h)) (y ^ 2 * lambdaSecondFactored h a rho y) t := by
  let a := upperTailGap h
  let rho : ℝ → ℝ := fun x ↦ Real.exp (-(h * x))
  let y : ℝ → ℝ := fun x ↦ Real.exp (-x)
  have rho_eq (x : ℝ) : rho x = 1 - h * a x := by
    dsimp [rho, a, upperTailGap]
    field_simp [hh.ne']
    ring
  have hexp (x : ℝ) : Real.exp (-((1 + h) * x)) = y x * rho x := by
    change _ = Real.exp (-x) * Real.exp (-(h * x))
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow (x : ℝ) : Real.exp (-(2 * x)) = y x ^ 2 := by
    change _ = Real.exp (-x) ^ 2
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hu (x : ℝ) : HasDerivAt (upperTailLambda h)
      (y x ^ 2 * lambdaDerivFactored h (a x) (rho x) (y x)) x := by
    refine (hasDerivAt_upperTailLambda hh).congr_deriv ?_
    rw [show Real.exp (-(2 * x)) = y x ^ 2 from hpow x, hexp x]
    unfold lambdaDerivFactored
    linear_combination (-((3 + h) * (3 + 2 * h) * a x * y x ^ 2)) * rho_eq x
  have hdu (x : ℝ) : deriv (upperTailLambda h) x =
      y x ^ 2 * lambdaDerivFactored h (a x) (rho x) (y x) := (hu x).deriv
  have ha : HasDerivAt a (rho t) t := hasDerivAt_upperTailGap hh
  have hr : HasDerivAt rho (-h * rho t) t := exp_decay_hasDerivAt h t
  have hy : HasDerivAt y (-y t) t := by simpa only [one_mul, neg_one_mul] using exp_decay_hasDerivAt 1 t
  refine ⟨?_, hu t, ?_⟩
  · unfold upperTailLambda lambdaFactored
    rw [show Real.exp (-((3 + h) * t)) = y t ^ 2 * (y t * rho t) by
      rw [← hpow, ← hexp, ← Real.exp_add]
      congr 1
      ring, hpow]
    ring
  · rw [show deriv (upperTailLambda h) =
        fun x ↦ y x ^ 2 * lambdaDerivFactored h (a x) (rho x) (y x) from funext hdu]
    have hu₁ := (ha.fun_mul ((hr.fun_mul (hy.const_sub 1)).fun_sub ha)).const_mul
      ((3 + h) * (3 + 2 * h))
    convert (hy.pow 2).fun_mul hu₁ using 1
    · funext x
      unfold lambdaDerivFactored
      simp only [Pi.pow_apply]
      ring
    · change y t ^ 2 * lambdaSecondFactored h (a t) (rho t) (y t) = _
      unfold lambdaSecondFactored
      simp only [Pi.pow_apply]
      ring

private theorem middleGapFifthOrder_jets {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    let a := upperTailGap h t
    let s := upperTailSlope h t
    let g := 3 + h
    let b := Real.exp (-(g * t))
    let U := upperTailLambda h t
    let P := middleGapRootTaylorFive U - b
    let q := 3 / 2 - s
    let P₁ := rootFiveDeriv U * deriv (upperTailLambda h) t + g * b
    let P₂ := rootFiveSecond U * (deriv (upperTailLambda h) t) ^ 2 +
      rootFiveDeriv U * deriv (deriv (upperTailLambda h)) t - g ^ 2 * b
    deriv (middleGapFifthOrder h) t = (Real.exp (3 * t / 2) / a) * (q * P + P₁) ∧
      deriv (deriv (middleGapFifthOrder h)) t =
        (Real.exp (3 * t / 2) / a) * (((q ^ 2 + s * (h + s)) * P) + 2 * q * P₁ + P₂) := by
  let g : ℝ := 3 + h
  let b : ℝ → ℝ := fun x ↦ Real.exp (-(g * x))
  let a := upperTailGap h
  let s := upperTailSlope h
  let e : ℝ → ℝ := fun x ↦ Real.exp (3 * x / 2)
  let K : ℝ → ℝ := fun x ↦ e x / a x
  let q : ℝ → ℝ := fun x ↦ 3 / 2 - s x
  let U := upperTailLambda h
  let P : ℝ → ℝ := fun x ↦ middleGapRootTaylorFive (U x) - b x
  let P₁ : ℝ → ℝ := fun x ↦ rootFiveDeriv (U x) * deriv U x + g * b x
  let P₂ : ℝ → ℝ := fun x ↦ rootFiveSecond (U x) * (deriv U x) ^ 2 +
    rootFiveDeriv (U x) * deriv (deriv U) x - g ^ 2 * b x
  have hb (x : ℝ) : HasDerivAt b (-g * b x) x := exp_decay_hasDerivAt g x
  have hK {x : ℝ} (hx : 0 < x) : HasDerivAt K (q x * K x) x := by
    have hE : HasDerivAt e (3 / 2 * e x) x := by
      have he := (((hasDerivAt_id' x).const_mul 3).div_const 2).exp
      convert he using 1
      simp [e, mul_comm]
    have hA := hasDerivAt_upperTailGap (t := x) hh
    have ha := gap_pos hh hx
    have hSlope := upperTailGap_logDeriv hh hx
    rw [hA.deriv] at hSlope
    refine (hE.fun_div hA ha.ne').congr_deriv ?_
    change _ = (3 / 2 - upperTailSlope h x) * (e x / upperTailGap h x)
    rw [← hSlope]
    field_simp [ha.ne']
  have hP (x : ℝ) : HasDerivAt P (P₁ x) x := by
    have hu := (middleGapLambda_jets hh x).2.1
    rw [← hu.deriv] at hu
    refine (((hasDerivAt_rootFive (U x)).comp x hu).fun_sub (hb x)).congr_deriv ?_
    dsimp [P₁]
    ring
  have hP₁ : HasDerivAt P₁ (P₂ t) t := by
    have hu := (middleGapLambda_jets hh t).2.1
    have huu := (middleGapLambda_jets hh t).2.2
    rw [← hu.deriv] at hu
    rw [← huu.deriv] at huu
    refine ((((hasDerivAt_rootFiveDeriv (U t)).comp t hu).fun_mul huu).fun_add
      ((hb t).const_mul g)).congr_deriv ?_
    dsimp [P₂, U]
    ring
  have hq : HasDerivAt q (s t * (h + s t)) t := by
    simpa only [neg_neg] using (hasDerivAt_upperTailSlope hh ht).const_sub (3 / 2)
  have hfirst {x : ℝ} (hx : 0 < x) :
      HasDerivAt (middleGapFifthOrder h) (K x * (q x * P x + P₁ x)) x := by
    refine ((hK hx).fun_mul (hP x)).congr_deriv ?_
    ring
  refine ⟨(hfirst ht).deriv, ?_⟩
  have he : deriv (middleGapFifthOrder h) =ᶠ[𝓝 t] fun x ↦ K x * (q x * P x + P₁ x) := by
    filter_upwards [eventually_gt_nhds ht] with x hx using (hfirst hx).deriv
  rw [he.deriv_eq]
  have hsecond := (hK ht).fun_mul ((hq.fun_mul (hP t)).fun_add hP₁)
  exact (hsecond.congr_deriv (by ring)).deriv

/-- Polynomial signs on the physical variables imply the two bounds on the fifth-order profile. -/
theorem middleGapFifthOrder_bounds_of_polynomial {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    (hs : 0 ≤ middleGapSlopePolynomial h t (upperTailGap h t) (Real.exp (-(h * t)))
      (Real.exp (-t)))
    (hc : 0 < middleGapCurvaturePolynomial h (upperTailGap h t) (Real.exp (-(h * t)))
      (Real.exp (-t))) :
    middleGapSlopeBudget h t ≤ -deriv (middleGapFifthOrder h) t ∧
      0 < deriv (deriv (middleGapFifthOrder h)) t := by
  let a := upperTailGap h t
  let rho := Real.exp (-(h * t))
  let y := Real.exp (-t)
  let E := Real.exp (3 * t / 2)
  let g : ℝ := 3 + h
  let w : ℝ := 4 + t
  let m : ℝ := 3 / 2 + h
  let U := upperTailLambda h t
  have ha : 0 < a := gap_pos hh ht
  have hw : 0 < w := by dsimp [w]; positivity
  have hy : 0 < y := Real.exp_pos _
  have hE : 0 < E := Real.exp_pos _
  have hr : upperTailSlope h t = rho / a := by
    rw [← upperTailGap_logDeriv hh ht, (hasDerivAt_upperTailGap hh).deriv]
  have hexp : Real.exp (-(g * t)) = y ^ 3 * rho := by
    dsimp [y, rho]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    push_cast
    congr 1
    dsimp [g]
    ring
  have hcE : Real.exp (-(3 * t / 2)) = E * y ^ 3 := by
    dsimp [E, y]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    push_cast
    congr 1
    ring
  have hCB : middleGapSlopeBudget h t =
      (11 / 4 + 1 / 25000) * (m + 1 / w) * (1 + a / 4) * (E * y ^ 3) := by
    unfold middleGapSlopeBudget
    rw [hcE]
  obtain ⟨hU, hU₁, hU₂⟩ := middleGapLambda_jets hh t
  obtain ⟨hG₁, hG₂⟩ := middleGapFifthOrder_jets hh ht
  change U = y ^ 2 * lambdaFactored h a rho y at hU
  change HasDerivAt (upperTailLambda h) (y ^ 2 * lambdaDerivFactored h a rho y) t at hU₁
  change HasDerivAt (deriv (upperTailLambda h)) (y ^ 2 * lambdaSecondFactored h a rho y) t at hU₂
  have hS : middleGapRootTaylorFive U = U * rootFiveFactor U := by
    unfold middleGapRootTaylorFive rootFiveFactor
    ring
  change deriv (middleGapFifthOrder h) t = E / a *
    ((3 / 2 - upperTailSlope h t) * (middleGapRootTaylorFive U - Real.exp (-(g * t))) +
      (rootFiveDeriv U * deriv (upperTailLambda h) t + g * Real.exp (-(g * t)))) at hG₁
  change deriv (deriv (middleGapFifthOrder h)) t = E / a *
    (((3 / 2 - upperTailSlope h t) ^ 2 + upperTailSlope h t * (h + upperTailSlope h t)) *
      (middleGapRootTaylorFive U - Real.exp (-(g * t))) +
      2 * (3 / 2 - upperTailSlope h t) *
        (rootFiveDeriv U * deriv (upperTailLambda h) t + g * Real.exp (-(g * t))) +
      (rootFiveSecond U * (deriv (upperTailLambda h) t) ^ 2 +
        rootFiveDeriv U * deriv (deriv (upperTailLambda h)) t - g ^ 2 * Real.exp (-(g * t)))) at hG₂
  have hsEq : w * a ^ 2 * (-deriv (middleGapFifthOrder h) t - middleGapSlopeBudget h t) =
      E * y ^ 2 * middleGapSlopePolynomial h t a rho y := by
    rw [hG₁, hCB, hr, hexp, hU₁.deriv, hS, hU]
    unfold middleGapSlopePolynomial
    dsimp only
    change _ = E * y ^ 2 * ((-w) * ((3 / 2 * a - rho) * lambdaFactored h a rho y *
      rootFiveFactor (y ^ 2 * lambdaFactored h a rho y) +
      a * lambdaDerivFactored h a rho y * rootFiveDeriv (y ^ 2 * lambdaFactored h a rho y) +
      y * rho * (a * m + rho)) -
      (11 / 4 + 1 / 25000) * (m * w + 1) * (1 + a / 4) * a ^ 2 * y)
    field_simp [ha.ne', hw.ne']
    dsimp only [m, g]
    ring
  have hcEq : a ^ 3 * deriv (deriv (middleGapFifthOrder h)) t =
      E * y ^ 2 * middleGapCurvaturePolynomial h a rho y := by
    rw [hG₂, hr, hexp, hU₁.deriv, hU₂.deriv, hS, hU]
    unfold middleGapCurvaturePolynomial
    dsimp only
    field_simp [ha.ne']
    dsimp only [g]
    ring
  have hA : 0 ≤ E * y ^ 2 * middleGapSlopePolynomial h t a rho y :=
    mul_nonneg (by positivity) hs
  have hB : 0 < E * y ^ 2 * middleGapCurvaturePolynomial h a rho y :=
    mul_pos (by positivity) hc
  rw [← hsEq] at hA
  rw [← hcEq] at hB
  exact ⟨sub_nonneg.mp (nonneg_of_mul_nonneg_right hA (by positivity)),
    pos_of_mul_pos_right hB (by positivity)⟩

#print axioms middleGapFifthOrder_bounds_of_polynomial

end RefinedBMV.PositiveCenter
