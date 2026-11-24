/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailFullScore
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full central mixed score including its radical contribution. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailJointScore

/-! The radical contribution under the same positive factor as the other two summands. -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

open private hasDerivAt_middleTail_invMarginal hasDerivAt_gap_logarithmic from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailLeading
open private upperTailRadicalRoot_pos hasDerivAt_upperTailRadicalRoot radicalRateFactor
  hasDerivAt_radicalRateFactor from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedGapRadical
open private middleTail_gapSlope_sub from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailJointScore

private theorem middleTailRadical_value {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    let h : ℝ := 3 / (p : ℝ)
    let c := (3 + h) * (3 + 2 * h) / 2
    let C : ℝ → ℝ := fun t ↦ compositionMoment p 0 (-t)
    let f := upperTailGap h
    let d := v - u
    let z := upperTailRadicalRoot h
    separatedGapRadicalContribution p u v =
      (Real.exp u * (Real.sqrt (C u))⁻¹) *
        ((Real.sqrt (C v))⁻¹ / f v) * (Real.exp (2 * d) / f d) *
          (z v - z d) ^ 2 / (2 * c) := by
  intro h c C f d z
  let β : ℝ → ℝ := fun t ↦ 1 - Real.exp (-(h * t))
  let A := upperTailNormalizer (p + 1) h (((p + 2).choose 2 : ℝ) / (p + 1))
  let ell := 1 - Real.exp (-u)
  let E := Real.exp (-(2 * d))
  have hh : 0 < h := by dsimp only [h]; positivity
  have hd : 0 < d := sub_pos.mpr huv
  have hv := hu.trans huv
  have hfd : 0 < f d := tail_gap_pos hh hd
  have hfv : 0 < f v := tail_gap_pos hh hv
  have hc : 0 < c := by dsimp only [c]; positivity
  have hell : 0 < ell := upperTailLinear_ell_pos hu
  have hE : 0 < E := Real.exp_pos _
  have hCu : 0 < Real.sqrt (C u) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne'))
  have hCv : 0 < Real.sqrt (C v) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne'))
  have hβv : β v = h * f v := tail_gap_factor hh
  have hBase := middleTail_normalizedBase_eq hp hu huv
  change upperTailBaseFactor p u d / Real.sqrt (A v) =
    Real.exp u * (h * f d * ell ^ 2 / (2 * (Real.sqrt (C u) * Real.sqrt (C v) * β v)))
    at hBase
  have hQ : upperTailQuadratic h u d =
      (((z v - z d) / ell) ^ 2) * (c * f d ^ 2 * E)⁻¹ := by
    unfold upperTailQuadratic upperTailRootDifference
    dsimp only [d, z]
    rw [sub_add_cancel v u]
  change (1 / Real.sqrt (A v)) * upperTailBaseFactor p u d * upperTailQuadratic h u d = _
  have hcancel : (1 / Real.sqrt (A v)) * upperTailBaseFactor p u d =
      upperTailBaseFactor p u d / Real.sqrt (A v) := by ring
  rw [hcancel, hBase, hQ, hβv,
    show Real.exp (2 * d) = E⁻¹ by dsimp only [E]; rw [Real.exp_neg, inv_inv]]
  field_simp [hh.ne', hc.ne', hfd.ne', hfv.ne', hCu.ne', hCv.ne', hell.ne', hE.ne']
  <;> ring

/-- The cleared radical mixed derivative in the independent coordinates. -/
noncomputable def middleTailRadicalScore (h u d a b : ℝ) : ℝ :=
  let v := d + u
  let f := upperTailGap h d
  let c := (3 + h) * (3 + 2 * h) / 2
  let j := upperTailSlope h d
  let η := j * (h + j)
  let z := upperTailRadicalRoot h
  let T := deriv z
  let D := z v - z d
  let Dv := T v - T d
  let α := -1 + j - a
  let β := 2 - j - upperTailSlope h v - b
  Real.exp (2 * d) / (c * f ^ 2) *
    ((α * β - η) * D ^ 2 + 2 * D * (α * Dv + β * T d + deriv T d) + 2 * T d * Dv)

/-- Multiplication by the positive weight used by both leading terms gives
the cleared radical score. -/
theorem middleTailRadical_clearedMixed_eq {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    let h : ℝ := 3 / (p : ℝ)
    let C : ℝ → ℝ := fun t ↦ compositionMoment p 0 (-t)
    let B := middleTailRatio h u v
    let a := reflectedHalfLogSlope (compositionMoment p 0)
    (2 / B * (Real.sqrt (C u) * Real.sqrt (C v))) *
      deriv (fun t ↦ deriv (fun x ↦ separatedGapRadicalContribution p x t) u) v =
        middleTailRadicalScore h u (v - u) (a u) (a v) := by
  intro h C B a
  let d := v - u
  let c := (3 + h) * (3 + 2 * h) / 2
  let f := upperTailGap h
  let j := upperTailSlope h
  let z := upperTailRadicalRoot h
  let T := deriv z
  let P : ℝ → ℝ := fun t ↦ Real.exp t * (Real.sqrt (C t))⁻¹
  let Q : ℝ → ℝ := fun t ↦ (Real.sqrt (C t))⁻¹ / f t
  let J : ℝ → ℝ := fun t ↦ Real.exp (2 * t) / f t
  let ell : ℝ → ℝ := fun t ↦ 2 - j t
  let α : ℝ → ℝ := fun t ↦ 1 - a u - ell (t - u)
  let β := ell d - j v - a v
  let η := j d * (h + j d)
  let D : ℝ → ℝ := fun t ↦ z t - z (t - u)
  let Dv := T v - T d
  have hh : 0 < h := by dsimp only [h]; positivity
  have hd : 0 < d := sub_pos.mpr huv
  have hv := hu.trans huv
  have hfd : 0 < f d := tail_gap_pos hh hd
  have hfv : 0 < f v := tail_gap_pos hh hv
  have hc : 0 < c := by dsimp only [c]; positivity
  have hP : HasDerivAt P (P u * (1 - a u)) u := by
    refine ((hasDerivAt_id' u).exp.mul (hasDerivAt_middleTail_invMarginal hp hu)).congr_deriv ?_
    simp only [P, id_eq, mul_one, Pi.mul_apply]
    ring
  have hQ : HasDerivAt Q (Q v * (-j v - a v)) v := by
    refine ((hasDerivAt_middleTail_invMarginal hp hv).div (hasDerivAt_gap_logarithmic hh hv)
      hfv.ne').congr_deriv ?_
    change ((-a v * (Real.sqrt (C v))⁻¹) * f v - (Real.sqrt (C v))⁻¹ * (j v * f v)) /
      (f v) ^ 2 = Q v * (-j v - a v)
    dsimp only [Q]
    field_simp [hfv.ne'] <;> ring
  have hJ (t : ℝ) (ht : 0 < t) : HasDerivAt J (J t * ell t) t := by
    have hf : 0 < f t := tail_gap_pos hh ht
    refine ((((hasDerivAt_id' t).const_mul 2).exp).div (hasDerivAt_gap_logarithmic hh ht)
      hf.ne').congr_deriv ?_
    change ((Real.exp (2 * t) * (2 * 1)) * f t - Real.exp (2 * t) * (j t * f t)) /
      (f t) ^ 2 = J t * ell t
    dsimp only [J, ell]
    field_simp [hf.ne'] <;> ring
  have hz (t : ℝ) (ht : 0 < t) : HasDerivAt z (T t) t :=
    (hasDerivAt_upperTailRadicalRoot hh ht).differentiableAt.hasDerivAt
  have hfirst : (fun y ↦ deriv (fun x ↦ separatedGapRadicalContribution p x y) u) =ᶠ[𝓝 v]
      fun y ↦ (P u * Q y * J (y - u) / (2 * c)) *
        (α y * (D y) ^ 2 + 2 * D y * T (y - u)) := by
    filter_upwards [eventually_gt_nhds huv] with y hy
    have hnear : (fun x ↦ separatedGapRadicalContribution p x y) =ᶠ[𝓝 u]
        fun x ↦ P x * Q y * J (y - x) * (z y - z (y - x)) ^ 2 / (2 * c) := by
      filter_upwards [eventually_gt_nhds hu, eventually_lt_nhds hy] with t ht hty
      exact middleTailRadical_value hp ht hty
    have hdif : HasDerivAt (fun x ↦ y - x) (-1) u := by
      simpa only [zero_sub] using (hasDerivAt_id' u).const_sub y
    have hGap := (hJ (y-u) (sub_pos.mpr hy)).comp u hdif
    have hDiff := ((hz (y-u) (sub_pos.mpr hy)).comp u hdif).const_sub (z y)
    have hder := ((((hP.mul_const (Q y)).mul hGap).mul (hDiff.pow 2))).div_const (2 * c)
    rw [hnear.deriv_eq, hder.deriv]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp_def, Pi.pow_apply,
      Pi.mul_apply, mul_neg, mul_one, neg_neg]
    dsimp only [α, D]
    ring
  have hdif : HasDerivAt (fun y ↦ y - u) 1 v := (hasDerivAt_id' v).sub_const u
  have hGap := (hJ d hd).comp v hdif
  have hDiff : HasDerivAt D Dv v := by
    simpa only [D, Dv, Function.comp_def, mul_one] using (hz v hv).sub ((hz d hd).comp v hdif)
  have hα : HasDerivAt α (-η) v := by
    have hj := (hasDerivAt_upperTailSlope hh hd).comp v hdif
    simpa only [α, ell, η, Function.comp_def, mul_one, neg_neg] using
      (hj.const_sub (2 : ℝ)).const_sub (1 - a u)
  have hSmooth : ContDiffAt ℝ 2 z d := by
    have hBefore : ContDiffAt ℝ 2 (fun t ↦ 1 - upperTailLambda h t) d := by
      unfold upperTailLambda upperTailGap
      fun_prop
    exact hBefore.sqrt (Real.sqrt_pos.mp (upperTailRadicalRoot_pos hh hd)).ne'
  have hT : DifferentiableAt ℝ T d :=
    (hSmooth.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hT' := hT.hasDerivAt.comp v hdif
  have hleft := (((hQ.const_mul (P u)).mul hGap)).div_const (2 * c)
  have hright := (hα.mul (hDiff.pow 2)).add ((hDiff.const_mul 2).mul hT')
  have hder := hleft.mul hright
  rw [hfirst.deriv_eq, hder.deriv]
  have hExp : Real.exp u * f d / f v = B := rfl
  have hCu : 0 < Real.sqrt (C u) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne'))
  have hCv : 0 < Real.sqrt (C v) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne'))
  have hB : 0 < B := div_pos (mul_pos (Real.exp_pos _) hfd) hfv
  unfold middleTailRadicalScore
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp_def, Pi.pow_apply,
    Pi.mul_apply, Pi.add_apply, mul_one, sub_add_cancel v u]
  dsimp only [P, Q, J, α, β, ell, Dv, D, η]
  have hB' : B = Real.exp u * f d / f v := hExp.symm
  rw [hB']
  field_simp [hc.ne', hCu.ne', hCv.ne', hfd.ne', hfv.ne', (Real.exp_pos u).ne']
  <;> ring

/-- The square-root derivatives in the full score have a common numerator,
so the arithmetic comparison needs a single positive root at each point. -/
theorem middleTailRadical_root_derivatives {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    let f := upperTailGap h t
    let b := Real.exp (-(h * t))
    let x := Real.exp (-t)
    let g := f - b * (1 - x)
    let c := (3 + h) * (3 + 2 * h) / 2
    let z := upperTailRadicalRoot h
    let N := c * f * x ^ 2 * g
    let N₁ := c * x ^ 2 * ((b - 2 * f) * g + f * ((1 + h) * b * (1 - x)))
    deriv z t = N / z t ∧ deriv (deriv z) t = (N₁ - (N / z t) ^ 2) / z t := by
  intro f b x g c z N N₁
  let numerator : ℝ → ℝ := fun s ↦ c * upperTailGap h s * Real.exp (-s) ^ 2 *
    radicalRateFactor h s
  have hExp (s : ℝ) : Real.exp (-((1 + h) * s)) = Real.exp (-(h * s)) * Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he : radicalRateFactor h t = g := by
    change (1 + h) * f - 1 + Real.exp (-((1 + h) * t)) = f - b * (1 - x)
    rw [hExp]
    change (1 + h) * f - 1 + b * x = _
    have H : 1 - b = h * f := tail_gap_factor hh
    linear_combination -H
  have hA (s : ℝ) (hs : 0 < s) :
      HasDerivAt z (numerator s / z s) s := by
    refine (hasDerivAt_upperTailRadicalRoot hh hs).congr_deriv ?_
    simp only [numerator, c]
    rw [show Real.exp (-(2 * s)) = Real.exp (-s) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
    ring
  have hval : numerator t = N := by
    dsimp only [numerator, N]
    rw [he]
  have hG := hasDerivAt_radicalRateFactor h t
  rw [hExp] at hG
  have hG' : HasDerivAt (radicalRateFactor h) ((1 + h) * b * (1 - x)) t := by
    refine hG.congr_deriv ?_
    change (1 + h) * (b - b * x) = (1 + h) * b * (1 - x)
    ring
  have hX := (hasDerivAt_id' t).neg.exp
  have hNum : HasDerivAt numerator N₁ t := by
    refine ((((hasDerivAt_upperTailGap (t := t) hh).const_mul c).mul (hX.pow 2)).mul hG')
      |>.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply, Pi.neg_apply]
    dsimp only [N₁]
    rw [he]
    change (c * b * x ^ 2 + c * f * (2 * x * (x * -1))) * g +
      (c * f * x ^ 2) * ((1 + h) * b * (1 - x)) = _
    ring
  have hnear : deriv z =ᶠ[𝓝 t] fun s ↦ numerator s / z s := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (hA s hs).deriv
  have hz : 0 < z t := upperTailRadicalRoot_pos hh ht
  have ht' := (hNum.div (hA t ht) hz.ne').deriv
  rw [hnear.deriv_eq, ht', hval]
  refine ⟨(hA t ht).deriv.trans (by rw [hval]), ?_⟩
  field_simp [hz.ne'] <;> ring

/-- The radical score is affine in a single root ratio. The coefficients
use the squared roots and the numerator of each root derivative. -/
theorem middleTailRadicalScore_affine_rootRatio {h u d a b : ℝ}
    (hh : 0 < h) (hu : 0 < u) (hd : 0 < d) :
    let v := d + u
    let f := upperTailGap h
    let c := (3 + h) * (3 + 2 * h) / 2
    let q : ℝ → ℝ := fun t ↦ 1 - upperTailLambda h t
    let e : ℝ → ℝ := fun t ↦ Real.exp (-(h * t))
    let x : ℝ → ℝ := fun t ↦ Real.exp (-t)
    let g : ℝ → ℝ := fun t ↦ f t - e t * (1 - x t)
    let N : ℝ → ℝ := fun t ↦ c * f t * x t ^ 2 * g t
    let N₁ : ℝ → ℝ := fun t ↦
      c * x t ^ 2 * ((e t - 2 * f t) * g t + f t * ((1 + h) * e t * (1 - x t)))
    let s : ℝ → ℝ := fun t ↦ N t / q t
    let r := Real.sqrt (q v / q d) - 1
    let j := upperTailSlope h d
    let α := -1 + j - a
    let β := 2 - j - upperTailSlope h v - b
    let C₀ := 2 * s d * (s v - s d)
    let C₁ := 2 * (α * (s v - s d) + β * s d + N₁ d / q d - s d ^ 2 + s d * s v)
    let C₂ := α * β - j * (h + j) + 2 * α * s v
    middleTailRadicalScore h u d a b =
      Real.exp (2 * d) * q d / (c * f d ^ 2) *
        (C₀ + C₂ * ((q v - q d) / q d) + (C₁ - 2 * C₂) * r) := by
  intro v f c q e x g N N₁ s r j α β C₀ C₁ C₂
  let z := upperTailRadicalRoot h
  have hv : 0 < v := add_pos hd hu
  have hz (t : ℝ) (ht : 0 < t) : 0 < z t := upperTailRadicalRoot_pos hh ht
  have hq (t : ℝ) (ht : 0 < t) : z t ^ 2 = q t := by
    have hpos : 0 < Real.sqrt (1 - upperTailLambda h t) := hz t ht
    exact Real.sq_sqrt (Real.sqrt_pos.mp hpos).le
  have hs (t : ℝ) (ht : 0 < t) :
      deriv z t = z t * s t ∧ deriv (deriv z) t = z t * (N₁ t / q t - s t ^ 2) := by
    obtain ⟨h₁, h₂⟩ := middleTailRadical_root_derivatives hh ht
    change deriv z t = N t / z t at h₁
    change deriv (deriv z) t = (N₁ t - (N t / z t) ^ 2) / z t at h₂
    constructor
    · rw [h₁]
      change N t / z t = z t * (N t / q t)
      rw [← hq t ht]
      field_simp [(hz t ht).ne'] <;> ring
    · rw [h₂]
      change (N₁ t - (N t / z t) ^ 2) / z t =
        z t * (N₁ t / q t - (N t / q t) ^ 2)
      rw [← hq t ht]
      field_simp [(hz t ht).ne'] <;> ring
  have hr : z v = z d * (1 + r) := by
    have hqv : 0 ≤ q v := (hq v hv) ▸ sq_nonneg (z v)
    change z v = z d * (1 + (Real.sqrt (q v / q d) - 1))
    rw [Real.sqrt_div hqv]
    change z v = z d * (1 + (z v / z d - 1))
    field_simp [(hz d hd).ne'] <;> ring
  have hD : z v - z d = z d * r := by linear_combination hr
  have hDv : deriv z v - deriv z d = z d * (s v - s d + r * s v) := by
    rw [(hs v hv).1, (hs d hd).1]
    linear_combination s v * hr
  have hy : (q v - q d) / q d = r ^ 2 + 2 * r := by
    rw [← hq v hv, ← hq d hd, hr]
    field_simp [(hz d hd).ne'] <;> ring
  change Real.exp (2 * d) / (c * f d ^ 2) *
    ((α * β - j * (h + j)) * (z v - z d) ^ 2 +
      2 * (z v - z d) *
        (α * (deriv z v - deriv z d) + β * deriv z d + deriv (deriv z) d) +
      2 * deriv z d * (deriv z v - deriv z d)) = _
  rw [hD, hDv, (hs d hd).1, (hs d hd).2, hy]
  change _ = Real.exp (2 * d) * q d / (c * f d ^ 2) *
    (2 * s d * (s v - s d) + C₂ * (r ^ 2 + 2 * r) + (C₁ - 2 * C₂) * r)
  calc
    _ = (Real.exp (2 * d) * z d ^ 2 / (c * f d ^ 2)) *
        (2 * s d * (s v - s d) + C₂ * (r ^ 2 + 2 * r) + (C₁ - 2 * C₂) * r) := by
      dsimp only [C₁, C₂]
      ring
    _ = _ := by rw [hq d hd]

/-- A joint sign of all three cleared contributions gives the mixed sign
even where the leading square and linear term fail to have the required sign. -/
theorem logKernel_mixed_neg_of_fullMiddleTailScore {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hv₁ : 1 ≤ v)
    (hscore :
      let h : ℝ := 3 / (p : ℝ)
      let a := reflectedHalfLogSlope (compositionMoment p 0)
      middleTailLeadingScore h u (v - u) (a u) (a v) +
        middleTailLinearScore h u (v - u) (a u) (a v) +
          middleTailRadicalScore h u (v - u) (a u) (a v) < 0) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  let C : ℝ → ℝ := fun t ↦ compositionMoment p 0 (-t)
  let B := middleTailRatio h u v
  let a := reflectedHalfLogSlope (compositionMoment p 0)
  let scale := 2 / B * (Real.sqrt (C u) * Real.sqrt (C v))
  have hh : 0 < h := by dsimp only [h]; positivity
  have hd : 0 < d := sub_pos.mpr huv
  have hv := hu.trans huv
  have hfd : 0 < upperTailGap h d := tail_gap_pos hh hd
  have hfv : 0 < upperTailGap h v := tail_gap_pos hh hv
  have hB : 0 < B := div_pos (mul_pos (Real.exp_pos u) hfd) hfv
  have hCu : 0 < Real.sqrt (C u) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne'))
  have hCv : 0 < Real.sqrt (C v) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne'))
  have hscale : 0 < scale := mul_pos (div_pos (by norm_num) hB) (mul_pos hCu hCv)
  have hq : B⁻¹ = upperTailGap h v * Real.exp (-u) / upperTailGap h d := by
    change (Real.exp u * upperTailGap h d / upperTailGap h v)⁻¹ = _
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos u).ne', hfd.ne', hfv.ne'] <;> ring
  have hδ := middleTail_gapSlope_sub hh hu hd
  change upperTailSlope h d - upperTailSlope h (d + u) =
    Real.exp (-(h * d)) * upperTailGap h u / (upperTailGap h d * upperTailGap h (d + u)) at hδ
  rw [sub_add_cancel v u] at hδ
  have hlead : scale *
      deriv (fun y ↦ deriv (fun x ↦ middleTailLeadingContribution p x y) u) v =
        middleTailLeadingScore h u d (a u) (a v) := by
    rw [show scale = 2 / B * (Real.sqrt (C u) * Real.sqrt (C v)) from rfl,
      middleTailLeading_mixed_eq hp hu huv]
    change (1 - B⁻¹ ^ 2) * _ + _ + _ = _
    unfold middleTailLeadingScore
    dsimp only
    rw [sub_add_cancel v u, hq, hδ]
  have hlin : scale *
      deriv (fun y ↦ deriv (fun x ↦ middleTailLinearContribution p x y) u) v =
        middleTailLinearScore h u d (a u) (a v) := by
    rw [show scale = 2 / B * (Real.sqrt (C u) * Real.sqrt (C v)) from rfl,
      middleTailLinear_clearedMixed_eq hp hu huv]
    unfold middleTailLinearScore
    dsimp only
    rw [sub_add_cancel v u]
  have hrad : scale *
      deriv (fun y ↦ deriv (fun x ↦ separatedGapRadicalContribution p x y) u) v =
        middleTailRadicalScore h u d (a u) (a v) :=
    middleTailRadical_clearedMixed_eq hp hu huv
  rw [middleTail_kernel_mixed_eq hp hu huv hv₁]
  apply (mul_lt_mul_iff_right₀ hscale).mp
  rw [mul_add, mul_add, hlead, hlin, hrad, mul_zero]
  exact hscore

end RefinedBMV.PositiveCenter
