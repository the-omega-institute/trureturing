/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailLeading
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hyperbolic form of the normalized leading square. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailFormula
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

open private tail_leading_gap from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailFormula

open private compositionMoment_marginal_smooth from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization

private theorem hasDerivAt_middleTail_invMarginal {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let C : ℝ → ℝ := fun x ↦ compositionMoment p 0 (-x)
    HasDerivAt (fun x ↦ (Real.sqrt (C x))⁻¹)
      (-reflectedHalfLogSlope (compositionMoment p 0) t * (Real.sqrt (C t))⁻¹) t := by
  intro C
  have hC : 0 < C t := compositionMoment_marginal_pos hp (neg_ne_zero.mpr ht.ne')
  have hs := Real.sqrt_pos.mpr hC
  have hd : DifferentiableAt ℝ C t :=
    ((compositionMoment_marginal_smooth p).differentiable (by norm_num) (-t)).comp t
      differentiableAt_id.neg
  refine ((hd.hasDerivAt.sqrt hC.ne').inv hs.ne').congr_deriv ?_
  change -(deriv C t / (2 * Real.sqrt (C t))) / Real.sqrt (C t) ^ 2 =
    -(deriv C t / C t / 2) * (Real.sqrt (C t))⁻¹
  rw [show deriv C t / C t = deriv C t / Real.sqrt (C t) ^ 2 by
    rw [Real.sq_sqrt hC.le]]
  field_simp [hs.ne'] <;> ring

/-- Cancel the weight and retain the common marginal factors of the three summands. -/
theorem middleTail_normalizedBase_eq {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    let h : ℝ := 3 / (p : ℝ)
    let d := v - u
    let C : ℝ → ℝ := fun t ↦ compositionMoment p 0 (-t)
    let β : ℝ → ℝ := fun t ↦ 1 - Real.exp (-(h * t))
    upperTailBaseFactor p u d /
        Real.sqrt (upperTailNormalizer (p + 1) h (((p + 2).choose 2 : ℝ) / (p + 1)) v) =
      Real.exp u * (h * upperTailGap h d * (1 - Real.exp (-u)) ^ 2 /
        (2 * (Real.sqrt (C u) * Real.sqrt (C v) * β v))) := by
  intro h d C β
  let N : ℝ := ((p + 2).choose 2 : ℝ) / (p + 1)
  let A := upperTailNormalizer (p + 1) h N
  let g := upperTailGap h d
  let ell := 1 - Real.exp (-u)
  have hh : 0 < h := by dsimp only [h]; positivity
  have hv := hu.trans huv
  have hd : 0 < d := sub_pos.mpr huv
  have hβ (t : ℝ) (ht : 0 < t) : 0 < β t :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht)))
  have hβd : β d = h * g := by
    change β d = h * (β d / h)
    field_simp [hh.ne'] <;> ring
  have hN : 0 < N := by
    have hchoose : 0 < ((p + 2).choose 2 : ℝ) := by
      exact_mod_cast (Nat.choose_pos (show 2 ≤ p + 2 by omega))
    dsimp only [N]
    positivity
  have hCv : 0 < C v := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne')
  have hA : A v = N * (Real.exp (-v) * (β v * C v)) := by
    have hlo := upperTail_lower_weight hp v 0
    dsimp only at hlo
    simp only [zero_add, neg_zero, zero_div, Real.exp_zero, mul_zero] at hlo
    have hup := upperTail_upper_weight hp hv
    change (1 - (Real.exp (-v / (p : ℝ))) ^ 3) *
      DimThree.defect p (Real.exp (-v / (p : ℝ))) 1 1 = (p + 1 : ℝ) * A v at hup
    rw [hlo, (tail_cube_pow hp v).1] at hup
    have hn : (p + 1 : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    change (p + 1 : ℝ) * A v =
      (p + 1 : ℝ) * (((p + 2).choose 2 : ℝ) / (p + 1) * (Real.exp (-v) * (β v * C v)))
    rw [← hup]
    change β v * (((p + 2).choose 2 : ℝ) * Real.exp (-v) * C v) = _
    field_simp [hn] <;> ring
  have hexpRoot : Real.sqrt (Real.exp (-v)) = Real.exp (-v / 2) := by
    rw [show Real.exp (-v) = (Real.exp (-v / 2)) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring, Real.sqrt_sq (Real.exp_pos _).le]
  have hroot : Real.sqrt (A v) =
      Real.sqrt N * (Real.exp (-v / 2) * (Real.sqrt (β v) * Real.sqrt (C v))) := by
    rw [hA, Real.sqrt_mul hN.le, Real.sqrt_mul (Real.exp_pos _).le,
      Real.sqrt_mul (hβ v hv).le, hexpRoot]
  have he : Real.exp (-d / 2) * Real.exp (u / 2) =
      Real.exp u * Real.exp (-v / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [d]
    ring
  let S := Real.sqrt (C u) * Real.sqrt (C v) * β v
  have hsu := Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne'))
  have hsv := Real.sqrt_pos.mpr hCv
  have hb := Real.sqrt_pos.mpr (hβ v hv)
  have hsβ : (β v)⁻¹ = (Real.sqrt (β v))⁻¹ ^ 2 := by
    rw [inv_pow, Real.sq_sqrt (hβ v hv).le]
  have hBase : upperTailBaseFactor p u d / Real.sqrt (A v) =
      Real.exp u * (h * g * ell ^ 2 / (2 * S)) := by
    unfold upperTailBaseFactor
    change Real.sqrt N / 2 * Real.exp (-d / 2) *
      (β d / Real.sqrt (β (d + u))) *
      (Real.exp (u / 2) * ell ^ 2 / Real.sqrt (C u)) / Real.sqrt (A v) = _
    rw [show d + u = v by exact sub_add_cancel v u, hroot, hβd]
    calc
      _ = (Real.exp (-d / 2) * Real.exp (u / 2)) *
          (h * g * ell ^ 2 / (2 * S * Real.exp (-v / 2))) := by
        dsimp only [S]
        simp only [div_eq_mul_inv, mul_inv_rev, hsβ]
        field_simp [hsu.ne', hsv.ne', hb.ne', (Real.sqrt_pos.mpr hN).ne',
          (Real.exp_pos (-v / 2)).ne'] <;> ring
      _ = _ := by
        rw [he]
        field_simp [(Real.exp_pos (-v / 2)).ne'] <;> ring
  exact hBase

/-- The ratio whose logarithmic derivatives are elementary gap slopes. -/
noncomputable def middleTailRatio (h u v : ℝ) : ℝ :=
  Real.exp u * upperTailGap h (v - u) / upperTailGap h v

/-- The leading square in the exact kernel decomposition, with its upper weight. -/
noncomputable def middleTailLeadingContribution (p : ℕ) (u v : ℝ) : ℝ :=
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  upperTailBaseFactor p u d * (1 - upperTailSlope h d * upperTailRatio h u) ^ 2 /
    Real.sqrt (upperTailNormalizer (p + 1) h (((p + 2).choose 2 : ℝ) / (p + 1)) v)

/-- Write the leading square as a sum of a ratio and its reciprocal. -/
theorem middleTailLeading_eq {p : ℕ} (hp : 0 < p) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    let h : ℝ := 3 / (p : ℝ)
    let C : ℝ → ℝ := fun t ↦ compositionMoment p 0 (-t)
    let B := middleTailRatio h u v
    middleTailLeadingContribution p u v =
      (B - 2 + B⁻¹) / 2 * (Real.sqrt (C u))⁻¹ * (Real.sqrt (C v))⁻¹ := by
  intro h C B
  let d := v - u
  let β : ℝ → ℝ := fun t ↦ 1 - Real.exp (-(h * t))
  let ell := 1 - Real.exp (-u)
  let r := 1 - upperTailSlope h d * upperTailRatio h u
  let g := upperTailGap h
  have hh : 0 < h := by dsimp only [h]; positivity
  have hd : 0 < d := sub_pos.mpr huv
  have hv := hu.trans huv
  have hgd : 0 < g d := tail_gap_pos hh hd
  have hgv : 0 < g v := tail_gap_pos hh hv
  have hβv : β v = h * g v := by
    change β v = h * (β v / h)
    field_simp [hh.ne'] <;> ring
  have hB : 0 < B := by
    change 0 < Real.exp u * g d / g v
    exact div_pos (mul_pos (Real.exp_pos _) hgd) hgv
  have hB' : B * g v = Real.exp u * g d := by
    change (Real.exp u * g d / g v) * g v = _
    exact div_mul_cancel₀ _ hgv.ne'
  have hinv : B⁻¹ = g v * Real.exp (-u) / g d := by
    change (Real.exp u * g d / g v)⁻¹ = _
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos u).ne', hgd.ne', hgv.ne']
    <;> ring
  have hgap := tail_leading_gap hh hu hd
  change g d - g (d + u) * Real.exp (-u) = g d * ell * r at hgap
  have hgapInv : g v * Real.exp (-u) = g d * B⁻¹ := by
    rw [hinv]
    field_simp [hgd.ne'] <;> ring
  rw [sub_add_cancel v u, hgapInv] at hgap
  have hlead : ell * r = 1 - B⁻¹ := by
    apply mul_left_cancel₀ hgd.ne'
    rw [← mul_assoc, ← hgap, mul_sub, mul_one]
  have hnormalized := middleTail_normalizedBase_eq hp hu huv
  change upperTailBaseFactor p u d /
      Real.sqrt (upperTailNormalizer (p + 1) h (((p + 2).choose 2 : ℝ) / (p + 1)) v) =
    Real.exp u * (h * g d * ell ^ 2 / (2 * (Real.sqrt (C u) * Real.sqrt (C v) * β v)))
    at hnormalized
  change upperTailBaseFactor p u d * r ^ 2 /
      Real.sqrt (upperTailNormalizer (p + 1) h (((p + 2).choose 2 : ℝ) / (p + 1)) v) = _
  rw [mul_div_right_comm, hnormalized, hβv]
  have hcu := Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne'))
  have hcv := Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne'))
  calc
    _ = (Real.exp u * g d) * (ell * r) ^ 2 /
        (2 * Real.sqrt (C u) * Real.sqrt (C v) * g v) := by
      field_simp [hh.ne', hgv.ne', hcu.ne', hcv.ne'] <;> ring
    _ = B * (ell * r) ^ 2 / (2 * Real.sqrt (C u) * Real.sqrt (C v)) := by
      rw [← hB']
      field_simp [hgv.ne', hcu.ne', hcv.ne'] <;> ring
    _ = _ := by
      rw [hlead]
      field_simp [hB.ne', hcu.ne', hcv.ne']
      <;> ring

private theorem hasDerivAt_gap_logarithmic {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (upperTailGap h) (upperTailSlope h t * upperTailGap h t) t := by
  have H := hasDerivAt_upperTailGap (t := t) hh
  refine H.congr_deriv ?_
  rw [← H.deriv]
  exact (div_eq_iff (tail_gap_pos hh ht).ne').mp (upperTailGap_logDeriv hh ht)

private theorem hasDerivAt_middleTailRatio_fst {h u v : ℝ} (hh : 0 < h)
    (hu : 0 < u) (huv : u < v) :
    HasDerivAt (fun x ↦ middleTailRatio h x v)
      ((1 - upperTailSlope h (v - u)) * middleTailRatio h u v) u := by
  have hgap := (hasDerivAt_gap_logarithmic hh (sub_pos.mpr huv)).comp u
    ((hasDerivAt_const u v).sub (hasDerivAt_id' u))
  refine (((hasDerivAt_id' u).exp.mul hgap).div_const _).congr_deriv ?_
  simp only [middleTailRatio, Function.comp_def, id_eq, mul_one, zero_sub, mul_neg, Pi.mul_apply]
  ring

private theorem hasDerivAt_middleTailRatio_snd {h u v : ℝ} (hh : 0 < h)
    (hu : 0 < u) (huv : u < v) :
    HasDerivAt (middleTailRatio h u)
      ((upperTailSlope h (v - u) - upperTailSlope h v) * middleTailRatio h u v) v := by
  have hv := hu.trans huv
  have hgap := (hasDerivAt_gap_logarithmic hh (sub_pos.mpr huv)).comp v
    ((hasDerivAt_id' v).sub_const u)
  refine ((hgap.const_mul (Real.exp u)).div (hasDerivAt_gap_logarithmic hh hv)
    (tail_gap_pos hh hv).ne').congr_deriv ?_
  simp only [middleTailRatio, Function.comp_def, mul_one, Pi.mul_apply]
  field_simp [(tail_gap_pos hh hv).ne'] <;> ring

private noncomputable def middleTailRatioJet (h u v : ℝ) : MixedJet ℝ :=
  let B := middleTailRatio h u v
  let j := upperTailSlope h (v - u)
  let ell := 1 - j
  let Δ := j - upperTailSlope h v
  ⟨B, ell * B, Δ * B, (ell * Δ + j * (h + j)) * B⟩

private theorem middleTailRatioJet_isAt {h u v : ℝ} (hh : 0 < h)
    (hu : 0 < u) (huv : u < v) : MixedJet.IsAt (middleTailRatioJet h) u v := by
  have hv := hasDerivAt_middleTailRatio_snd hh hu huv
  refine ⟨?_, hv, ?_⟩
  · filter_upwards [eventually_gt_nhds huv] with y hy
    exact hasDerivAt_middleTailRatio_fst hh hu hy
  · have hj := (hasDerivAt_upperTailSlope hh (sub_pos.mpr huv)).comp v
      ((hasDerivAt_id' v).sub_const u)
    refine ((hj.const_sub 1).mul hv).congr_deriv ?_
    simp only [middleTailRatioJet, Function.comp_def, mul_one, neg_neg, Pi.mul_apply]
    ring

/-- After multiplying by the positive marginal factor, the leading mixed derivative
uses the same ratio powers as the linear correction. -/
theorem middleTailLeading_mixed_eq {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    let h : ℝ := 3 / (p : ℝ)
    let C : ℝ → ℝ := fun t ↦ compositionMoment p 0 (-t)
    let B := middleTailRatio h u v
    let a := reflectedHalfLogSlope (compositionMoment p 0)
    let j := upperTailSlope h (v - u)
    let ell := 1 - j
    let Δ := j - upperTailSlope h v
    let η := j * (h + j)
    (2 / B * (Real.sqrt (C u) * Real.sqrt (C v))) *
      deriv (fun y ↦ deriv (fun x ↦ middleTailLeadingContribution p x y) u) v =
        (1 - B⁻¹ ^ 2) * (η + Δ * (ell - a u) - a v * ell) +
          a v * a u * (1 - B⁻¹) ^ 2 + 2 * Δ * ell * B⁻¹ ^ 2 := by
  intro h C B a j ell Δ η
  let A : ℝ → ℝ := fun t ↦ (Real.sqrt (C t))⁻¹
  let U : ℝ → ℝ → MixedJet ℝ := fun x _ ↦ ⟨A x, -(a x) * A x, 0, 0⟩
  let V : ℝ → ℝ → MixedJet ℝ := fun _ y ↦ ⟨A y, 0, -(a y) * A y, 0⟩
  let J := middleTailRatioJet h
  let two : ℝ → ℝ → MixedJet ℝ := fun _ _ ↦ ⟨2, 0, 0, 0⟩
  let half : ℝ → ℝ → MixedJet ℝ := fun _ _ ↦ ⟨1 / 2, 0, 0, 0⟩
  let T : ℝ → ℝ → MixedJet ℝ :=
    fun x y ↦ (((J x y).sub (two x y)).add (J x y).reciprocal).mul
      (((half x y).mul (U x y)).mul (V x y))
  have hh : 0 < h := by dsimp only [h]; positivity
  have hv := hu.trans huv
  have hB : 0 < B :=
    div_pos (mul_pos (Real.exp_pos _) (tail_gap_pos hh (sub_pos.mpr huv))) (tail_gap_pos hh hv)
  have hU : MixedJet.IsAt U u v :=
    ⟨Filter.Eventually.of_forall (fun _ ↦ hasDerivAt_middleTail_invMarginal hp hu),
      hasDerivAt_const v _, hasDerivAt_const v _⟩
  have hV : MixedJet.IsAt V u v :=
    ⟨Filter.Eventually.of_forall (fun y ↦ hasDerivAt_const u (A y)),
      hasDerivAt_middleTail_invMarginal hp hv, hasDerivAt_const v _⟩
  have htwo : MixedJet.IsAt two u v :=
    ⟨Filter.Eventually.of_forall (fun _ ↦ hasDerivAt_const u _),
      hasDerivAt_const v _, hasDerivAt_const v _⟩
  have hhalf : MixedJet.IsAt half u v :=
    ⟨Filter.Eventually.of_forall (fun _ ↦ hasDerivAt_const u _),
      hasDerivAt_const v _, hasDerivAt_const v _⟩
  have hJ : MixedJet.IsAt J u v := middleTailRatioJet_isAt hh hu huv
  have hJR := hJ.reciprocal (show (J u v).value ≠ 0 from hB.ne')
  have hT : MixedJet.IsAt T u v :=
    (((hJ.sub htwo).add hJR).mul ((hhalf.mul hU).mul hV))
  have hs : (fun y ↦ deriv (fun x ↦ middleTailLeadingContribution p x y) u) =ᶠ[𝓝 v]
      fun y ↦ (T u y).du := by
    filter_upwards [eventually_gt_nhds huv, hT.1] with y hy hTy
    rw [← hTy.deriv]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hu, eventually_lt_nhds hy] with x hx hxy
    rw [middleTailLeading_eq hp hx hxy]
    simp only [T, J, middleTailRatioJet, two, half, U, V, A, C, h,
      MixedJet.sub, MixedJet.add, MixedJet.reciprocal, MixedJet.mul]
    ring
  rw [hs.deriv_eq, hT.2.2.deriv]
  have hCu : 0 < Real.sqrt (C u) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne'))
  have hCv : 0 < Real.sqrt (C v) :=
    Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne'))
  change 2 / B * (Real.sqrt (C u) * Real.sqrt (C v)) *
    ((((⟨B, ell * B, Δ * B, (ell * Δ + η) * B⟩ : MixedJet ℝ).sub (two u v)).add
      (⟨B, ell * B, Δ * B, (ell * Δ + η) * B⟩ : MixedJet ℝ).reciprocal).mul
      (((half u v).mul (U u v)).mul (V u v))).duv = _
  simp only [two, half, U, V, A, MixedJet.sub, MixedJet.add, MixedJet.reciprocal, MixedJet.mul]
  field_simp [hB.ne', hCu.ne', hCv.ne'] <;> ring

end RefinedBMV.PositiveCenter
