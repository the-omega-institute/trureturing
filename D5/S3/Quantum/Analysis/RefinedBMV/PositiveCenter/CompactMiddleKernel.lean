/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMiddleKernel
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A kernel formula with the two reflected marginals separated from the single radical. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGapIdentities
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleEndpoints
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripProfile
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MixedNormalization
import Batteries.Tactic.OpenPrivate

/-! The kernel in the form used by the middle-gap endpoint argument. -/

namespace RefinedBMV.PositiveCenter.CompactGap

open Filter
open scoped Topology

noncomputable section

open private rate node c W X R cross_eq W_eq_defect X_pos gap_factor from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGapIdentities

private theorem W_eq_reflected {p : ℕ} (hp : 0 < p) (t : ℝ) :
    W (rate p) t = c (rate p) * (upperTailGap (rate p) t) ^ 2 *
      Real.exp (-t) * compositionMoment p 0 (-t) := by
  have hDefect : DimThree.defect p (node p t) 1 1 =
      ((p+2).choose 2 : ℝ) * Real.exp (-t) * compositionMoment p 0 (-t) := by
    simpa [node] using upperTail_lower_weight hp t 0
  have hscale : ((p+2).choose 2 : ℝ) * (rate p) ^ 2 = c (rate p) := tail_choose_scale hp
  rw [← W_eq_defect hp, gap_factor, hDefect, ← hscale]
  ring

private theorem sqrt_W_eq_reflected {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    Real.sqrt (W (rate p) t) =
      Real.sqrt (c (rate p)) * upperTailGap (rate p) t * Real.exp (-t / 2) *
        Real.sqrt (compositionMoment p 0 (-t)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < rate p := by unfold rate; positivity
  have hc : 0 < c (rate p) := by unfold c; positivity
  have hf := tail_gap_pos hh ht
  have he : Real.exp (-t) = Real.exp (-t / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [W_eq_reflected hp, Real.sqrt_mul (by positivity : 0 ≤
    c (rate p) * (upperTailGap (rate p) t) ^ 2 * Real.exp (-t)),
    Real.sqrt_mul (by positivity : 0 ≤ c (rate p) * (upperTailGap (rate p) t) ^ 2),
    Real.sqrt_mul hc.le, Real.sqrt_sq hf.le, he, Real.sqrt_sq (Real.exp_pos _).le]

private theorem weight_closed {h u v : ℝ} (hh : 0 < h) (hv : 0 < v) (huv : u < v) :
    leftStripWeight h u v =
      Real.exp (v + (v - u)) / (c h * upperTailGap h v * upperTailGap h (v - u)) := by
  have hfv := tail_gap_pos hh hv
  have hfd := tail_gap_pos hh (sub_pos.mpr huv)
  unfold leftStripWeight logReciprocalGap
  change Real.exp ((v - Real.log (upperTailGap h v)) +
    ((v - u) - Real.log (upperTailGap h (v - u)))) / c h = _
  rw [Real.exp_add, Real.exp_sub, Real.exp_sub, Real.exp_log hfv, Real.exp_log hfd, Real.exp_add]
  ring

/-- A single square root remains in the numerator, with a positive prefactor. -/
theorem logKernel_eq_middleGap {p : ℕ} (hp : 0 < p) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    let h : ℝ := 3 / (p : ℝ)
    let d := v - u
    let f := upperTailGap h
    let Xv := 1 - upperTailLambda h v
    let Xd := 1 - upperTailLambda h d
    let P := ((3 + h) * (3 + 2 * h) / 2) * f v * f d * Real.exp (-(v + d))
    logKernel p u v =
      leftStripWeight h u v /
        Real.sqrt (compositionMoment p 0 (-u) * compositionMoment p 0 (-v)) *
      (1 - upperTailCrossCorrection h u d - Real.sqrt (Xv * Xd) - P) := by
  let h := rate p
  let d := v - u
  let f := upperTailGap h
  let C := fun t ↦ compositionMoment p 0 (-t)
  have hd : 0 < d := sub_pos.mpr huv
  have hv := hu.trans huv
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h, rate]; positivity
  have hc : 0 < c h := by unfold c; positivity
  have hfu : 0 < f u := tail_gap_pos hh hu
  have hfv : 0 < f v := tail_gap_pos hh hv
  have hfd : 0 < f d := tail_gap_pos hh hd
  have hCu : 0 < C u := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne')
  have hCv : 0 < C v := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne')
  have hva : d + u = v := sub_add_cancel v u
  have hk := logKernel_eq_exp_mul_G hp hu hd
  rw [hva] at hk
  change logKernel p u v = Real.exp (-d / 2) * G h u d at hk
  change logKernel p u v = leftStripWeight h u v / Real.sqrt (C u * C v) *
    (1 - upperTailCrossCorrection h u d - Real.sqrt (X h v * X h d) -
      c h * f v * f d * Real.exp (-(v + d)))
  rw [hk]
  unfold G
  dsimp only
  rw [hva, sqrt_W_eq_reflected hp hu, sqrt_W_eq_reflected hp hv, Real.sqrt_mul hCu.le,
    Real.sqrt_mul (X_pos hp hv).le, cross_eq hp hu d]
  have hL : leftStripWeight h u v = Real.exp (v + d) / (c h * f v * f d) :=
    weight_closed hh hv huv
  rw [hL]
  have he : Real.exp (v + d) * Real.exp (-u / 2) * Real.exp (-v / 2) =
      Real.exp (-d / 2) * Real.exp (2 * d) := by
    simp only [← Real.exp_add]
    congr 1
    dsimp only [d]
    ring
  rw [← mul_div_assoc, ← mul_assoc, ← he]
  dsimp only [C, f, h] at hfu hfv hfd hc hCu hCv ⊢
  have hr := Real.sqrt_pos.mpr hc
  have hsq := Real.sq_sqrt hc.le
  generalize Real.sqrt (c (rate p)) = root at hr hsq ⊢
  rw [← hsq]
  field_simp [hfu.ne', hfv.ne', hfd.ne', hr.ne', (Real.sqrt_pos.mpr hCu).ne',
    (Real.sqrt_pos.mpr hCv).ne', (Real.exp_pos (-u / 2)).ne', (Real.exp_pos (-v / 2)).ne'] <;> ring

private def weightJet (h u v : ℝ) : MixedJet ℝ :=
  let L := leftStripWeight h u v
  let a := profileSlope h (v - u)
  let b := profileSlope h v + a
  ⟨L, -(L * a), L * b, -(L * (a * b + profileCurvature h (v - u)))⟩

private theorem weightJet_isAt {h u v : ℝ} (hh : 0 < h) (hu : 0 < u) (huv : u < v) :
    MixedJet.IsAt (weightJet h) u v := by
  refine ⟨?_, hasDerivAt_leftStripWeight_right hh (hu.trans huv) huv, ?_⟩
  · filter_upwards [eventually_gt_nhds huv] with y hy
    simpa only [weightJet, neg_mul] using hasDerivAt_leftStripWeight_left hh hy
  · have ha := (hasDerivAt_profileSlope hh (sub_pos.mpr huv)).comp v
      ((hasDerivAt_id' v).sub_const u)
    have hL := hasDerivAt_leftStripWeight_right hh (hu.trans huv) huv
    refine (hL.mul ha).neg.congr_deriv ?_
    dsimp only [weightJet, Function.comp_def] at *
    ring

open private inverseRoot_deriv from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MixedNormalization

private def inverseRootPairJet (C : ℝ → ℝ) (u v : ℝ) : MixedJet ℝ :=
  let A := (Real.sqrt (C (-u)))⁻¹
  let B := (Real.sqrt (C (-v)))⁻¹
  let α := reflectedHalfLogSlope C u
  let β := reflectedHalfLogSlope C v
  MixedJet.mul ⟨A, -α * A, 0, 0⟩ ⟨B, 0, -β * B, 0⟩

private theorem inverseRootPairJet_isAt {C : ℝ → ℝ} (hC : Differentiable ℝ C) {u v : ℝ}
    (hu : 0 < C (-u)) (hv : 0 < C (-v)) : MixedJet.IsAt (inverseRootPairJet C) u v := by
  let A : ℝ → ℝ → MixedJet ℝ := fun x _ ↦
    ⟨(Real.sqrt (C (-x)))⁻¹,
      -reflectedHalfLogSlope C x * (Real.sqrt (C (-x)))⁻¹, 0, 0⟩
  let B : ℝ → ℝ → MixedJet ℝ := fun _ y ↦
    ⟨(Real.sqrt (C (-y)))⁻¹, 0, -reflectedHalfLogSlope C y * (Real.sqrt (C (-y)))⁻¹, 0⟩
  have hA : MixedJet.IsAt A u v := ⟨Eventually.of_forall (fun _ ↦ inverseRoot_deriv hC hu),
    hasDerivAt_const v _, hasDerivAt_const v _⟩
  have hB : MixedJet.IsAt B u v := ⟨Eventually.of_forall (fun _ ↦ hasDerivAt_const u _),
    inverseRoot_deriv hC hv, hasDerivAt_const v _⟩
  exact hA.mul hB

/-- The logarithmic slopes of the positive kernel prefactor combine with the gap curvature. -/
theorem middlePrefactor_jet {h u v : ℝ} {C : ℝ → ℝ}
    (hh : 0 < h) (hu : 0 < u) (huv : u < v) (hC : Differentiable ℝ C)
    (hCu : 0 < C (-u)) (hCv : 0 < C (-v)) :
    MixedJet.IsAt (fun x y ↦ (weightJet h x y).mul (inverseRootPairJet C x y)) u v :=
  (weightJet_isAt hh hu huv).mul (inverseRootPairJet_isAt hC hCu hCv)

private def crossProfile (h t : ℝ) : ℝ :=
  upperTailSlope h t * (1 - Real.exp (-((3 + h) * t)))

private theorem ratio_mul_gap {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    upperTailSlope h t * upperTailGap h t = Real.exp (-(h * t)) := by
  have hGap := tail_gap_pos hh ht
  rw [← upperTailGap_logDeriv hh ht, (hasDerivAt_upperTailGap hh).deriv,
    div_mul_cancel₀ _ hGap.ne']

theorem upperTailSlope_eq_inv_gap_sub_rate {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    upperTailSlope h t = (upperTailGap h t)⁻¹ - h := by
  have hF := tail_gap_pos hh ht
  apply mul_right_cancel₀ hF.ne'
  rw [ratio_mul_gap hh ht, sub_mul, inv_mul_cancel₀ hF.ne']
  linarith only [tail_gap_factor (t := t) hh]

private theorem crossCorrection_eq_profile {h u : ℝ} (hh : 0 < h) (hu : 0 < u) (d : ℝ) :
    upperTailCrossCorrection h u d =
      Real.exp (-((3 + h) * d)) * (1 + upperTailGap h d * crossProfile h u) := by
  have hf := tail_gap_pos hh hu
  have huGap : 1 - Real.exp (-(h * u)) = h * upperTailGap h u := tail_gap_factor hh
  have hdGap : 1 - Real.exp (-(h * d)) = h * upperTailGap h d := tail_gap_factor hh
  have hexp : Real.exp (-((3 + 2 * h) * u)) =
      Real.exp (-(h * u)) * Real.exp (-((3 + h) * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : upperTailSlope h u = Real.exp (-(h * u)) / upperTailGap h u := by
    apply (eq_div_iff hf.ne').2
    exact ratio_mul_gap hh hu
  unfold upperTailCrossCorrection crossProfile
  rw [hexp, hs, show Real.exp (-(h * d)) = 1 - h * upperTailGap h d by linarith only [hdGap]]
  have hlocal :
      (1 - Real.exp (-(h * u)) * Real.exp (-((3 + h) * u))) / upperTailGap h u =
        h + (Real.exp (-(h * u)) / upperTailGap h u) * (1 - Real.exp (-((3 + h) * u))) := by
    field_simp [hf.ne']
    linarith only [huGap]
  rw [mul_div_assoc, hlocal]
  ring

private theorem crossProfile_deriv {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    HasDerivAt (crossProfile h)
      (-(crossProfile h u) / upperTailGap h u +
        (3 + h) * upperTailSlope h u * Real.exp (-((3 + h) * u))) u := by
  have he := (((hasDerivAt_id' u).const_mul (3 + h)).neg).exp
  have hd := (hasDerivAt_upperTailSlope hh hu).mul (he.const_sub 1)
  refine hd.congr_deriv ?_
  simp only [crossProfile, Pi.neg_apply, mul_one]
  have hs : h + upperTailSlope h u = 1 / upperTailGap h u := by
    apply (eq_div_iff (tail_gap_pos hh hu).ne').2
    rw [add_mul, ratio_mul_gap hh hu]
    linarith only [tail_gap_factor (t := u) hh]
  rw [hs]
  ring

private def gapJet (f f₁ f₂ : ℝ → ℝ) (u v : ℝ) : MixedJet ℝ :=
  ⟨f (v - u), -f₁ (v - u), f₁ (v - u), -f₂ (v - u)⟩

private theorem gapJet_isAt {f f₁ f₂ : ℝ → ℝ}
    (hf : ∀ t > 0, HasDerivAt f (f₁ t) t) (hf₁ : ∀ t > 0, HasDerivAt f₁ (f₂ t) t)
    {u v : ℝ} (huv : u < v) : MixedJet.IsAt (gapJet f f₁ f₂) u v := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [eventually_gt_nhds huv] with y hy
    have h := (hf (y - u) (sub_pos.mpr hy)).comp u ((hasDerivAt_id' u).const_sub y)
    simpa [gapJet, Function.comp_def, mul_neg] using h
  · have h := (hf (v - u) (sub_pos.mpr huv)).comp v ((hasDerivAt_id' v).sub_const u)
    simpa [gapJet, Function.comp_def] using h
  · have h := (hf₁ (v - u) (sub_pos.mpr huv)).comp v ((hasDerivAt_id' v).sub_const u)
    change HasDerivAt (-(fun t : ℝ ↦ f₁ (t - u))) (-f₂ (v - u)) v
    simpa [Function.comp_def] using h.neg

private def crossProfileJet (h u _ : ℝ) : MixedJet ℝ :=
  ⟨crossProfile h u, -(crossProfile h u) / upperTailGap h u +
      (3 + h) * upperTailSlope h u * Real.exp (-((3 + h) * u)), 0, 0⟩

private theorem crossProfileJet_isAt {h u v : ℝ} (hh : 0 < h) (hu : 0 < u) :
    MixedJet.IsAt (crossProfileJet h) u v :=
  ⟨Eventually.of_forall (fun _ ↦ crossProfile_deriv hh hu),
    hasDerivAt_const v _, hasDerivAt_const v _⟩

private def crossDecay (h t : ℝ) : ℝ := Real.exp (-((3 + h) * t))
private def crossDecayGap (h t : ℝ) : ℝ := crossDecay h t * upperTailGap h t
private def crossRate (h t : ℝ) : ℝ := (3 + 2 * h) * upperTailGap h t - 1

private theorem crossDecay_deriv (h t : ℝ) :
    HasDerivAt (crossDecay h) (-(3 + h) * crossDecay h t) t := by
  have h := (((hasDerivAt_id' t).const_mul (3 + h)).neg).exp
  unfold crossDecay
  convert h using 1 <;> simp only [Pi.neg_apply, mul_one] <;> ring

private theorem crossDecayGap_deriv {h t : ℝ} (hh : 0 < h) :
    HasDerivAt (crossDecayGap h) (-(crossDecay h t * crossRate h t)) t := by
  refine ((crossDecay_deriv h t).mul (hasDerivAt_upperTailGap hh)).congr_deriv ?_
  have he : Real.exp (-(h * t)) = 1 - h * upperTailGap h t := by
    linarith only [tail_gap_factor (t := t) hh]
  rw [he]
  unfold crossRate
  ring

private theorem crossDecayGap_second {h t : ℝ} (hh : 0 < h) :
    HasDerivAt (fun x ↦ -(crossDecay h x * crossRate h x))
      (-(crossDecay h t * ((3 + h) - (3 + 2 * h) * crossRate h t))) t := by
  have hr := ((hasDerivAt_upperTailGap (t := t) hh).const_mul (3 + 2 * h)).sub_const 1
  refine ((crossDecay_deriv h t).mul hr).neg.congr_deriv ?_
  have he : Real.exp (-(h * t)) = 1 - h * upperTailGap h t := by
    linarith only [tail_gap_factor (t := t) hh]
  rw [he]
  unfold crossRate
  ring

private def quadraticWeight (h t : ℝ) : ℝ :=
  c h * (upperTailGap h t) ^ 2 * Real.exp (-(2 * t))

private def Xfirst (h t : ℝ) : ℝ :=
  2 * c h * crossDecayGap h t + 2 * quadraticWeight h t * profileSlope h t

private def Xsecond (h t : ℝ) : ℝ :=
  2 * quadraticWeight h t * (profileCurvature h t - 2 * profileSlope h t ^ 2) -
    2 * c h * crossDecay h t * crossRate h t

private theorem Xfirst_deriv {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (X h) (Xfirst h t) t := by
  have hLambda := (hasDerivAt_upperTailLambda (t := t) hh).const_sub 1
  refine hLambda.congr_deriv ?_
  have he : Real.exp (-((3 + h) * t)) = Real.exp (-(2 * t)) *
      Real.exp (-((1 + h) * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold Xfirst quadraticWeight crossDecayGap crossDecay c profileSlope
  rw [he]
  have hf := ratio_mul_gap hh ht
  have hg := tail_gap_factor (t := t) hh
  have hl : upperTailGap h t * (1 - upperTailSlope h t) =
      (1 + h) * upperTailGap h t - 1 := by nlinarith only [hf, hg]
  linear_combination
    -(3 + h) * (3 + 2 * h) * Real.exp (-(2 * t)) * upperTailGap h t * hl

private theorem quadraticWeight_deriv {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (quadraticWeight h) (-2 * quadraticWeight h t * profileSlope h t) t := by
  have he := (((hasDerivAt_id' t).const_mul (2 : ℝ)).neg).exp
  have hw := (((hasDerivAt_upperTailGap hh).pow 2).const_mul (c h)).mul he
  refine hw.congr_deriv ?_
  rw [← ratio_mul_gap hh ht]
  unfold quadraticWeight profileSlope
  simp only [Pi.neg_apply, Pi.pow_apply, mul_one]
  ring

private theorem Xsecond_deriv {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    HasDerivAt (Xfirst h) (Xsecond h t) t := by
  have hFirst := (crossDecayGap_deriv (t := t) hh).const_mul (2 * c h)
  have hSecond := ((quadraticWeight_deriv hh ht).const_mul 2).mul (hasDerivAt_profileSlope hh ht)
  exact (hFirst.add hSecond).congr_deriv (by unfold Xsecond; ring)

private def upperRadicandJet (h _ v : ℝ) : MixedJet ℝ :=
  ⟨X h v, 0, Xfirst h v, 0⟩

private theorem upperRadicandJet_isAt {h u v : ℝ} (hh : 0 < h) (hv : 0 < v) :
    MixedJet.IsAt (upperRadicandJet h) u v :=
  ⟨Eventually.of_forall (fun _ ↦ hasDerivAt_const u _), Xfirst_deriv hh hv, hasDerivAt_const v _⟩

private def radicandJet (h u v : ℝ) : MixedJet ℝ :=
  (upperRadicandJet h u v).mul (gapJet (X h) (Xfirst h) (Xsecond h) u v)

private def radicalJet (h u v : ℝ) : MixedJet ℝ :=
  (radicandJet h u v).sqrtFrom (Real.sqrt (radicandJet h u v).value)

private theorem radicalJet_isAt {p : ℕ} (hp : 0 < p) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    MixedJet.IsAt (radicalJet (rate p)) u v := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < rate p := by unfold rate; positivity
  have hv := hu.trans huv
  have hd := sub_pos.mpr huv
  have hg := gapJet_isAt (fun t ht ↦ Xfirst_deriv hh ht) (fun t ht ↦ Xsecond_deriv hh ht) huv
  exact ((upperRadicandJet_isAt hh hv).mul hg).sqrtFrom (mul_pos (X_pos hp hv) (X_pos hp hd))

private def crossDefectJet (h u v : ℝ) : MixedJet ℝ :=
  let E := gapJet (crossDecay h) (fun t ↦ -(3 + h) * crossDecay h t)
    (fun t ↦ (3 + h) ^ 2 * crossDecay h t) u v
  let A := gapJet (crossDecayGap h) (fun t ↦ -(crossDecay h t * crossRate h t))
    (fun t ↦ -(crossDecay h t * ((3 + h) - (3 + 2 * h) * crossRate h t))) u v
  (⟨1, 0, 0, 0⟩ : MixedJet ℝ).sub (E.add (A.mul (crossProfileJet h u v)))

private theorem crossDefectJet_isAt {h u v : ℝ} (hh : 0 < h) (hu : 0 < u) (huv : u < v) :
    MixedJet.IsAt (crossDefectJet h) u v := by
  have hconst : MixedJet.IsAt (fun (_ _ : ℝ) ↦ ⟨1, 0, 0, 0⟩) u v :=
    ⟨Eventually.of_forall (fun _ ↦ hasDerivAt_const u _), hasDerivAt_const v _,
      hasDerivAt_const v _⟩
  have hE := gapJet_isAt (f₂ := fun t ↦ (3 + h) ^ 2 * crossDecay h t)
    (fun t _ ↦ crossDecay_deriv h t) (fun t _ ↦ by
    have hd := (crossDecay_deriv h t).const_mul (-(3 + h))
    exact hd.congr_deriv (by ring)) huv
  have hA := gapJet_isAt (fun _ _ ↦ crossDecayGap_deriv hh)
    (fun _ _ ↦ crossDecayGap_second hh) huv
  exact hconst.sub (hE.add (hA.mul (crossProfileJet_isAt hh hu)))

private def middleJet (p : ℕ) (u v : ℝ) : MixedJet ℝ :=
  let h := rate p
  let L := weightJet h u v
  let N := inverseRootPairJet (compositionMoment p 0) u v
  ((L.mul N).mul ((crossDefectJet h u v).sub (radicalJet h u v))).sub N

private theorem middleJet_value {p : ℕ} (hp : 0 < p) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    (middleJet p u v).value = logKernel p u v := by
  let h := rate p
  let d := v - u
  let f := upperTailGap h
  let P := c h * f v * f d * Real.exp (-(v + d))
  let L := leftStripWeight h u v
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by unfold h rate; positivity
  have hv := hu.trans huv
  have hd := sub_pos.mpr huv
  have hc : 0 < c h := by unfold c; positivity
  have hfv : 0 < f v := tail_gap_pos hh hv
  have hfd : 0 < f d := tail_gap_pos hh hd
  have hLP : L * P = 1 := by
    unfold L P
    rw [weight_closed hh hv huv]
    change Real.exp (v + d) / (c h * f v * f d) *
      (c h * f v * f d * Real.exp (-(v + d))) = 1
    calc
      _ = Real.exp (v + d) * Real.exp (-(v + d)) := by
        field_simp [hc.ne', hfv.ne', hfd.ne']
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hCu := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne')
  let den := Real.sqrt (compositionMoment p 0 (-u) * compositionMoment p 0 (-v))
  have hN : (inverseRootPairJet (compositionMoment p 0) u v).value = 1 / den := by
    unfold inverseRootPairJet MixedJet.mul den
    dsimp only
    rw [Real.sqrt_mul hCu.le, one_div, mul_inv_rev, mul_comm]
  have hW : (crossDefectJet h u v).value = 1 - upperTailCrossCorrection h u d := by
    rw [crossCorrection_eq_profile hh hu d]
    unfold crossDefectJet MixedJet.sub MixedJet.add MixedJet.mul gapJet crossDecayGap
    dsimp only [crossProfileJet, crossDecay, d]
    ring
  have hR : (radicalJet h u v).value = Real.sqrt (X h v * X h d) := rfl
  have hk := logKernel_eq_middleGap hp hu huv
  change logKernel p u v = L / den *
    (1 - upperTailCrossCorrection h u d - Real.sqrt (X h v * X h d) - P) at hk
  rw [hk]
  change (L * (inverseRootPairJet (compositionMoment p 0) u v).value) *
    ((crossDefectJet h u v).value - (radicalJet h u v).value) -
      (inverseRootPairJet (compositionMoment p 0) u v).value = _
  rw [hN, hW, hR]
  linear_combination (1 / den) * hLP

/-- The jet differentiates the original log kernel in the independent coordinates. -/
theorem logKernel_mixed_eq_middleJet {p : ℕ} (hp : 0 < p) {u v : ℝ} (hu : 0 < u)
    (huv : u < v) (hC : Differentiable ℝ (compositionMoment p 0)) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v = (middleJet p u v).duv := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < rate p := by unfold rate; positivity
  have hv := hu.trans huv
  have hCu := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne')
  have hCv := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne')
  have hN := inverseRootPairJet_isAt hC hCu hCv
  have hj : MixedJet.IsAt (middleJet p) u v :=
    ((middlePrefactor_jet hh hu huv hC hCu hCv).mul
      ((crossDefectJet_isAt hh hu huv).sub (radicalJet_isAt hp hu huv))).sub hN
  have hNear : (fun y ↦ deriv (fun x ↦ logKernel p x y) u) =ᶠ[𝓝 v]
      (fun y ↦ (middleJet p u y).du) := by
    filter_upwards [hj.1, eventually_gt_nhds huv] with y hy hUy
    have hEq : (fun x ↦ logKernel p x y) =ᶠ[𝓝 u] (fun x ↦ (middleJet p x y).value) := by
      filter_upwards [eventually_gt_nhds hu, eventually_lt_nhds hUy] with x hx hxy
      exact (middleJet_value hp hx hxy).symm
    exact hEq.deriv_eq.trans hy.deriv
  exact hNear.deriv_eq.trans hj.2.2.deriv

private theorem radicalJet_algebra {x y a b k : ℝ} (hx : 0 < x) (hy : 0 < y) :
    let r := Real.sqrt (x * y)
    (⟨x * y, -2 * a * x, 2 * b * y + 2 * a * x, -2 * k * x - 4 * a * b⟩ :
      MixedJet ℝ).sqrtFrom r =
        ⟨r, -r * (a / y), r * (a / y + b / x),
          -r * (k / y + a * (b * y - a * x) / (y ^ 2 * x))⟩ := by
  let r := Real.sqrt (x * y)
  have hrsq : r ^ 2 = x * y := Real.sq_sqrt (mul_pos hx hy).le
  have hr : 0 < r := Real.sqrt_pos.mpr (mul_pos hx hy)
  have hi : r⁻¹ = r / (x * y) := by
    rw [← hrsq]
    field_simp [hr.ne'] <;> ring
  have hq : 1 / (2 * r) = r⁻¹ / 2 := by
    field_simp [hr.ne'] <;> ring
  have hq3 : (r⁻¹ / 2) * (r⁻¹ / 2) * (1 / r) = r⁻¹ / (4 * (x * y)) := by
    rw [← hrsq]
    field_simp [hr.ne'] <;> ring
  change (⟨r, (1 / (2 * r)) * (-2 * a * x),
      (1 / (2 * r)) * (2 * b * y + 2 * a * x),
      (1 / (2 * r)) * (-2 * k * x - 4 * a * b) -
        (1 / (2 * r)) * (1 / (2 * r)) * (1 / r) *
          (-2 * a * x) * (2 * b * y + 2 * a * x)⟩ : MixedJet ℝ) = _
  rw [hq, hq3, hi]
  congr 1 <;> field_simp [hx.ne', hy.ne'] <;> ring

/-- The middle-gap derivative is affine in the positive square root, after
the square of that root is eliminated using the product of its two arguments. -/
theorem middleJet_duv_factor {p : ℕ} (hp : 0 < p) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    let h := rate p
    let d := v - u
    let L := leftStripWeight h u v
    let C := compositionMoment p 0
    let N := (inverseRootPairJet C u v).value
    let α := reflectedHalfLogSlope C u
    let β := reflectedHalfLogSlope C v
    let U := profileSlope h d + α
    let V := profileSlope h v + profileSlope h d - β
    let J := profileCurvature h d + U * V
    let x := X h v
    let y := X h d
    let a := Xfirst h d / 2
    let b := Xfirst h v / 2
    let k := Xsecond h d / 2
    let W := crossDefectJet h u v
    let M := W.duv - U * W.dv + V * W.du - α * β / L
    let R := (k + (U + V) * a) * y * x + U * b * y ^ 2 + a * (b * y - a * x)
    (middleJet p u v).duv =
      L * N * (M - J * W.value + Real.sqrt (x * y) * (J + R / (y ^ 2 * x))) := by
  dsimp only
  let h := rate p
  let d := v - u
  let x := X h v
  let y := X h d
  let a := Xfirst h d / 2
  let b := Xfirst h v / 2
  let k := Xsecond h d / 2
  have hx : 0 < x := X_pos hp (hu.trans huv)
  have hy : 0 < y := X_pos hp (sub_pos.mpr huv)
  have hL : 0 < leftStripWeight h u v := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hh : 0 < h := by dsimp [h, rate]; positivity
    unfold leftStripWeight
    positivity
  have hrad : radicalJet h u v =
      ⟨Real.sqrt (x * y), -Real.sqrt (x * y) * (a / y),
        Real.sqrt (x * y) * (a / y + b / x),
        -Real.sqrt (x * y) * (k / y + a * (b * y - a * x) / (y ^ 2 * x))⟩ := by
    rw [← radicalJet_algebra (a := a) (b := b) (k := k) hx hy]
    unfold radicalJet radicandJet upperRadicandJet gapJet MixedJet.mul
    dsimp only [x, y, a, b, k, h, d]
    congr 1 <;> ring
  unfold middleJet
  dsimp only
  rw [hrad]
  simp only [weightJet, inverseRootPairJet, MixedJet.mul, MixedJet.sub, a, b, k]
  dsimp only [x, y, h, d] at hx hy hL ⊢
  generalize X (rate p) v = x' at hx ⊢
  generalize X (rate p) (v - u) = y' at hy ⊢
  generalize leftStripWeight (rate p) u v = L' at hL ⊢
  field_simp [hL.ne', hx.ne', hy.ne'] <;> ring

private def middlePolynomialParts (p : ℕ) (u v α β : ℝ) : ℝ × ℝ × ℝ :=
  let h := rate p
  let d := v - u
  let x := X h v
  let y := X h d
  let a := Xfirst h d / 2
  let b := Xfirst h v / 2
  let k := Xsecond h d / 2
  let U := profileSlope h d + α
  let V := profileSlope h v + profileSlope h d - β
  let W := crossDefectJet h u v
  let M := W.duv - U * W.dv + V * W.du - α * β / leftStripWeight h u v
  let J := profileCurvature h d + U * V
  let R := (k + (U + V) * a) * y * x + U * b * y ^ 2 + a * (b * y - a * x)
  (M, J, R)

/-- The zero-radical test and the denominator-cleared upper-radical test. -/
def middleEndpointScores (p : ℕ) (u v α β μ : ℝ) : ℝ × ℝ :=
  let h := rate p
  let x := X h v
  let y := X h (v - u)
  let W := (crossDefectJet h u v).value
  let S := x + y
  let H := y ^ 2 * x
  let A := S ^ 2 / 2 - (x - y) ^ 2 / 4
  let (M, J, R) := middlePolynomialParts p u v α β
  (M - J * W + μ, H * (S * M + (A - S * W) * J) + A * R + H * S * μ)

/-- Reexpress the endpoint scores using the common gap weight and the two
scaled radicand defects. -/
private theorem middleEndpointScores_eq_scaled (p : ℕ) (u v α β μ : ℝ)
    {w δx δy E M₀ R₀ : ℝ}
    (hx : 1 - X (rate p) v = w * δx)
    (hy : 1 - X (rate p) (v - u) = w * δy)
    (hW : 1 - (crossDefectJet (rate p) u v).value = w * E)
    (hM : (middlePolynomialParts p u v α β).1 = w * M₀)
    (hR : (middlePolynomialParts p u v α β).2.2 = w * R₀) :
    let x := X (rate p) v
    let y := X (rate p) (v - u)
    let S := x + y
    let H := y ^ 2 * x
    let B := (E - (δx + δy) / 2) * S - w * (δy - δx) ^ 2 / 4
    let A := S ^ 2 / 2 - w ^ 2 * (δy - δx) ^ 2 / 4
    let J := (middlePolynomialParts p u v α β).2.1
    middleEndpointScores p u v α β μ =
      (w * M₀ - J * (crossDefectJet (rate p) u v).value + μ,
        w * (H * (S * M₀ + B * J) + A * R₀) + H * S * μ) := by
  have hdiff : X (rate p) v - X (rate p) (v - u) = w * (δy - δx) := by
    linear_combination hy - hx
  have hsum : X (rate p) v + X (rate p) (v - u) =
      2 - w * (δx + δy) := by
    linear_combination -hx - hy
  have hoffset : (X (rate p) v + X (rate p) (v - u)) / 2 -
      (crossDefectJet (rate p) u v).value = w * (E - (δx + δy) / 2) := by
    linear_combination (1 / 2 : ℝ) * hsum + hW
  let x := X (rate p) v
  let y := X (rate p) (v - u)
  let S := X (rate p) v + X (rate p) (v - u)
  let H := y ^ 2 * x
  let W := (crossDefectJet (rate p) u v).value
  let J := (middlePolynomialParts p u v α β).2.1
  let M := (middlePolynomialParts p u v α β).1
  let R := (middlePolynomialParts p u v α β).2.2
  have hB : S ^ 2 / 2 - (w * (δy - δx)) ^ 2 / 4 - S * W =
      w * ((E - (δx + δy) / 2) * S - w * (δy - δx) ^ 2 / 4) := by
    change S / 2 - W = _ at hoffset
    calc
      _ = S * (S / 2 - W) - (w * (δy - δx)) ^ 2 / 4 := by ring
      _ = _ := by rw [hoffset]; ring
  let A := S ^ 2 / 2 - (x - y) ^ 2 / 4
  change (M - J * W + μ, H * (S * M + (A - S * W) * J) + A * R + H * S * μ) =
    (w * M₀ - J * W + μ, w * (H * (S * M₀ +
      ((E - (δx + δy) / 2) * S - w * (δy - δx) ^ 2 / 4) * J) +
      (S ^ 2 / 2 - w ^ 2 * (δy - δx) ^ 2 / 4) * R₀) + H * S * μ)
  have hA : A = S ^ 2 / 2 - (w * (δy - δx)) ^ 2 / 4 := by
    change S ^ 2 / 2 - (X (rate p) v - X (rate p) (v - u)) ^ 2 / 4 = _
    rw [hdiff]
  change M = _ at hM
  change R = _ at hR
  rw [hM, hR, hA, hB]
  exact Prod.ext rfl (by ring)

private theorem middleRadicandDefect (h s : ℝ) :
    1 - X h s = quadraticWeight h s + crossDecay h s * (1 + (3 + h) * upperTailGap h s) := by
  unfold X upperTailLambda quadraticWeight crossDecay c
  ring

private theorem middleCrossDefect (h u v : ℝ) :
    1 - (crossDefectJet h u v).value =
      crossDecay h (v - u) * (1 + upperTailGap h (v - u) * crossProfile h u) := by
  simp only [crossDefectJet, MixedJet.sub, MixedJet.add, MixedJet.mul, gapJet,
    crossProfileJet, crossDecayGap]
  ring

/-- The endpoint tests in terms of the three ratios used by the Taylor replay. -/
theorem middleEndpointScores_eq_replay (p : ℕ) (u v α β μ : ℝ)
    {e q r : ℝ}
    (he : quadraticWeight (rate p) (v - u) * e = crossDecay (rate p) (v - u))
    (hq : quadraticWeight (rate p) (v - u) * q = quadraticWeight (rate p) v)
    (hr : quadraticWeight (rate p) (v - u) * r = (leftStripWeight (rate p) u v)⁻¹) :
    let h := rate p
    let d := v - u
    let w := quadraticWeight h d
    let x := X h v
    let y := X h d
    let F := upperTailGap h
    let U := profileSlope h d + α
    let V := profileSlope h v + profileSlope h d - β
    let J := profileCurvature h d + U * V
    let g := 3 + h
    let m := crossRate h d
    let T := crossProfile h u
    let T₁ := (crossProfileJet h u v).du
    let a := profileSlope h d + c h * F d * e
    let b := q * profileSlope h v + c h * F v * e * crossDecay h u
    let k := profileCurvature h d - 2 * profileSlope h d ^ 2 - c h * e * m
    let Wv := e * (g + m * T)
    let Wu := -e * (F d * T₁ + g + m * T)
    let Wuv := e * (m * T₁ + g ^ 2 - (g - (3 + 2 * h) * m) * T)
    let M := Wuv - U * Wv + V * Wu - α * β * r
    let R := (k + (U + V) * a) * y * x + U * b * y ^ 2 + w * a * (b * y - a * x)
    let δx := q + e * crossDecay h u * (1 + g * F v)
    let δy := 1 + e * (1 + g * F d)
    let E := e * (1 + F d * T)
    let S := x + y
    let H := y ^ 2 * x
    let B := (E - (δx + δy) / 2) * S - w * (δy - δx) ^ 2 / 4
    let A := S ^ 2 / 2 - w ^ 2 * (δy - δx) ^ 2 / 4
    middleEndpointScores p u v α β μ =
      (w * M - J * (crossDefectJet h u v).value + μ,
        w * (H * (S * M + B * J) + A * R) + H * S * μ) := by
  let h := rate p
  let d := v - u
  let w := quadraticWeight h d
  let F := upperTailGap h
  let g := 3 + h
  let m := crossRate h d
  let T := crossProfile h u
  let T₁ := (crossProfileJet h u v).du
  let W := crossDefectJet h u v
  have he₁ : crossDecay h v = (w * e) * crossDecay h u := by
    change w * e = crossDecay h d at he
    rw [he]
    unfold crossDecay
    rw [← Real.exp_add]
    congr 1
    dsimp only [g, d]
    ring
  have ha : Xfirst h d / 2 = w * (profileSlope h d + c h * F d * e) := by
    unfold Xfirst crossDecayGap
    change (2 * c h * (crossDecay h d * F d) + 2 * w * profileSlope h d) / 2 = _
    linear_combination -(c h * F d) * he
  have hb : Xfirst h v / 2 =
      w * (q * profileSlope h v + c h * F v * e * crossDecay h u) := by
    unfold Xfirst crossDecayGap
    rw [he₁, ← hq]
    ring
  have hk : Xsecond h d / 2 =
      w * (profileCurvature h d - 2 * profileSlope h d ^ 2 - c h * e * m) := by
    unfold Xsecond
    change (2 * w * (profileCurvature h d - 2 * profileSlope h d ^ 2) -
      2 * c h * crossDecay h d * m) / 2 = _
    linear_combination (c h * m) * he
  have hV : W.dv = (w * e) * (g + m * T) := by
    dsimp only [W, crossDefectJet, MixedJet.sub, MixedJet.add, MixedJet.mul, gapJet,
      crossProfileJet, crossDecayGap, m, g, T]
    rw [he]
    ring
  have hU : W.du = -(w * e) * (F d * T₁ + g + m * T) := by
    dsimp only [W, crossDefectJet, MixedJet.sub, MixedJet.add, MixedJet.mul, gapJet,
      crossProfileJet, crossDecayGap, m, g, T, T₁, F]
    rw [he]
    ring
  have hUV : W.duv = (w * e) * (m * T₁ + g ^ 2 - (g - (3 + 2 * h) * m) * T) := by
    dsimp only [W, crossDefectJet, MixedJet.sub, MixedJet.add, MixedJet.mul, gapJet,
      crossProfileJet, crossDecayGap, m, g, T, T₁]
    rw [he]
    ring
  let U := profileSlope h d + α
  let V := profileSlope h v + profileSlope h d - β
  let x := X h v
  let y := X h d
  let a := profileSlope h d + c h * F d * e
  let b := q * profileSlope h v + c h * F v * e * crossDecay h u
  let k := profileCurvature h d - 2 * profileSlope h d ^ 2 - c h * e * m
  have hratio : α * β / leftStripWeight h u v = α * β * (w * r) := by
    rw [div_eq_mul_inv, hr]
  have hM : (middlePolynomialParts p u v α β).1 =
      w * (e * (m * T₁ + g ^ 2 - (g - (3 + 2 * h) * m) * T) -
        U * (e * (g + m * T)) + V * (-e * (F d * T₁ + g + m * T)) - α * β * r) := by
    change W.duv - U * W.dv + V * W.du - α * β / leftStripWeight h u v = _
    rw [hV, hU, hUV, hratio]
    ring
  have hR : (middlePolynomialParts p u v α β).2.2 = w *
      ((k + (U + V) * a) * y * x + U * b * y ^ 2 + w * a * (b * y - a * x)) := by
    change (Xsecond h d / 2 + (U + V) * (Xfirst h d / 2)) * y * x +
      U * (Xfirst h v / 2) * y ^ 2 +
      (Xfirst h d / 2) * (Xfirst h v / 2 * y - Xfirst h d / 2 * x) = _
    rw [ha, hb, hk]
    change (w * k + (U + V) * (w * a)) * y * x + U * (w * b) * y ^ 2 +
      (w * a) * (w * b * y - w * a * x) = _
    ring
  have hδx : 1 - x = w * (q + e * crossDecay h u * (1 + g * F v)) := by
    change 1 - X h v = _
    rw [middleRadicandDefect, he₁, ← hq]
    change w * q + w * e * crossDecay h u * (1 + g * F v) = _
    ring
  have hδy : 1 - y = w * (1 + e * (1 + g * F d)) := by
    change 1 - X h d = _
    rw [middleRadicandDefect, ← he]
    change w + (w * e) * (1 + g * F d) = _
    ring
  have hE : 1 - W.value = w * (e * (1 + F d * T)) := by
    change 1 - (crossDefectJet h u v).value = _
    rw [middleCrossDefect, ← he]
    change (w * e) * (1 + F d * T) = _
    ring
  exact middleEndpointScores_eq_scaled p u v α β μ hδx hδy hE hM hR

theorem middleReplayRatios {h u v : ℝ} (hh : 0 < h) (hu : 0 < u) (huv : u < v) :
    let d := v - u
    let F := upperTailGap h
    let w := quadraticWeight h d
    w * (Real.exp (-((1 + h) * d)) / (c h * F d ^ 2)) = crossDecay h d ∧
    w * (Real.exp (-(2 * u)) * (F v / F d) ^ 2) = quadraticWeight h v ∧
    w * (Real.exp (-u) * (F v / F d)) = (leftStripWeight h u v)⁻¹ := by
  let d := v - u
  let F := upperTailGap h
  have hF : 0 < F d := tail_gap_pos hh (sub_pos.mpr huv)
  have hc : 0 < c h := by unfold c; positivity
  have hfirst : Real.exp (-(2 * d)) * Real.exp (-((1 + h) * d)) = crossDecay h d := by
    rw [← Real.exp_add]
    unfold crossDecay
    congr 1
    ring
  have hsecond : Real.exp (-(2 * d)) * Real.exp (-(2 * u)) = Real.exp (-(2 * v)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [d]
    ring
  have hthird : Real.exp (-(2 * d)) * Real.exp (-u) = Real.exp (-(v + d)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [d]
    ring
  refine ⟨?_, ?_, ?_⟩
  · change (c h * F d ^ 2 * Real.exp (-(2 * d))) *
        (Real.exp (-((1 + h) * d)) / (c h * F d ^ 2)) = crossDecay h d
    rw [← hfirst]
    field_simp [hc.ne', hF.ne']
    <;> ring
  · change (c h * F d ^ 2 * Real.exp (-(2 * d))) *
        (Real.exp (-(2 * u)) * (F v / F d) ^ 2) =
      c h * F v ^ 2 * Real.exp (-(2 * v))
    rw [← hsecond]
    field_simp [hF.ne']
    <;> ring
  · have hL : (leftStripWeight h u v)⁻¹ =
        c h * F v * F d * Real.exp (-(v + d)) := by
      rw [weight_closed hh (hu.trans huv) huv, inv_div, div_eq_mul_inv, Real.exp_neg]
    change (c h * F d ^ 2 * Real.exp (-(2 * d))) *
        (Real.exp (-u) * (F v / F d)) = (leftStripWeight h u v)⁻¹
    rw [hL, ← hthird]
    field_simp [hF.ne']
    <;> ring

/-- At each pair of slope endpoints, the two polynomial tests bound the
derivative at the actual square root. Interpolation then fixes the slopes. -/
theorem logKernel_mixed_neg_of_middle_corner_scores {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hC : Differentiable ℝ (compositionMoment p 0))
    {α₀ α₁ β₀ β₁ μ : ℝ} (hμ : 0 ≤ μ)
    (hα₀ : α₀ ≤ reflectedHalfLogSlope (compositionMoment p 0) u)
    (hα₁ : reflectedHalfLogSlope (compositionMoment p 0) u ≤ α₁)
    (hβ₀ : β₀ ≤ reflectedHalfLogSlope (compositionMoment p 0) v)
    (hβ₁ : reflectedHalfLogSlope (compositionMoment p 0) v ≤ β₁)
    (hcorner : ∀ α β : ℝ, (α = α₀ ∨ α = α₁) → (β = β₀ ∨ β = β₁) →
      (middleEndpointScores p u v α β μ).1 < 0 ∧
      (middleEndpointScores p u v α β μ).2 < 0) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h := rate p
  let d := v - u
  let x := X h v
  let y := X h d
  let S := x + y
  let A := S ^ 2 / 2 - (x - y) ^ 2 / 4
  let H := y ^ 2 * x
  let W := crossDefectJet h u v
  let L := leftStripWeight h u v
  let C := compositionMoment p 0
  let N := (inverseRootPairJet C u v).value
  let U := profileSlope h d
  let V := profileSlope h v + profileSlope h d
  let a := Xfirst h d / 2
  let b := Xfirst h v / 2
  let k := Xsecond h d / 2
  let r := Real.sqrt (x * y)
  let Z := r - W.value
  let f (α β : ℝ) :=
    let (M, J, R) := middlePolynomialParts p u v α β
    M - J * W.value + r * (J + R / H)
  have hx : 0 < x := X_pos hp (hu.trans huv)
  have hy : 0 < y := X_pos hp (sub_pos.mpr huv)
  have hzero (α β : ℝ) (ha : α = α₀ ∨ α = α₁) (hb : β = β₀ ∨ β = β₁) :
      f α β < 0 := by
    let parts := middlePolynomialParts p u v α β
    have hc := hcorner α β ha hb
    have hB : A - S * W.value = 1 * (A - S * W.value) := by rw [one_mul]
    have h := middle_radical_lt_of_endpoints (x := x) (y := y) (w := 1)
      (J := parts.2.1) (W := W.value) (M := parts.1) (R := parts.2.2)
      (B := A - S * W.value) (μ := μ)
      hx hy hB (by simpa only [middleEndpointScores, one_mul] using hc.1)
      (by simpa only [middleEndpointScores, one_mul] using hc.2)
    have hm : -μ ≤ 0 := neg_nonpos.mpr hμ
    simpa only [f, one_mul, H, r] using h.trans_le hm
  let c₀ := W.duv - U * W.dv + V * W.du +
    (profileCurvature h d + U * V) * Z +
      r * (((k + (U + V) * a) * y * x + U * b * y ^ 2 + a * (b * y - a * x)) / H)
  let cα := -W.dv + V * Z + r * ((a * y * x + b * y ^ 2) / H)
  let cβ := -W.du - U * Z - r * (a * y * x / H)
  let cαβ := -1 / L - Z
  have hf (α β : ℝ) : f α β = c₀ + cα * α + cβ * β + cαβ * α * β := by
    unfold f middlePolynomialParts c₀ cα cβ cαβ
    dsimp only [U, V, Z, a, b, k, x, y, H, L, h, d]
    simp only [div_eq_mul_inv]
    ring
  have h₀₀ := hzero α₀ β₀ (.inl rfl) (.inl rfl)
  have h₀₁ := hzero α₀ β₁ (.inl rfl) (.inr rfl)
  have h₁₀ := hzero α₁ β₀ (.inr rfl) (.inl rfl)
  have h₁₁ := hzero α₁ β₁ (.inr rfl) (.inr rfl)
  simp only [hf] at h₀₀ h₀₁ h₁₀ h₁₁
  have hsign := bilinear_lt_zero_of_corners hα₀ hα₁ hβ₀ hβ₁ h₀₀ h₀₁ h₁₀ h₁₁
  rw [← hf] at hsign
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by unfold h rate; positivity
  have hL : 0 < L := by unfold L leftStripWeight; positivity
  have hCu := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hu.ne')
  have hCv := compositionMoment_marginal_pos hp (neg_ne_zero.mpr (hu.trans huv).ne')
  have hN : 0 < N := by
    change 0 < (Real.sqrt (C (-u)))⁻¹ * (Real.sqrt (C (-v)))⁻¹
    exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hCu)) (inv_pos.mpr (Real.sqrt_pos.mpr hCv))
  rw [logKernel_mixed_eq_middleJet hp hu huv hC, middleJet_duv_factor hp hu huv]
  exact mul_neg_of_pos_of_neg (mul_pos hL hN) hsign

end

end RefinedBMV.PositiveCenter.CompactGap
