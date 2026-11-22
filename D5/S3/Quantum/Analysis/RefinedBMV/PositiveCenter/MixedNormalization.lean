/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MixedNormalization
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed differentiation of the marginal normalization and radical. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMixedJet
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Mixed derivatives of the marginal normalization -/

open Filter
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

def marginalLogSlope (R : ℝ → ℝ) (t : ℝ) : ℝ := deriv R t / R t

def reflectedHalfLogSlope (R : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (fun s ↦ R (-s)) t / R (-t) / 2

private theorem root_deriv {R : ℝ → ℝ} {t : ℝ} (hR : DifferentiableAt ℝ R t)
    (ht : 0 < R t) :
    HasDerivAt (fun x ↦ Real.sqrt (R x))
      (marginalLogSlope R t / 2 * Real.sqrt (R t)) t := by
  refine (hR.hasDerivAt.sqrt ht.ne').congr_deriv ?_
  have hs := (Real.sqrt_pos.mpr ht).ne'
  unfold marginalLogSlope
  field_simp [hs, ht.ne']
  rw [Real.sq_sqrt ht.le]

private theorem inverseRoot_deriv {R : ℝ → ℝ} {t : ℝ} (hR : Differentiable ℝ R)
    (ht : 0 < R (-t)) :
    HasDerivAt (fun x ↦ (Real.sqrt (R (-x)))⁻¹)
      (-reflectedHalfLogSlope R t * (Real.sqrt (R (-t)))⁻¹) t := by
  have h := root_deriv ((hR (-t)).comp t (differentiableAt_id.neg)) ht
  refine (h.inv (Real.sqrt_pos.mpr ht).ne').congr_deriv ?_
  change -(marginalLogSlope (fun x ↦ R (-x)) t / 2 * Real.sqrt (R (-t))) /
    Real.sqrt (R (-t)) ^ 2 = _
  unfold reflectedHalfLogSlope marginalLogSlope
  field_simp [(Real.sqrt_pos.mpr ht).ne']

private def gapRootJet (R : ℝ → ℝ) (u v : ℝ) : MixedJet ℝ :=
  let d := v-u
  let C := Real.sqrt (R d)
  let r := marginalLogSlope R
  ⟨C, -(r d / 2) * C, r d / 2 * C, (-deriv r d / 2 - (r d / 2)^2) * C⟩

private theorem gapRootJet_isAt {R : ℝ → ℝ} (hR : ContDiff ℝ 2 R) {u v : ℝ}
    (hpos : ∀ t ≠ 0, 0 < R t) (huv : u < v) : MixedJet.IsAt (gapRootJet R) u v := by
  let r := marginalLogSlope R
  let d := v-u
  have hdiff := hR.differentiable (by norm_num)
  have hc := root_deriv (hdiff d) (hpos d (sub_ne_zero.mpr huv.ne'))
  have hV : HasDerivAt (fun y ↦ Real.sqrt (R (y-u))) (r d / 2 * Real.sqrt (R d)) v := by
    have hd := hc.comp v ((hasDerivAt_id' v).sub_const u)
    change HasDerivAt (fun y ↦ Real.sqrt (R (y-u))) (_ * 1) v at hd
    simpa only [mul_one] using hd
  refine ⟨?_, hV, ?_⟩
  · filter_upwards [eventually_gt_nhds huv] with y hy
    have hs := root_deriv (hdiff (y-u)) (hpos (y-u) (sub_ne_zero.mpr hy.ne'))
    have hd := hs.comp u ((hasDerivAt_const u y).fun_sub (hasDerivAt_id' u))
    change HasDerivAt (fun x ↦ Real.sqrt (R (y-x))) (_ * (0-1)) u at hd
    simpa only [gapRootJet, zero_sub, mul_neg_one, neg_mul] using hd
  · have hr : DifferentiableAt ℝ r d :=
      (hR.differentiable_deriv_two d).div (hdiff d) (hpos d (sub_ne_zero.mpr huv.ne')).ne'
    have hd := hr.hasDerivAt.comp v ((hasDerivAt_id' v).sub_const u)
    refine (((hd.div_const 2).neg).mul hV).congr_deriv ?_
    change -(deriv r d * 1 / 2) * Real.sqrt (R d) +
      -(r d / 2) * (r d / 2 * Real.sqrt (R d)) = _
    dsimp only [gapRootJet]
    ring

/-- Mixed derivative of a centered joint moment minus the marginal radical
after division by the two reflected marginal roots. -/
theorem mixed_normalized_marginal_sub {R : ℝ → ℝ} {J : ℝ → ℝ → MixedJet ℝ}
    (hR : ContDiff ℝ 2 R) (hpos : ∀ t ≠ 0, 0 < R t)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hj : MixedJet.IsAt J u v) :
    let r := marginalLogSlope R
    let a := reflectedHalfLogSlope R u
    let b := reflectedHalfLogSlope R v
    let d := v-u
    let m := J u v
    Real.sqrt (R (-u) * R (-v)) *
      deriv (fun y ↦ deriv (fun x ↦ ((J x y).value - Real.sqrt (R y * R (y-x))) /
        Real.sqrt (R (-x) * R (-y))) u) v =
      m.duv - b*m.du - a*m.dv + a*b*m.value -
        Real.sqrt (R v * R d) *
          (-deriv r d / 2 - (r d + 2*a)*(r v + r d - 2*b)/4) := by
  dsimp only
  let C (x : ℝ) := Real.sqrt (R x)
  let P (x : ℝ) := (C (-x))⁻¹
  let α := reflectedHalfLogSlope R
  let r := marginalLogSlope R
  have hv := hu.trans huv
  have hf := hR.differentiable (by norm_num)
  let A : ℝ → ℝ → MixedJet ℝ := fun x _ ↦ ⟨P x, -α x * P x, 0, 0⟩
  let B : ℝ → ℝ → MixedJet ℝ := fun _ y ↦ ⟨P y, 0, -α y * P y, 0⟩
  let V : ℝ → ℝ → MixedJet ℝ := fun _ y ↦ ⟨C y, 0, r y / 2 * C y, 0⟩
  have hA : MixedJet.IsAt A u v :=
    ⟨Eventually.of_forall fun _ ↦ inverseRoot_deriv hf (hpos _ (neg_ne_zero.mpr hu.ne')),
      hasDerivAt_const v _, hasDerivAt_const v _⟩
  have hB : MixedJet.IsAt B u v :=
    ⟨Eventually.of_forall fun y ↦ hasDerivAt_const u _, inverseRoot_deriv hf
      (hpos _ (neg_ne_zero.mpr hv.ne')), hasDerivAt_const v _⟩
  have hV : MixedJet.IsAt V u v :=
    ⟨Eventually.of_forall fun y ↦ hasDerivAt_const u _, root_deriv (hf v) (hpos v hv.ne'),
      hasDerivAt_const v _⟩
  let W x y := (MixedJet.mul (A x y) (B x y)).mul
    ((J x y).sub ((V x y).mul (gapRootJet R x y)))
  have hW : MixedJet.IsAt W u v := (hA.mul hB).mul (hj.sub (hV.mul (gapRootJet_isAt hR hpos huv)))
  have hEq : (fun y ↦ deriv (fun x ↦ ((J x y).value - Real.sqrt (R y * R (y-x))) /
      Real.sqrt (R (-x) * R (-y))) u) =ᶠ[𝓝 v] fun y ↦ (W u y).du := by
    filter_upwards [eventually_gt_nhds huv, hW.1] with y hy hd
    have he : (fun x ↦ ((J x y).value - Real.sqrt (R y * R (y-x))) /
        Real.sqrt (R (-x) * R (-y))) =ᶠ[𝓝 u] fun x ↦ (W x y).value := by
      filter_upwards [eventually_gt_nhds hu] with x hx
      rw [Real.sqrt_mul (hpos y (hu.trans hy).ne').le,
        Real.sqrt_mul (hpos (-x) (neg_ne_zero.mpr hx.ne')).le]
      dsimp [W, A, B, V, P, C, MixedJet.mul, MixedJet.sub, gapRootJet]
      rw [div_eq_mul_inv, mul_inv]
      ring
    exact he.deriv_eq.trans hd.deriv
  rw [hEq.deriv_eq, hW.2.2.deriv,
    Real.sqrt_mul (hpos (-u) (neg_ne_zero.mpr hu.ne')).le,
    Real.sqrt_mul (hpos v hv.ne').le]
  have hCu := (Real.sqrt_pos.mpr (hpos (-u) (neg_ne_zero.mpr hu.ne'))).ne'
  have hCv := (Real.sqrt_pos.mpr (hpos (-v) (neg_ne_zero.mpr hv.ne'))).ne'
  dsimp only [W, A, B, V, P, C, α, r, MixedJet.mul, MixedJet.sub, gapRootJet]
  field_simp [hCu, hCv]
  ring

end RefinedBMV.PositiveCenter
