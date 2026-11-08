/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentEndpoint
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentEndpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local fourth energy bounds moving endpoint differences with an exact interval-length constant. -/

import D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.MovingEndpointVariance

/-! The local fourth-energy estimate for two moving endpoints. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentEndpoint

open Set MeasureTheory
open VarianceTransferDefs FourthMomentTransferDefs

noncomputable section
set_option autoImplicit false

/-- Local fourth energy controls signed differences between two increasing endpoints. -/
theorem local_fourth_endpoint_bound
    {E p q p' q' : ℝ → ℝ} {α β C X ε l r A B R m : ℝ}
    (hE : LocallyBoundedMeasurable E) (_hC : 0 ≤ C) (_hε : 0 ≤ ε)
    (_hX : 4 ≤ X) (hlr : l ≤ r) (hAB : A ≤ B) (hR : 0 < R) (hm : 0 < m)
    (hA : X / 2 ≤ A) (hB : B ≤ 4 * X)
    (hlo : (4 * X) ^ α ≤ R) (hhi : 4 * R ≤ (X / 2) ^ β)
    (hV : localFourthEnergyWindow E α β C X ε)
    (hp : ContinuousOn p (Icc l r)) (hq : ContinuousOn q (Icc l r))
    (hdp : ∀ x ∈ Icc l r, HasDerivWithinAt p (p' x) (Icc l r) x)
    (hdq : ∀ x ∈ Icc l r, HasDerivWithinAt q (q' x) (Icc l r) x)
    (hlower : ∀ x ∈ Icc l r, m ≤ p' x ∧ m ≤ q' x)
    (himage : ∀ x ∈ Icc l r, p x ∈ Icc A B ∧ q x ∈ Icc A B)
    (hgap : ∀ x ∈ Icc l r, |q x - p x| ≤ R) :
    (∫ x in l..r, |E (q x) - E (p x)| ^ 4) ≤
      (656 / 3 : ℝ) * (C / m) * R ^ 2 * Real.log X ^ 2 * (B - A + ε * X) := by
  let K := C * Real.log X ^ 2 * (B - A + ε * X)
  have hv (v : ℝ) (hv : v ∈ Icc R (4 * R)) :
      (∫ y in A..B, increment E v y ^ 4) ≤ K * v ^ 2 := by
    have hh := hV A B hA hAB hB v (hlo.trans hv.1) (hv.2.trans hhi)
    simpa only [Even.pow_abs (by decide : Even 4)] using hh.trans_eq (by dsimp [K]; ring)
  have hi (a b : ℝ) : IntervalIntegrable (fun v : ℝ => K * v ^ 2) volume a b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have hh := MovingEndpointVariance.two_endpoint_integral_average_pow_le
    (e := 4) (by decide) (by norm_num) hE hlr
    (show 2 * R ≤ 3 * R by linarith) (show R ≤ 4 * R by linarith) hm
    hp hq hdp hdq (fun x hx => (hlower x hx).1) (fun x hx => (hlower x hx).2)
    himage (by
      intro x hx
      have hg := abs_le.1 (hgap x hx)
      constructor <;> linarith)
    (hi (2 * R) (3 * R)) (hi R (4 * R))
    (fun v hv' => hv v ⟨by linarith [hv'.1], by linarith [hv'.2]⟩) hv
  have hab (a b : ℝ) : (∫ v in a..b, K * v ^ 2) = K * ((b ^ 3 - a ^ 3) / 3) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [hab, hab] at hh
  norm_num only [Nat.reduceSub, Nat.reducePow] at hh
  have hh' : R * (∫ x in l..r, |E (q x) - E (p x)| ^ 4) ≤
      R * ((656 / 3 : ℝ) * (C / m) * R ^ 2 * Real.log X ^ 2 * (B - A + ε * X)) := by
    simpa only [Even.pow_abs (by decide : Even 4), show 3 * R - 2 * R = R by ring] using
      hh.trans_eq (by dsimp [K]; ring)
  exact (mul_le_mul_iff_right₀ hR).1 hh'

end
end D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentEndpoint
