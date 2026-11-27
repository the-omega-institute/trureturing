/- GID: D5/S3/Quantum/Recovery/BKM/PowerPullback
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKM/PowerPullback
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic pullback of the actual BKM integral. -/

import D5.S3.Quantum.Recovery.BKMObservableRigidity
import D5.S3.Quantum.Recovery.BKMSpectralVariance

/-! # Cubic pullback of the actual BKM integral -/

noncomputable section

open MeasureTheory
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Matrix.SpectralPower (mpow mpow_one mpow_two)
open D5.S3.Quantum.Recovery.BKMRelativeDensity (omega continuous_mpow)
open D5.S3.Quantum.Recovery.BKMObservableRigidity (mpow_add mpow_zero)

namespace D5.S3.Quantum.Recovery.BKM.PowerPullback

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "M" => Matrix ι ι ℂ

private theorem cube_posDef {B : M} (hB : B.PosDef) : (B ^ (3 : ℕ)).PosDef := by
  rw [← CFC.rpow_natCast _ 3 hB.posSemidef.nonneg]
  exact Matrix.IsStrictlyPositive.posDef
    (IsStrictlyPositive.rpow B (3 : ℝ) hB.isStrictlyPositive)

private theorem mpow_cube {B : M} (hB : B.PosDef) (s : ℝ) :
    mpow (B ^ (3 : ℕ)) s = mpow B (3 * s) := by
  unfold mpow
  rw [← CFC.rpow_eq_cfc_real (cube_posDef hB).posSemidef.nonneg,
    ← CFC.rpow_eq_cfc_real hB.posSemidef.nonneg,
    ← CFC.rpow_natCast _ 3 hB.posSemidef.nonneg]
  exact CFC.rpow_rpow B 3 s (by norm_num) hB.isStrictlyPositive

private theorem continuous_power_integrand {B : M} (hB : B.PosDef) (X : M) (m : ℝ) :
    Continuous (fun t : ℝ => mpow B t * X * mpow B (m - t)) :=
  let hc := continuous_mpow B hB
  (hc.mul continuous_const).mul (hc.comp (continuous_const.sub continuous_id))

private theorem integral_power_segment {B : M} (hB : B.PosDef) (X : M)
    (m k l : ℝ) (hm : m = k + 1 + l) :
    (∫ t in k..k + 1, mpow B t * X * mpow B (m - t)) =
      mpow B k * omega B X * mpow B l := by
  let f (t : ℝ) := mpow B t * X * mpow B (m - t)
  let g (s : ℝ) := mpow B s * X * mpow B (1 - s)
  let L := ContinuousLinearMap.mulLeftRight ℂ M (mpow B k) (mpow B l)
  have hshift (s : ℝ) : f (s + k) = L (g s) := by
    change mpow B (s + k) * X * mpow B (m - (s + k)) =
      mpow B k * (mpow B s * X * mpow B (1 - s)) * mpow B l
    rw [show m - (s + k) = (1 - s) + l by rw [hm]; ring,
      add_comm s k, ← mpow_add hB k s, ← mpow_add hB (1 - s) l]
    simp only [mul_assoc]
  calc
    _ = ∫ s in (0 : ℝ)..1, f (s + k) := by
      rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (1 : ℝ) k]
    _ = ∫ s in (0 : ℝ)..1, L (g s) := by simp only [hshift]
    _ = L (∫ s in (0 : ℝ)..1, g s) :=
      L.intervalIntegral_comp_comm ((continuous_power_integrand hB X 1).intervalIntegrable 0 1)
    _ = _ := rfl

/-- The actual BKM integral at a positive definite cube is the average of the
three ordered products obtained from the BKM integral at its base. -/
theorem omega_cube {B : M} (hB : B.PosDef) (X : M) :
    omega (B ^ (3 : ℕ)) X =
      (1 / 3 : ℝ) •
        (B ^ (2 : ℕ) * omega B X + B * omega B X * B + omega B X * B ^ (2 : ℕ)) := by
  let f (t : ℝ) := mpow B t * X * mpow B (3 - t)
  have hf := continuous_power_integrand hB X 3
  have h01 : (∫ t in (0 : ℝ)..1, f t) = omega B X * B ^ (2 : ℕ) := by
    simpa only [zero_add, mpow_zero hB, one_mul, mpow_two hB.isHermitian, pow_two] using
      integral_power_segment hB X 3 0 2 (by norm_num)
  have h12 : (∫ t in (1 : ℝ)..2, f t) = B * omega B X * B := by
    simpa only [one_add_one_eq_two, mpow_one hB.isHermitian] using
      integral_power_segment hB X 3 1 1 (by norm_num)
  have h23 : (∫ t in (2 : ℝ)..3, f t) = B ^ (2 : ℕ) * omega B X := by
    simpa only [show (2 : ℝ) + 1 = 3 by norm_num, mpow_zero hB, mul_one,
      mpow_two hB.isHermitian, pow_two] using integral_power_segment hB X 3 2 0 (by norm_num)
  calc
    omega (B ^ (3 : ℕ)) X = ∫ s in (0 : ℝ)..1, f (3 * s) := by
      simp only [omega, mpow_cube hB, f, show ∀ s : ℝ, 3 * (1 - s) = 3 - 3 * s by
        intro s
        ring]
    _ = (1 / 3 : ℝ) • ∫ t in (0 : ℝ)..3, f t := by
      simpa only [one_div, mul_zero, mul_one] using
        intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) f
          (show (3 : ℝ) ≠ 0 by norm_num)
    _ = _ := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 2) (hf.intervalIntegrable 2 3),
        ← intervalIntegral.integral_add_adjacent_intervals
          (hf.intervalIntegrable 0 1) (hf.intervalIntegrable 1 2), h01, h12, h23]
      ac_rfl

end D5.S3.Quantum.Recovery.BKM.PowerPullback
