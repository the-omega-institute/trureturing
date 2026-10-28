/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrialEnergy
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrialEnergy
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual stopping-cylinder trial extensions and strict original free-root energy bounds. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm

/-! Single-edge trial extensions for the actual biased stopping partitions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrialEnergy

open FiniteSourceHardy (H Edge)
open BiasedBoundaryTrace (G M J cylinder indicator b J_single)
open BiasedBoundaryPathSplit (constG)
open BiasedBoundaryCylinderProjection (Q atomMean)
open BiasedBoundaryStopping (Threshold A Qt Vt actual_stopping_partition actual_stopping_residual)
open BiasedBoundaryFreeRootForm (D energy free_root_least_energy)
open MeasureTheory
open scoped BigOperators ENNReal

/-- Every actual stopping-cylinder function has a finite original-edge extension.
Its edge energy bounds the original free-root minimum from above, strictly below
the stopping Rayleigh threshold for every nonzero function. -/
theorem actual_stopping_trial_energy :
    ∀ (t : Threshold) (F : Vt t), ∃ z : H,
      z = ∑ p ∈ A t, lp.single 2 p (atomMean p F.val) ∧
      J z = F.val ∧
      ‖z‖ ^ 2 = ∑ p ∈ A t, (atomMean p F.val) ^ 2 ∧
      F.val ∈ D ∧
      ‖F.val‖ ^ 2 = ∑ p ∈ A t,
        M.real (cylinder p.val) * (atomMean p F.val) ^ 2 ∧
      energy F.val ≤ ‖z‖ ^ 2 ∧
      (F.val ≠ 0 →
        b * t.val * ‖z‖ ^ 2 < ‖F.val‖ ^ 2 ∧
        ‖z‖ ^ 2 < (b * t.val)⁻¹ * ‖F.val‖ ^ 2 ∧
        energy F.val < (b * t.val)⁻¹ * ‖F.val‖ ^ 2) := by
  classical
  intro t F
  let x : Edge → ℝ := fun p => atomMean p F.val
  let z : H := ∑ p ∈ A t, lp.single 2 p (x p)
  have hfix : Qt t F.val = F.val := by
    rw [(actual_stopping_residual t).2.1]
    exact (Vt t).starProjection_eq_self_iff.mpr F.property
  have hsum : (∑ p ∈ A t, x p • indicator p) = F.val := by
    simpa only [Qt, Q, sum_apply,
      ContinuousLinearMap.smulRight_apply] using hfix
  have htrace : J z = F.val := by
    dsimp only [z]
    simp only [map_sum, J_single]
    exact hsum
  have hnormz : ‖z‖ ^ 2 = ∑ p ∈ A t, (x p)^2 := by
    simpa [z] using lp.norm_sum_single (p := (2 : ℝ≥0∞))
      (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x (A t)
  have hdomain : F.val ∈ D := ⟨0,z,by simp [htrace]⟩
  have hnorm : ‖F.val‖ ^ 2 =
      ∑ p ∈ A t, M.real (cylinder p.val) * (x p)^2 := by
    rw [(actual_stopping_residual t).2.2.2.2.1 F.val]
    apply Finset.sum_congr rfl
    intro p hp
    have hpull := (actual_stopping_residual t).2.2.1 p hp F.val
    rw [hfix] at hpull
    rw [hpull]
    congr 1
    change ‖x p • Lp.const 2 M (1 : ℝ)‖ ^ 2 = (x p)^2
    rw [norm_smul, Lp.norm_const (μ := M) (p := 2) (c := (1 : ℝ)) (by norm_num)]
    simp
  have henergy : energy F.val ≤ ‖z‖ ^ 2 := by
    let f : D := ⟨F.val,hdomain⟩
    have h := (free_root_least_energy f).2.2.2
    rw [h.1]
    exact (h.2.1 0 z (by change F.val = constG 0 + J z; simp [htrace])).2
  refine ⟨z,rfl,htrace,hnormz,hdomain,hnorm,henergy,?_⟩
  intro hF
  have hnonzero : ∃ p ∈ A t, x p ≠ 0 := by
    by_contra h
    push Not at h
    apply hF
    rw [← hsum]
    exact Finset.sum_eq_zero (fun p hp => by rw [h p hp,zero_smul])
  obtain ⟨p,hp,hxp⟩ := hnonzero
  have hmass := (actual_stopping_partition t).2.2.2.2.2.2.1
  have hstrict : b * t.val * ‖z‖ ^ 2 < ‖F.val‖ ^ 2 := by
    rw [hnormz,hnorm,Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro q hq
      exact mul_le_mul_of_nonneg_right (hmass q hq).1.le (sq_nonneg _)
    · exact ⟨p,hp,mul_lt_mul_of_pos_right (hmass p hp).1 (sq_pos_of_ne_zero hxp)⟩
  have hbt : 0 < b * t.val := mul_pos
    (sq_pos_of_pos BiasedBoundaryTrace.a_pos) t.property.1
  have hupper : ‖z‖ ^ 2 < (b * t.val)⁻¹ * ‖F.val‖ ^ 2 := by
    exact (lt_inv_mul_iff₀ hbt).mpr hstrict
  exact ⟨hstrict,hupper,henergy.trans_lt hupper⟩

#print axioms actual_stopping_trial_energy

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrialEnergy
