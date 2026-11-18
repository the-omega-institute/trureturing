/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid
   mirror-E: none(waiver:general-integral-estimates)
   anchors: []
   utility: none
   digest: Cost and entropy estimates for right-endpoint logistic grids. -/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real Set MeasureTheory Finset
open scoped BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid

/-- The cost of the two symmetric families of logistic bins. -/
def rightEndpointCost (t : ℕ → ℝ) (m : ℕ) : ℝ :=
  2 * ∑ i ∈ range m, (t (i + 1) - t i) * (t (i + 1) * sigmoid (-t (i + 1)))

/-- The binary entropy of the two symmetric families of logistic bins. -/
def rightEndpointEntropy (t : ℕ → ℝ) (m : ℕ) : ℝ :=
  2 * ∑ i ∈ range m, (t (i + 1) - t i) * binEntropy (sigmoid (-t (i + 1)))

/-- On a grid starting at zero, the right-endpoint cost has a one-sided mesh error,
and the entropy deficit is bounded by the mesh times the total entropy drop. -/
theorem rightEndpoint_bounds {t : ℕ → ℝ} {m : ℕ} {U δ : ℝ} (hm : 0 < m)
    (hzero : t 0 = 0) (hend : t m = U)
    (hstep : ∀ i < m, 0 < t (i + 1) - t i)
    (hwidth : ∀ i < m, t (i + 1) - t i ≤ δ) :
    rightEndpointCost t m ≤
      2 * (∫ u in (0 : ℝ)..U, u * sigmoid (-u)) + 2 * δ * (∫ u in (0 : ℝ)..U, sigmoid (-u)) ∧
    0 ≤ 2 * (∫ u in (0 : ℝ)..U, binEntropy (sigmoid (-u))) - rightEndpointEntropy t m ∧
    2 * (∫ u in (0 : ℝ)..U, binEntropy (sigmoid (-u))) - rightEndpointEntropy t m ≤
      2 * δ * (log 2 - binEntropy (sigmoid (-U))) ∧
    2 * δ * (log 2 - binEntropy (sigmoid (-U))) ≤ 2 * δ * log 2 := by
  let q (u : ℝ) := sigmoid (-u)
  let f (u : ℝ) := binEntropy (q u)
  let width (i : ℕ) := t (i + 1) - t i
  have hq : Continuous q := continuous_sigmoid.comp continuous_neg
  have hf : Continuous f := binEntropy_continuous.comp hq
  have hmoment : Continuous (fun u => u * q u) := continuous_id.mul hq
  have hqanti : Antitone q := fun _ _ hab => sigmoid_monotone (neg_le_neg hab)
  have hqhalf {u : ℝ} (hu : 0 ≤ u) : q u ∈ Icc 0 (2⁻¹ : ℝ) := by
    refine ⟨sigmoid_nonneg _, ?_⟩
    simpa only [q, neg_zero, sigmoid_zero] using hqanti hu
  have hfanti : AntitoneOn f (Ici 0) := fun _ ha _ hb hab =>
    binEntropy_strictMonoOn.monotoneOn (hqhalf hb) (hqhalf ha) (hqanti hab)
  have ht_nonneg : ∀ i ≤ m, 0 ≤ t i := by
    intro i
    induction i with
    | zero => intro _; rw [hzero]
    | succ i ih =>
      intro hi
      exact (ih (Nat.le_of_succ_le hi)).trans (sub_pos.mp (hstep i hi)).le
  have hcost (i : ℕ) (hi : i < m) :
      width i * (t (i + 1) * q (t (i + 1))) ≤
        (∫ u in t i..t (i + 1), u * q u) + δ * (∫ u in t i..t (i + 1), q u) := by
    have hle : t i ≤ t (i + 1) := (sub_pos.mp (hstep i hi)).le
    have hmul : Continuous (fun u => δ * q u) := continuous_const.mul hq
    have hpoint (u : ℝ) (hu : u ∈ Icc (t i) (t (i + 1))) :
        t (i + 1) * q (t (i + 1)) ≤ u * q u + δ * q u := by
      calc
        _ ≤ t (i + 1) * q u :=
          mul_le_mul_of_nonneg_left (hqanti hu.2) (ht_nonneg (i + 1) hi)
        _ ≤ (u + δ) * q u :=
          mul_le_mul_of_nonneg_right (by linarith [hwidth i hi, hu.1]) (sigmoid_nonneg _)
        _ = _ := add_mul _ _ _
    have h := intervalIntegral.integral_mono_on hle intervalIntegrable_const
      ((hmoment.add hmul).intervalIntegrable _ _) hpoint
    rwa [intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_add (hmoment.intervalIntegrable _ _)
        (hmul.intervalIntegrable _ _), intervalIntegral.integral_const_mul] at h
  have hentropy (i : ℕ) (hi : i < m) :
      0 ≤ (∫ u in t i..t (i + 1), f u) - width i * f (t (i + 1)) ∧
      (∫ u in t i..t (i + 1), f u) - width i * f (t (i + 1)) ≤
        δ * (f (t i) - f (t (i + 1))) := by
    have ha := ht_nonneg i hi.le
    have hb := ht_nonneg (i + 1) hi
    have hle := (sub_pos.mp (hstep i hi)).le
    have hl := intervalIntegral.integral_mono_on hle intervalIntegrable_const
      (hf.intervalIntegrable _ _) (fun _ hu => hfanti (ha.trans hu.1) hb hu.2)
    have hh := intervalIntegral.integral_mono_on hle (hf.intervalIntegrable _ _)
      intervalIntegrable_const (fun _ hu => hfanti ha (ha.trans hu.1) hu.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hl hh
    refine ⟨sub_nonneg.mpr hl, ?_⟩
    calc
      _ ≤ width i * f (t i) - width i * f (t (i + 1)) := sub_le_sub_right hh _
      _ = width i * (f (t i) - f (t (i + 1))) := (mul_sub _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hwidth i hi)
        (sub_nonneg.mpr (hfanti ha hb hle))
  have hsum_cost := sum_le_sum fun i hi => hcost i (mem_range.mp hi)
  rw [sum_add_distrib, ← mul_sum,
    intervalIntegral.sum_integral_adjacent_intervals
      (fun _ _ => hmoment.intervalIntegrable _ _),
    intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hq.intervalIntegrable _ _),
    hzero, hend] at hsum_cost
  have hsum_lower := sum_nonneg fun i hi => (hentropy i (mem_range.mp hi)).1
  have hsum_upper := sum_le_sum fun i hi => (hentropy i (mem_range.mp hi)).2
  have hsum_f : (∑ i ∈ range m, ∫ u in t i..t (i + 1), f u) = ∫ u in (0 : ℝ)..U, f u := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => hf.intervalIntegrable _ _),
      hzero, hend]
  rw [sum_sub_distrib, hsum_f] at hsum_lower hsum_upper
  have hdrop : (∑ i ∈ range m, (f (t i) - f (t (i + 1)))) = f 0 - f U := by
    rw [Finset.sum_range_sub' (fun i => f (t i)), hzero, hend]
  rw [← mul_sum, hdrop] at hsum_upper
  have hfzero : f 0 = log 2 := by simp [f, q]
  rw [hfzero] at hsum_upper
  have hδ : 0 ≤ δ := (hstep 0 hm).le.trans (hwidth 0 hm)
  have hfU : 0 ≤ f U := binEntropy_nonneg _
  change 2 * (∑ i ∈ range m, width i * (t (i + 1) * q (t (i + 1)))) ≤ _ ∧
    0 ≤ 2 * (∫ u in (0 : ℝ)..U, f u) - 2 * (∑ i ∈ range m, width i * f (t (i + 1))) ∧
    2 * (∫ u in (0 : ℝ)..U, f u) - 2 * (∑ i ∈ range m, width i * f (t (i + 1))) ≤
      2 * δ * (log 2 - f U) ∧ 2 * δ * (log 2 - f U) ≤ 2 * δ * log 2
  refine ⟨?_, by linarith, ?_, ?_⟩
  · change _ ≤ 2 * (∫ u in (0 : ℝ)..U, u * q u) + 2 * δ * (∫ u in (0 : ℝ)..U, q u)
    linarith
  · linarith
  · exact mul_le_mul_of_nonneg_left (sub_le_self _ hfU) (by positivity)

end D5.S3.Arith.Robin.Analytic.OmegaTail.LogisticGrid
