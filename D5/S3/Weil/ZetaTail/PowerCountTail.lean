/- GID: D5/S3/Weil/ZetaTail/PowerCountTail
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaTail/PowerCountTail
   mirror-E: none(waiver:analytic-inequality)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.ImproperIntegrals]
   utility: none
   digest: Finite weighted power counts imply an inclusive inverse-power tail and summability. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Classical partial summation for arbitrary weighted ordinates. The count hypothesis
is imposed on finite subsets, so neither local finiteness nor a supplied infinite sum
is needed. This general analytic inference supplies no actual zeta-density estimate,
signed spectral comparison, or proof of RH. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace D5.S3.Weil.ZetaTail.PowerCountTail

private theorem finite_inverse_power_tail_le {ι : Type*} (g m : ι → ℝ)
    {Y C p a : ℝ} (hY : 0 < Y) (hC : 0 ≤ C) (hp : 0 < p) (hap : a < p)
    (hcount : ∀ u : ℝ, Y ≤ u → ∀ s : Finset ι,
      (∀ i ∈ s, g i < u) → ∑ i ∈ s, m i ≤ C * u ^ a)
    (s : Finset ι) (hs : ∀ i ∈ s, Y ≤ g i) :
    ∑ i ∈ s, m i * (g i) ^ (-p) ≤ (p * C / (p - a)) * Y ^ (a - p) := by
  classical
  by_cases he : s = ∅
  · subst s
    simp only [Finset.sum_empty]
    exact mul_nonneg (div_nonneg (mul_nonneg hp.le hC) (sub_pos.mpr hap).le)
      (Real.rpow_nonneg hY.le _)
  have hpow : -p - 1 < -1 := by linarith
  have hmajorpow : a - p - 1 < -1 := by linarith
  have hmoment (b w : ℝ) (hb : 0 < b) :
      (∫ u in Ioi b, (p * w) * u ^ (-p - 1)) = w * b ^ (-p) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hpow hb]
    rw [show -p - 1 + 1 = -p by ring]
    rw [show -p = -(p) by rfl, neg_div_neg_eq]
    field_simp
  let kernel := fun (i : ι) (u : ℝ) =>
    if g i < u then (p * m i) * u ^ (-p - 1) else 0
  have hk (i : ι) : IntegrableOn (kernel i) (Ioi Y) := by
    have h := IntegrableOn.indicator (t := Ioi (g i))
      ((integrableOn_Ioi_rpow_of_lt hpow hY).const_mul (p * m i)) measurableSet_Ioi
    convert! h using 1
  have heach (i : ι) (hi : i ∈ s) :
      (∫ u in Ioi Y, kernel i u) = m i * (g i) ^ (-p) := by
    change (∫ u in Ioi Y,
      (Ioi (g i)).indicator (fun u => (p * m i) * u ^ (-p - 1)) u) = _
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (hs i hi))]
    exact hmoment (g i) (m i) (hY.trans_le (hs i hi))
  have hmaj : IntegrableOn (fun u : ℝ => (p * C) * u ^ (a - p - 1)) (Ioi Y) :=
    (integrableOn_Ioi_rpow_of_lt hmajorpow hY).const_mul (p * C)
  have hmajval : (∫ u in Ioi Y, (p * C) * u ^ (a - p - 1)) =
      (p * C / (p - a)) * Y ^ (a - p) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hmajorpow hY]
    rw [show a - p - 1 + 1 = a - p by ring]
    rw [show a - p = -(p - a) by ring, neg_div_neg_eq]
    field_simp
  have hcomp (u : ℝ) (hu : u ∈ Ioi Y) :
      (∑ i ∈ s, kernel i u) ≤ (p * C) * u ^ (a - p - 1) := by
    have hu0 : 0 < u := hY.trans hu
    have hc := hcount u hu.le (s.filter (fun i => g i < u))
      (fun i hi => (Finset.mem_filter.mp hi).2)
    calc
      (∑ i ∈ s, kernel i u) =
          (p * ∑ i ∈ s.filter (fun i => g i < u), m i) * u ^ (-p - 1) := by
        dsimp only [kernel]
        rw [← Finset.sum_filter, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ (p * (C * u ^ a)) * u ^ (-p - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hp.le)
          (Real.rpow_nonneg hu0.le _)
      _ = (p * C) * u ^ (a - p - 1) := by
        rw [show a - p - 1 = a + (-p - 1) by ring, Real.rpow_add hu0]
        ring
  have hineq := setIntegral_mono_on (integrable_finsetSum s (fun i _ => hk i))
    hmaj measurableSet_Ioi hcomp
  rw [integral_finsetSum s (fun i _ => hk i), hmajval] at hineq
  rw [Finset.sum_congr rfl heach] at hineq
  exact hineq

/-- Raw strict weighted counts yield an inclusive inverse-power tail and its convergence.
No countability, local finiteness, positivity of all ordinates, or tail summability
is assumed. In particular, an ordinate equal to `Y` contributes its full mass. -/
theorem inverse_power_tail_of_raw_count {ι : Type*} (g m : ι → ℝ)
    {Y C p a : ℝ} (hY : 0 < Y) (hC : 0 ≤ C) (hp : 0 < p) (hap : a < p)
    (hm : ∀ i, 0 ≤ m i)
    (hcount : ∀ u : ℝ, Y ≤ u → ∀ s : Finset ι,
      (∀ i ∈ s, g i < u) → ∑ i ∈ s, m i ≤ C * u ^ a) :
    Summable (fun i => if Y ≤ g i then m i * (g i) ^ (-p) else 0) ∧
      (∑' i, if Y ≤ g i then m i * (g i) ^ (-p) else 0) ≤
        (p * C / (p - a)) * Y ^ (a - p) := by
  classical
  let f := fun i => if Y ≤ g i then m i * (g i) ^ (-p) else 0
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    dsimp only [f]
    split_ifs with hi
    · exact mul_nonneg (hm i) (Real.rpow_nonneg (hY.trans_le hi).le _)
    · exact le_rfl
  have hfinite (s : Finset ι) :
      ∑ i ∈ s, f i ≤ (p * C / (p - a)) * Y ^ (a - p) := by
    have h := finite_inverse_power_tail_le g m hY hC hp hap hcount
      (s.filter (fun i => Y ≤ g i)) (fun i hi => (Finset.mem_filter.mp hi).2)
    simpa only [Finset.sum_filter, f] using h
  exact ⟨summable_of_sum_le hf hfinite, Real.tsum_le_of_sum_le hf hfinite⟩

end D5.S3.Weil.ZetaTail.PowerCountTail
