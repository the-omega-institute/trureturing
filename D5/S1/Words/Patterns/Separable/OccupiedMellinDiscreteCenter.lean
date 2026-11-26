/- GID: D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteCenter
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedMellinDiscreteCenter
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SumIntegralComparisons]
   utility: none
   digest: A uniform shifted lattice bound around the singular Mellin sample at one. -/

import D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A discrete center window retains the regularized center exactly once. -/

namespace D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteCenter

open OccupiedMellinInterior

private theorem sample_majorant {β a s : ℝ} (hβ : 0 ≤ β) (ha : 0 < a)
    (hs : 1 / 2 ≤ s) :
    |sample β a s| ≤ 12 + 4*(a+|1 - s|)^(-β) := by
  have hsp : 0 < s := by linarith
  have hweight : s^(-(3 / 2 : ℝ)) ≤ 4 := by
    calc
      _ ≤ (1 / 2 : ℝ)^(-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hs (by norm_num)
      _ ≤ (1 / 2 : ℝ)^(-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ = _ := by norm_num [Real.rpow_neg]
  have hp : (a+(1+s))^(-β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr hβ)
  have hr : (a+1)^(-β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr hβ)
  have hp0 : 0 ≤ (a+(1+s))^(-β) := Real.rpow_nonneg (by linarith) _
  have hr0 : 0 ≤ (a+1)^(-β) := Real.rpow_nonneg (by linarith) _
  have hq0 : 0 ≤ (a+|1 - s|)^(-β) := Real.rpow_nonneg (by linarith [abs_nonneg (1 - s)]) _
  have hab : |(a+(1+s))^(-β)+(a+|1 - s|)^(-β)-2*(a+1)^(-β)| ≤ 3+(a+|1 - s|)^(-β) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  unfold sample
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hsp.le _)]
  have hh := mul_le_mul hweight hab (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4)
  linarith only [hh]

private theorem normalized_rpow {n : ℝ} (hn : 0 < n) :
    n^(3 / 4:ℝ) / n = n^(-(1 / 4 : ℝ)) := by
  rw [div_eq_mul_inv]
  have he : n⁻¹ = n^(-(1:ℝ)) := (Real.rpow_neg_one n).symm
  rw [he, ← Real.rpow_add hn]
  congr 1
  norm_num

/-- The exactly regularized center m=n contributes O(n^(-1 / 4)); a=2 / n
    is retained.  No value is assigned to the unregularized singularity. -/
private theorem exact_center_bound {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (n : ℕ) (hn : 0 < n) :
    |sample β (2/(n:ℝ)) 1| / n ≤ 16 * (n:ℝ)^(-(1 / 4:ℝ)) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have h := sample_majorant hβ (a := 2/(n:ℝ)) (s := 1) (by positivity) (by norm_num)
  simp only [sub_self, abs_zero, add_zero] at h
  have hh : (2/(n:ℝ))^(-β) ≤ (n:ℝ)^(3 / 4:ℝ) := by
    calc
      _ ≤ (1/(n:ℝ))^(-β) :=
        Real.rpow_le_rpow_of_nonpos (by positivity)
          (div_le_div_of_nonneg_right (by norm_num) hn0.le) (neg_nonpos.mpr hβ)
      _ = (n:ℝ)^β := by rw [one_div, Real.inv_rpow hn0.le, ← Real.rpow_neg hn0.le, neg_neg]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hβ'
  have hbase : 1 ≤ (n:ℝ)^(3 / 4:ℝ) :=
    Real.one_le_rpow hn1 (by norm_num)
  have hb : |sample β (2/(n:ℝ)) 1| ≤ 16 * (n:ℝ)^(3 / 4:ℝ) := by linarith
  exact (div_le_div_of_nonneg_right hb hn0.le).trans_eq (by rw [mul_div_assoc, normalized_rpow hn0])

/-- The same majorant for both distances r / n from the center. -/
private theorem side_sample_bound {β n r s : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (hn : 0 < n) (hr : 0 < r) (hrn : r / n ≤ 1 / 2)
    (hs : 1 / 2 ≤ s) (hsdist : |1 - s| = r / n) :
    |sample β (2 / n) s| ≤ 12 + 4*(n^(3 / 4:ℝ)*r^(-(3 / 4:ℝ))) := by
  have hx : 0 < r / n := div_pos hr hn
  have hp : (2 / n+|1 - s|)^(-β) ≤ n^(3 / 4:ℝ)*r^(-(3 / 4:ℝ)) := by
    rw [hsdist]
    calc
      _ ≤ (r / n)^(-β) :=
        Real.rpow_le_rpow_of_nonpos hx (by linarith [show 0 ≤ (2:ℝ)/n by positivity])
          (neg_nonpos.mpr hβ)
      _ ≤ (r / n)^(-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hx (hrn.trans (by norm_num)) (by linarith)
      _ = _ := by
        rw [Real.div_rpow hr.le hn.le, div_eq_mul_inv, ← Real.rpow_neg hn.le, neg_neg, mul_comm]
  exact (sample_majorant hβ (by positivity) hs).trans (by linarith)

open MeasureTheory

private theorem quarter_power_sum (K : ℕ) :
    (∑ i ∈ Finset.range K, (((i+1 : ℕ) : ℝ))^(-(3 / 4:ℝ))) ≤
      4 * (K:ℝ)^(1 / 4:ℝ) := by
  let f (x : ℝ) := x^(-(3 / 4:ℝ))
  have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hanti : AntitoneOn f (Set.Ioc (0 : ℝ) (0 + K)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos hx.1 hxy (by norm_num)
  have hint : IntegrableOn f (Set.Icc (0 : ℝ) (0 + K)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by simp)).1
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))
  have h : (∑ i ∈ Finset.range K, f ((i+1 : ℕ) : ℝ)) ≤ ∫ x in (0 : ℝ)..(K : ℝ), f x := by
    simpa only [zero_add] using hanti.sum_le_integral_of_integrableOn hint
  dsimp only [f] at h
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(3 / 4:ℝ))),
    show (-(3 / 4:ℝ))+1 = 1 / 4 by norm_num, Real.zero_rpow (by norm_num), sub_zero] at h
  convert h using 1
  ring

private theorem rescale_side_bound {n K : ℝ} (hn : 0 < n) (hK : 0 ≤ K) :
    (n ^ (3 / 4 : ℝ) * K ^ (1 / 4 : ℝ)) / n = (K/n) ^ (1 / 4 : ℝ) := by
  rw [mul_comm, mul_div_assoc, normalized_rpow hn, Real.div_rpow hK hn.le,
    Real.rpow_neg hn.le]
  exact (div_eq_mul_inv _ _).symm

/-- Integrated sample bound for one half of the center window; the sample radius
    is the positive natural index i+1, so neither side double counts m=n. -/
private theorem near_center_one_side {β δ σ : ℝ}
    (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2)
    (hσ : σ = 1 ∨ σ = -1) (n K : ℕ) (hn : 0 < n) (hKn : (K : ℝ) / n ≤ δ) :
    (∑ i ∈ Finset.range K, |sample β (2/(n:ℝ))
      (1+σ*(((i+1:ℕ):ℝ)/n))|) / n ≤ 28 * δ^(1 / 4:ℝ) := by
  have hNp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hK : 0 ≤ (K:ℝ) := by positivity
  let w (i : ℕ) := (((i+1:ℕ):ℝ))^(-(3 / 4:ℝ))
  have hterm (i : ℕ) (hi : i ∈ Finset.range K) :
      |sample β (2/(n:ℝ)) (1+σ*(((i+1:ℕ):ℝ)/n))| ≤ 12+4*((n:ℝ)^(3 / 4:ℝ)*w i) := by
    have hr : 0 < ((i+1:ℕ):ℝ) := by positivity
    have hcut : ((i+1:ℕ):ℝ)/n ≤ 1 / 2 :=
      ((div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi))
        hNp.le).trans hKn).trans hδ'
    have hnz : 0 ≤ ((i+1:ℕ):ℝ)/n := (div_pos hr hNp).le
    apply side_sample_bound hβ hβ' hNp hr hcut
    · rcases hσ with rfl | rfl <;> linarith
    · rcases hσ with rfl | rfl
      · rw [one_mul, show 1-(1+((i+1:ℕ):ℝ)/n) = -(((i+1:ℕ):ℝ)/n) by ring,
          abs_neg, abs_of_nonneg hnz]
      · rw [neg_one_mul, ← sub_eq_add_neg, show 1-(1-((i+1:ℕ):ℝ)/n) = ((i+1:ℕ):ℝ)/n by ring,
          abs_of_nonneg hnz]
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  have hP := quarter_power_sum K
  change ∑ i ∈ Finset.range K, w i ≤ _ at hP
  have hR : 0 ≤ (n:ℝ)^(3 / 4:ℝ) := Real.rpow_nonneg hNp.le _
  have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hR) (by norm_num : (0:ℝ) ≤ 4)
  have hdivide := div_le_div_of_nonneg_right (hsum.trans (add_le_add_right hmul _)) hNp.le
  have hfactor : ((K:ℝ)*12+4*((n:ℝ)^(3 / 4:ℝ)*(4*(K:ℝ)^(1 / 4:ℝ))))/n =
      12*((K : ℝ) / n) + 16*((K : ℝ) / n)^(1 / 4:ℝ) := by
    have h := rescale_side_bound hNp hK
    linear_combination 16 * h
  rw [hfactor] at hdivide
  have hδpow : δ ≤ δ^(1 / 4:ℝ) := by
    by_cases hz : δ = 0
    · simp [hz, Real.zero_rpow]
    · have hp : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hz)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hp
        (hδ'.trans (by norm_num : (1 / 2:ℝ) ≤ 1)) (show (1 / 4:ℝ) ≤ 1 by norm_num)
  have hQ := Real.rpow_le_rpow (div_nonneg hK hNp.le) hKn (by norm_num : (0:ℝ) ≤ 1 / 4)
  linarith only [hdivide, hKn, hδpow, hQ]

/-- Full symmetric finite window, expressed as separately indexed left and right
    samples and the single regularized center. -/
theorem near_center_cutoff {β δ : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 2) (n K : ℕ) (hn : 0 < n) (hKn : (K : ℝ) / n ≤ δ) :
    ((∑ i ∈ Finset.range K, |sample β (2/(n:ℝ)) (1-(((i+1:ℕ):ℝ)/n))|) +
      |sample β (2/(n:ℝ)) 1| +
      (∑ i ∈ Finset.range K, |sample β (2/(n:ℝ)) (1+(((i+1:ℕ):ℝ)/n))|)) / n ≤
      56*δ^(1 / 4:ℝ) + 16*(n:ℝ)^(-(1 / 4:ℝ)) := by
  have hl := near_center_one_side hβ hβ' hδ hδ' (σ := -1) (Or.inr rfl) n K hn hKn
  simp only [neg_one_mul, ← sub_eq_add_neg] at hl
  have hr := near_center_one_side hβ hβ' hδ hδ' (σ := 1) (Or.inl rfl) n K hn hKn
  simp only [one_mul] at hr
  rw [add_div, add_div]
  linarith only [hl, hr, exact_center_bound hβ hβ' n hn]

#print axioms near_center_cutoff

end D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteCenter
