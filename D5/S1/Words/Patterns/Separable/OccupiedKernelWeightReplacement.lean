/- GID: D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SumIntegralComparisons]
   utility: none
   digest: Absolute lattice replacement of actual Schröder weights by their leading power. -/

import D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient
import D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteCenter
import D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteTails
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.LinearCombination

/-! Actual positive jump weights, with the exceptional singleton included,
can be replaced by their leading power with summably small absolute error. -/

open MeasureTheory
open scoped BigOperators

namespace D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement

open OccupiedComparison OccupiedKernelCoefficient OccupiedMellinInterior
open OccupiedMellinCutoffs OccupiedMellinDiscreteCenter OccupiedMellinDiscreteTails

/-- Symmetric second difference of the shifted power lattice profile. -/
noncomputable def secondDiff (β n m : ℝ) : ℝ :=
  (2 + |n + m|) ^ (-β) + (2 + |n - m|) ^ (-β) - 2 * (2 + |n|) ^ (-β)

theorem sample_eq_lattice {β n m : ℝ} (hn : 0 < n) (hm : 0 < m) :
    sample β (2 / n) (m / n) = n ^ (β+(3 / 2:ℝ)) * (m^(-(3 / 2:ℝ)) *
      secondDiff β n m) := by
  have scale {u : ℝ} (hu : 0 ≤ u) : ((2+u)/n)^(-β) = n^β * (2+u)^(-β) := by
    rw [Real.div_rpow (by linarith) hn.le, div_eq_mul_inv,
      ← Real.rpow_neg hn.le, neg_neg, mul_comm]
  have ha : 2 / n+(1+m / n) = (2+|n+m|)/n := by
    rw [abs_of_pos (add_pos hn hm)]
    field_simp
  have hb : 2 / n+|1-m / n| = (2+|n-m|)/n := by
    have h : 1-m / n = (n-m)/n := by field_simp
    rw [h, abs_div, abs_of_pos hn, ← add_div]
  have hc : 2 / n+1 = (2+|n|)/n := by
    rw [abs_of_pos hn]
    field_simp
  unfold sample secondDiff
  rw [ha, hb, hc, scale (abs_nonneg _), scale (abs_nonneg _), scale (abs_nonneg _),
    Real.div_rpow hm.le hn.le, div_eq_mul_inv (m^(-(3 / 2:ℝ))),
    ← Real.rpow_neg hn.le, neg_neg, Real.rpow_add hn]
  ring

private theorem profile_second_difference {β n m : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 3 / 4)
    (hn : 0 < n) (hm : 0 < m) (hmcut : m ≤ n / 2) :
    |secondDiff β n m| ≤ 32 * m ^ 2 * n ^ (-β - 2) := by
  have hs := mellin_cutoff_bounds.2.2.2.1 β (2 / n) (m / n) (by linarith)
    hβ' (by positivity) (div_pos hm hn) (by apply (div_le_iff₀ hn).2; linarith)
  rw [sample_eq_lattice hn hm, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hn.le _), abs_of_nonneg (Real.rpow_nonneg hm.le _)] at hs
  have hnp : 0 < n ^ (β + (3 / 2 : ℝ)) := Real.rpow_pos_of_pos hn _
  have hmp : 0 < m ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hm _
  rw [← mul_assoc] at hs
  apply (le_of_mul_le_mul_left ?_ (mul_pos hnp hmp))
  apply hs.trans_eq
  have hn' : n ^ (β + (3 / 2 : ℝ)) * n ^ (-β - 2) = n ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hm' : m ^ (-(3 / 2 : ℝ)) * m ^ (2 : ℕ) = m ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hm]
    congr 1
    norm_num
  rw [Real.div_rpow hm.le hn.le, div_eq_mul_inv, ← Real.rpow_neg hn.le]
  linear_combination -32 * (m ^ (1 / 2 : ℝ)) * hn' - 32 *
    (n ^ (β + (3 / 2 : ℝ)) * n ^ (-β - 2)) * hm'

private theorem inverse_sqrt_sum (K : ℕ) :
    (∑ i ∈ Finset.range K, (((i+1 : ℕ) : ℝ))^(-(1 / 2:ℝ))) ≤
      2 * (K : ℝ)^(1 / 2:ℝ) := by
  let f (x : ℝ) := x^(-(1 / 2:ℝ))
  have hanti : AntitoneOn f (Set.Ioc (0 : ℝ) (0 + K)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos hx.1 hxy (by norm_num)
  have hint : IntegrableOn f (Set.Icc (0 : ℝ) (0 + K)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by simp)).1
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))
  have h : (∑ i ∈ Finset.range K, f ((i + 1 : ℕ) : ℝ)) ≤ ∫ x in (0 : ℝ)..(K : ℝ), f x := by
    simpa only [zero_add] using hanti.sum_le_integral_of_integrableOn hint
  dsimp only [f] at h
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1 / 2:ℝ))),
    show (-(1 / 2:ℝ))+1 = 1 / 2 by norm_num, Real.zero_rpow (by norm_num), sub_zero] at h
  convert h using 1
  ring

/-- Local coefficient-replacement error from an explicit coefficient remainder.
The summands are indexed by m=i+1, so zero never enters a negative power. -/
private theorem local_weight_replacement {β C : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 3 / 4)
    (hC : 0 ≤ C) (n K : ℕ) (hn : 0 < n) (hK : (K : ℝ) ≤ (n : ℝ) / 2)
    (err : ℕ → ℝ)
    (herr : ∀ m : ℕ, 0 < m → |err m| ≤ C * (m : ℝ)^(-(5 / 2:ℝ))) :
    (∑ i ∈ Finset.range K, |err (i+1) * secondDiff β (n : ℝ) ((i+1:ℕ):ℝ)|) ≤
      64 * C * (n : ℝ)^(-β-3 / 2) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hK0 : 0 ≤ (K : ℝ) := by positivity
  let w (i : ℕ) := (((i+1:ℕ):ℝ))^(-(1 / 2:ℝ))
  let D := 32*C*(n : ℝ)^(-β-2)
  have hD : 0 ≤ D := mul_nonneg (by positivity) (Real.rpow_nonneg hn0.le _)
  have hterm : ∀ i ∈ Finset.range K,
      |err (i+1) * secondDiff β (n : ℝ) ((i+1:ℕ):ℝ)| ≤ D * w i := by
    intro i hi
    have hiK : (i+1 : ℕ) ≤ K := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hmcut : ((i+1:ℕ):ℝ) ≤ (n : ℝ) / 2 := (by exact_mod_cast hiK : ((i+1:ℕ):ℝ) ≤ K).trans hK
    have hm : 0 < ((i+1:ℕ):ℝ) := by positivity
    have hd := profile_second_difference hβ hβ' hn0 hm hmcut
    rw [abs_mul]
    calc
      _ ≤ (C * ((i+1:ℕ):ℝ)^(-(5 / 2:ℝ))) *
          (32 * ((i+1:ℕ):ℝ)^2 * (n : ℝ)^(-β-2)) :=
        mul_le_mul (herr _ (by omega)) hd (abs_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hm.le _))
      _ = D * w i := by
        have hp : ((i+1:ℕ):ℝ)^(-(5 / 2:ℝ)) * ((i+1:ℕ):ℝ)^2 = w i := by
          dsimp [w]
          rw [← Real.rpow_natCast, ← Real.rpow_add hm]
          congr 1
          norm_num
        dsimp [D]
        linear_combination (32*C*(n : ℝ)^(-β-2)) * hp
  have hs := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hs
  have hs' : ∑ i ∈ Finset.range K, w i ≤ 2 * (n : ℝ)^(1 / 2:ℝ) := by
    apply (inverse_sqrt_sum K).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.rpow_le_rpow hK0 (by linarith) (by norm_num)
  apply hs.trans ((mul_le_mul_of_nonneg_left hs' hD).trans_eq ?_)
  have hp : (n : ℝ)^(-β-2) * (n : ℝ)^(1 / 2:ℝ) = (n : ℝ)^(-β-3 / 2) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  dsimp [D]
  linear_combination (64*C) * hp

private theorem denominator_identity (x : ℝ) (hx : 0 < x) :
    (21 / 16:ℝ) / (x^2 * Real.sqrt x) = (21 / 16:ℝ)*x^(-(5 / 2:ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hx, div_eq_mul_inv,
    ← Real.rpow_neg hx.le]
  congr 1
  norm_num

/-- Difference from the leading coefficient at positive jump size m. -/
noncomputable def actualWeightError (A : ℝ) (m : ℕ) : ℝ :=
  kernelWeight (m-1) - A / ((m : ℝ) * Real.sqrt m)

/-- The merged law supplies one kernel coefficient A, and the exceptional
singleton is absorbed into one explicit finite error constant E. -/
private theorem actual_uniform_weight_error :
    ∃ A > (0:ℝ), ∃ E : ℝ, 0 ≤ E ∧
      ∀ m : ℕ, 0 < m → |actualWeightError A m| ≤ E * (m : ℝ)^(-(5 / 2:ℝ)) := by
  obtain ⟨A, hA, hrem⟩ := actual_kernel_weight_strict_remainder
  let E : ℝ := max (21 / 16) |actualWeightError A 1|
  refine ⟨A, hA, E, (show (0:ℝ) ≤ 21 / 16 by norm_num).trans (le_max_left _ _), ?_⟩
  intro m hm
  by_cases he : m = 1
  · subst m
    simpa only [Nat.cast_one, Real.one_rpow, mul_one] using
      (le_max_right (21 / 16 : ℝ) |actualWeightError A 1|)
  · have hm2 : 2 ≤ m := by omega
    have hp : 0 < (m : ℝ) := by exact_mod_cast hm
    have hr := hrem m hm2
    rw [denominator_identity _ hp] at hr
    exact hr.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hp.le _))

private theorem transition_sample_bound {β a s : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (ha : 0 ≤ a) (hs : 3 / 2 ≤ s) :
    |sample β a s| ≤ 5 := by
  have h₁ : 1 ≤ a+(1+s) := by linarith
  have h₂ : 1 / 2 ≤ a+|1-s| := by rw [abs_of_neg (by linarith : 1-s < 0)]; linarith
  have h₃ : 1 ≤ a+1 := by linarith
  have hP := Real.rpow_le_one_of_one_le_of_nonpos h₁ (neg_nonpos.mpr hβ)
  have hR := Real.rpow_le_one_of_one_le_of_nonpos h₃ (neg_nonpos.mpr hβ)
  have hQ : (a+|1-s|)^(-β) ≤ 2 := by
    calc
      _ ≤ (1 / 2:ℝ)^(-β) := Real.rpow_le_rpow_of_nonpos (by norm_num) h₂ (neg_nonpos.mpr hβ)
      _ ≤ (1 / 2:ℝ)^(-(1:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = _ := by norm_num [Real.rpow_neg_one]
  have hP0 : 0 ≤ (a+(1+s))^(-β) := Real.rpow_nonneg (by linarith) _
  have hQ0 : 0 ≤ (a+|1-s|)^(-β) := Real.rpow_nonneg (by linarith) _
  have hR0 : 0 ≤ (a+1)^(-β) := Real.rpow_nonneg (by linarith) _
  have hab : |(a+(1+s))^(-β)+(a+|1-s|)^(-β)-2*(a+1)^(-β)| ≤ 5 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  unfold sample
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ s) _)]
  exact (mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num))
    hab (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)

private theorem floor_half_bounds (n : ℕ) (hn : 0 < n) :
    (n / 2 : ℕ) < n ∧ ((n/2:ℕ):ℝ) ≤ (n : ℝ) / 2 ∧
      (n : ℝ) / 2 ≤ ((n/2+1:ℕ):ℝ) := by
  have h₁ : n / 2 < n := by omega
  have h₂ : 2 * (n/2) ≤ n := by omega
  have h₃ : n ≤ 2*(n/2+1) := by omega
  refine ⟨h₁, ?_, ?_⟩
  · have h : (2:ℝ)*((n/2:ℕ):ℝ) ≤ (n : ℝ) := by exact_mod_cast h₂
    linarith
  · have h : (n : ℝ) ≤ 2*((n/2+1:ℕ):ℝ) := by exact_mod_cast h₃
    linarith

/-- Uniform absolute mass of the entire shifted mesh, obtained from the
small, symmetric center, bounded transition and integrable far bands.
The constant is intentionally loose. -/
private theorem absolute_shifted_mesh_bound {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (n : ℕ) (hn : 0 < n) :
    let F (i : ℕ) := |sample β (2/(n : ℝ)) (((i+1:ℕ):ℝ)/(n : ℝ))|
    Summable F ∧ (∑' i, F i)/(n : ℝ) ≤ 117 := by
  let F (i : ℕ) := |sample β (2/(n : ℝ)) (((i+1:ℕ):ℝ)/(n : ℝ))|
  let K := n/2
  let L := n-K-1
  let M := n+K
  let Q := 2*n-M
  obtain ⟨hKlt, hKhalf, hKplus⟩ := floor_half_bounds n hn
  change K < n at hKlt
  change (K : ℝ) ≤ (n : ℝ) / 2 at hKhalf
  change (n : ℝ) / 2 ≤ ((K+1:ℕ):ℝ) at hKplus
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : L + K + 1 = n := by dsimp [L]; omega
  have hM : L + (K + 1 + K) = M := by dsimp [M]; omega
  have hQ : M + Q = 2*n := by dsimp [Q, M]; omega
  have hKdiv : (K : ℝ)/(n : ℝ) ≤ 1 / 2 := by apply (div_le_iff₀ hn0).2; linarith
  have hLle : L ≤ K := by dsimp [L, K]; omega
  have hLdiv : (L:ℝ)/(n : ℝ) ≤ 1 / 2 :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hLle) hn0.le).trans hKdiv
  have ha : 0 ≤ (2:ℝ)/n := by positivity
  have hδ : (1 / 2:ℝ) ^ (1 / 4:ℝ) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
  have hδ' : (1 / 2:ℝ) ^ (3 / 2:ℝ) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
  have hnδ : (n : ℝ)^(-(1 / 4:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hsm := discrete_mellin_tail_bounds.1 β (2 / (n : ℝ)) n L hβ hβ' ha hn hLdiv
  have hsmall : (∑ i ∈ Finset.range L, F i) / (n : ℝ) ≤ 32 := by
    change (∑ i ∈ Finset.range L, F i) / (n : ℝ) ≤ _ at hsm
    have hpow := Real.rpow_le_rpow (show 0 ≤ (L : ℝ) / n by positivity) hLdiv
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith only [hsm, hpow, hδ']
  have hcl := near_center_cutoff (β := β) hβ hβ' (δ := 1 / 2)
    (by norm_num) le_rfl n K hn hKdiv
  have hcenter : ((∑ i ∈ Finset.range K, F (i+L)) + F (K+L) +
      (∑ i ∈ Finset.range K, F (i+(K+1+L))))/(n : ℝ) ≤ 72 := by
    have hleft : (∑ i ∈ Finset.range K, F (i+L)) =
        ∑ i ∈ Finset.range K, |sample β (2/(n : ℝ)) (1-(((i+1:ℕ):ℝ)/n))| := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < K := Finset.mem_range.mp hi
      dsimp [F]
      congr 2
      have hnat : K-1-i+L+1+(i+1)=n := by omega
      have hcast : ((K-1-i+L+1:ℕ):ℝ) + ((i+1:ℕ):ℝ) = n := by exact_mod_cast hnat
      apply (div_eq_iff hn0.ne').2
      field_simp
      linarith
    have hcenter' : F (K+L) = |sample β (2/(n : ℝ)) 1| := by
      have ht : K+L+1=n := by omega
      change |sample β (2/(n : ℝ)) (((K+L+1:ℕ):ℝ)/n)| = _
      rw [ht, div_self hn0.ne']
    have hright : (∑ i ∈ Finset.range K, F (i+(K+1+L))) =
        ∑ i ∈ Finset.range K, |sample β (2/(n : ℝ)) (1+(((i+1:ℕ):ℝ)/n))| := by
      apply Finset.sum_congr rfl
      intro i _
      have ht : i+(K+1+L)+1=n+(i+1) := by omega
      change |sample β (2/(n : ℝ)) (((i+(K+1+L)+1:ℕ):ℝ)/n)| = _
      rw [ht, Nat.cast_add, add_div, div_self hn0.ne']
    rw [hleft, hcenter', hright]
    linarith only [hcl,hδ,hnδ]
  have htransition : (∑ i ∈ Finset.range Q, F (i+M))/(n : ℝ) ≤ 5 := by
    have hsum : (∑ i ∈ Finset.range Q, F (i+M)) ≤ (Q:ℝ)*5 := by
      conv_rhs => rw [← nsmul_eq_mul, ← Finset.card_range (n := Q), ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro i _
      have hnat : n+(K+1) ≤ i+M+1 := by dsimp [M]; omega
      have hcast : (n : ℝ)+((K+1:ℕ):ℝ) ≤ ((i+M+1:ℕ):ℝ) := by exact_mod_cast hnat
      apply transition_sample_bound hβ hβ' ha
      apply (le_div_iff₀ hn0).2
      linarith
    apply (div_le_iff₀ hn0).2
    have hq : Q ≤ n := by dsimp [Q, M]; omega
    have hqc : (Q:ℝ) ≤ (n : ℝ) := by exact_mod_cast hq
    linarith only [hsum,hqc]
  have hsplit : (∑ i ∈ Finset.range (2*n), F i) =
      (∑ i ∈ Finset.range L, F i) +
        ((∑ i ∈ Finset.range K, F (i+L)) + F (K+L) +
          (∑ i ∈ Finset.range K, F (i+(K+1+L)))) +
        (∑ i ∈ Finset.range Q, F (i+M)) := by
    have htransEq : (∑ i ∈ Finset.range Q, F (M+i)) =
        ∑ i ∈ Finset.range Q, F (i+M) := by simp only [Nat.add_comm]
    have hmidEq : (∑ i ∈ Finset.range (K+1+K), F (L+i)) =
        (∑ i ∈ Finset.range K, F (i+L)) + F (K+L) +
          ∑ i ∈ Finset.range K, F (i+(K+1+L)) := by
      rw [Finset.sum_range_add, Finset.sum_range_succ]
      simp only [Nat.add_assoc, Nat.add_comm]
    have hpref : (∑ i ∈ Finset.range M, F i) =
        (∑ i ∈ Finset.range L, F i) + ∑ i ∈ Finset.range (K+1+K), F (L+i) := by
      rw [← hM, Finset.sum_range_add]
    rw [← hQ, Finset.sum_range_add, hpref, htransEq, hmidEq]
  have hB : (∑ i ∈ Finset.range (2*n), F i)/(n : ℝ) ≤ 109 := by
    rw [hsplit, add_div, add_div]
    linarith only [hsmall,hcenter,htransition]
  have ht : 2 ≤ ((2*n:ℕ):ℝ)/(n : ℝ) := by push_cast; rw [mul_div_cancel_right₀ _ hn0.ne']
  obtain ⟨hs,hfar⟩ := discrete_mellin_tail_bounds.2 β (2 / (n : ℝ)) n (2*n) hβ ha hn ht
  have htEq : (fun i : ℕ => F (i+(2*n))) =
      (fun i : ℕ => |sample β (2/(n : ℝ)) ((((2*n+i+1:ℕ):ℝ))/(n : ℝ))|) := by
    funext i
    change |sample β (2/(n : ℝ)) (((i+2*n+1:ℕ):ℝ)/n)| = _
    rw [Nat.add_comm i]
  rw [← htEq] at hs hfar
  have htval : ((2*n : ℕ) : ℝ) / (n : ℝ) = 2 := by
    push_cast
    rw [mul_div_cancel_right₀ _ hn0.ne']
  rw [htval] at hfar
  have hsum := (summable_nat_add_iff (2*n)).1 hs
  refine ⟨hsum, ?_⟩
  rw [← hsum.sum_add_tsum_nat_add (2*n), add_div]
  have hfar0 : (2:ℝ)^(-(1 / 2:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  linarith only [hB,hfar,hfar0]

/-- Summed absolute coefficient replacement; the finite small-jump and the
absolute shifted-mesh estimate supply complementary parts, with one scaling. -/
private theorem global_weight_replacement {β E : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 3 / 4)
    (hE : 0 ≤ E) (n : ℕ) (hn : 0 < n)
    (err : ℕ → ℝ) (herr : ∀ m : ℕ, 0 < m → |err m| ≤ E*(m : ℝ)^(-(5 / 2:ℝ))) :
    let e (i : ℕ) := |err (i+1) * secondDiff β (n : ℝ) ((i+1:ℕ):ℝ)|
    Summable e ∧ (∑' i, e i) ≤ 298 * E * (n : ℝ)^(-β-3 / 2) := by
  let e (i : ℕ) := |err (i+1) * secondDiff β (n : ℝ) ((i+1:ℕ):ℝ)|
  let F (i : ℕ) := |sample β (2/(n : ℝ)) (((i+1:ℕ):ℝ)/(n : ℝ))|
  let K := n/2
  let B := (2*E/(n : ℝ)) * (n : ℝ)^(-β-3 / 2)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨_, hK, hK'⟩ := floor_half_bounds n hn
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (div_nonneg (by linarith) hn0.le) (Real.rpow_nonneg hn0.le _)
  obtain ⟨hF, hFbound⟩ := absolute_shifted_mesh_bound (by linarith : 0 ≤ β) hβ' n hn
  change Summable F at hF
  change (∑' i, F i)/(n : ℝ) ≤ 117 at hFbound
  have hstep (i : ℕ) : e (i+K) ≤ B * F (i+K) := by
    let m := i+K+1
    have hm : 0 < m := by dsimp [m]; omega
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmK : ((K+1:ℕ):ℝ) ≤ (m : ℝ) := by exact_mod_cast (show K+1 ≤ m by dsimp [m]; omega)
    have hmcut : (n : ℝ) / 2 ≤ (m : ℝ) := hK'.trans hmK
    have hfrac : (m : ℝ)⁻¹ ≤ 2/(n : ℝ) := by
      apply (le_div_iff₀ hn0).2
      rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ hm0]
      linarith only [hmcut]
    have hp : (m : ℝ)^(-(5 / 2:ℝ)) = (m : ℝ)⁻¹ * (m : ℝ)^(-(3 / 2:ℝ)) := by
      rw [← Real.rpow_neg_one (m : ℝ), ← Real.rpow_add hm0]
      congr 1
      norm_num
    have hnScale :
        (n : ℝ)^(-β-3 / 2) * (n : ℝ)^(β+3 / 2) = 1 := by
      rw [← Real.rpow_add hn0, show (-β-3 / 2)+(β+3 / 2)=0 by ring, Real.rpow_zero]
    have hF' : F (i+K) = (n : ℝ)^(β+3 / 2) * ((m : ℝ)^(-(3 / 2:ℝ)) *
        |secondDiff β (n : ℝ) (m : ℝ)|) := by
      change |sample β (2/(n : ℝ)) ((m : ℝ)/n)| = _
      rw [sample_eq_lattice hn0 hm0, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hn0.le _), abs_of_nonneg (Real.rpow_nonneg hm0.le _)]
    change |err m * secondDiff β (n : ℝ) (m : ℝ)| ≤ _
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_right ((herr m hm).trans (show
      E*(m : ℝ)^(-(5 / 2:ℝ)) ≤ (2*E/(n : ℝ))*(m : ℝ)^(-(3 / 2:ℝ)) by
        rw [hp]
        have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfrac hE) (Real.rpow_nonneg hm0.le (-(3 / 2:ℝ)))
        convert h using 1 <;> ring)) (abs_nonneg (secondDiff β (n : ℝ) (m : ℝ)))
    apply hh.trans_eq
    rw [hF']
    dsimp [B]
    calc
      _ = _ * ((n : ℝ)^(-β-3 / 2)*(n : ℝ)^(β+3 / 2)) := by rw [hnScale,mul_one]
      _ = _ := by ring
  have hFt := (summable_nat_add_iff K).2 hF
  have het : Summable (fun i => e (i+K)) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hstep (hFt.mul_left B)
  have he := (summable_nat_add_iff K).1 het
  refine ⟨he, ?_⟩
  rw [← he.sum_add_tsum_nat_add K]
  have hlocal : ∑ i ∈ Finset.range K, e i ≤ 64*E*(n : ℝ)^(-β-3 / 2) :=
    local_weight_replacement hβ hβ' hE n K hn hK err herr
  have ht := het.tsum_le_tsum hstep (hFt.mul_left B)
  rw [tsum_mul_left] at ht
  have hsmall : 0 ≤ ∑ i ∈ Finset.range K, F i :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have htF : (∑' i, F (i+K)) ≤ (∑' i, F i) :=
    le_trans (le_add_of_nonneg_left hsmall) (hF.sum_add_tsum_nat_add K).le
  have htF' := (le_trans htF ((div_le_iff₀ hn0).mp hFbound))
  have houter := ht.trans (mul_le_mul_of_nonneg_left htF' hB)
  have hscale : B*(117*(n : ℝ)) = 234*E*(n : ℝ)^(-β-3 / 2) := by
    dsimp [B]
    field_simp
    ring
  rw [hscale] at houter
  linarith only [hlocal,houter]

/-- The actual merged Schröder kernel has a uniform absolute summed
replacement error of order n^(-β−3 / 2), fixed coefficient and constant. -/
theorem actual_global_weight_replacement :
    ∃ A > (0:ℝ), ∃ E : ℝ, 0 ≤ E ∧
      ∀ β : ℝ, 1 / 2 ≤ β → β ≤ 3 / 4 → ∀ n : ℕ, 0 < n →
      let e (i : ℕ) := |actualWeightError A (i+1) * secondDiff β (n : ℝ) ((i+1:ℕ):ℝ)|
      Summable e ∧ (∑' i, e i) ≤ 298 * E * (n : ℝ)^(-β-3 / 2) := by
  obtain ⟨A, hA, E, hE, hr⟩ := actual_uniform_weight_error
  exact ⟨A, hA, E, hE, fun β hβ hβ' n hn =>
    global_weight_replacement hβ hβ' hE n hn _ hr⟩

#print axioms actual_global_weight_replacement

end D5.S1.Words.Patterns.Separable.OccupiedKernelWeightReplacement
