/- GID: D5/S0/FiniteGeometry/SylvesterSimplexEhrhartDimensionSevenCoefficient
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/SylvesterSimplexEhrhartDimensionSevenCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Structural coefficient bridges and staged actual-prefix moments for dimension seven. -/

import D5.S0.FiniteGeometry.SylvesterSimplexEhrhartDimensionSeven

noncomputable section

namespace D5.S0.FiniteGeometry.SylvesterSimplexEhrhartDimensionSevenCoefficient

open scoped BigOperators

open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private periodNumerator binomialShiftPolynomial baseSamplePolynomial
  interiorSamplePolynomial sourceEhrhartPolynomial sourceEhrhartPolynomial_eval from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartSamples

open private prefixPeriod prefixBox prefixMass actualMoment actualMoment_zero
  lowKernel highKernel computedMoment computedMoment_eq_actualMoment prefixMass_div_lt
  prefixPeriod_pos powerSumPolynomial lowKernel_eval highKernel_eval
  lowKernel_natDegree_le highKernel_natDegree_le
  unitPolynomial unitPolynomial_sq_coeff_low unitPolynomial_sq_coeff_high
  unitPolynomial_sq_coeff_zero zeroMoment zeroMoment_eq zeroMoment_eq_sum_ite
  periodNumerator_seven_coeff fiberStat fiberStat_eq_sum from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartDimensionSeven

private lemma multiple_kernel_identity (M A j : ℕ) (hM : 0 < M) :
    (if A ≤ j * M then (unitPolynomial M ^ 2).coeff (j * M - A) else 0) =
      (if A / M = j then (if A % M = 0 then 1 else 0 : ℚ) else 0) +
      (if A / M + 1 = j then
        (M + 1 : ℚ) - ((A % M : ℕ) : ℚ) -
          2 * (if A % M = 0 then 1 else 0 : ℚ)
       else 0) +
      (if A / M + 2 = j then
        ((A % M : ℕ) : ℚ) - 1 + (if A % M = 0 then 1 else 0 : ℚ)
       else 0) := by
  let q := A / M
  let r := A % M
  have hr : r < M := Nat.mod_lt A hM
  have hA : q * M + r = A := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod A M
  change (if A ≤ j * M then (unitPolynomial M ^ 2).coeff (j * M - A) else 0) =
    (if q = j then (if r = 0 then 1 else 0 : ℚ) else 0) +
    (if q + 1 = j then
      (M + 1 : ℚ) - (r : ℚ) - 2 * (if r = 0 then 1 else 0 : ℚ)
     else 0) +
    (if q + 2 = j then (r : ℚ) - 1 + (if r = 0 then 1 else 0 : ℚ) else 0)
  by_cases hq0 : q = j
  · subst j
    by_cases hr0 : r = 0
    · simp only [hr0, if_pos, Nat.cast_zero]
      have hle : A ≤ q * M := by omega
      rw [if_pos hle]
      have hsub : q * M - A = 0 := by omega
      rw [hsub, unitPolynomial_sq_coeff_low M 0 hM]
      norm_num
    · have hgt : q * M < A := by omega
      simp [if_neg (Nat.not_le.mpr hgt), hr0, hM.ne']
  · by_cases hq1 : q + 1 = j
    · subst j
      have hle : A ≤ (q + 1) * M := by
        simp only [Nat.add_mul, one_mul]
        omega
      rw [if_pos hle]
      by_cases hr0 : r = 0
      · have hsub : (q + 1) * M - A = M := by
          simp only [Nat.add_mul, one_mul]
          omega
        rw [hsub, unitPolynomial_sq_coeff_high M M hM (le_refl M) (by omega)]
        simp [hq0, hr0, hM.ne']
        have hnat : 2 * M - 1 - M = M - 1 := by omega
        rw [hnat, Nat.cast_sub (by omega : 1 ≤ M)]
        ring
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
        have hsub : (q + 1) * M - A = M - r := by
          simp only [Nat.add_mul, one_mul]
          omega
        rw [hsub, unitPolynomial_sq_coeff_low M (M - r) (by omega)]
        simp [hq0, hr0, hM.ne']
        rw [Nat.cast_sub (Nat.le_of_lt hr)]
        ring
    · by_cases hq2 : q + 2 = j
      · subst j
        have hle : A ≤ (q + 2) * M := by
          simp only [Nat.add_mul]
          nlinarith
        rw [if_pos hle]
        by_cases hr0 : r = 0
        · have hsub : (q + 2) * M - A = 2 * M := by
            simp only [Nat.add_mul]
            omega
          rw [hsub, unitPolynomial_sq_coeff_zero M (2 * M) (by omega)]
          simp [hq0, hq1, hr0, hM.ne']
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
          have hsub : (q + 2) * M - A = 2 * M - r := by
            simp only [Nat.add_mul]
            omega
          rw [hsub, unitPolynomial_sq_coeff_high M (2 * M - r) hM
            (by omega) (by omega)]
          simp [hq0, hq1, hr0, hM.ne']
          have hnat : 2 * M - 1 - (2 * M - r) = r - 1 := by omega
          rw [hnat, Nat.cast_sub (by omega : 1 ≤ r)]
          ring
      · by_cases hjq : j < q
        · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hjq)
          have hjstep : j * M < (j + 1) * M := by
            rw [Nat.add_mul]
            omega
          have hnext : (j + 1) * M ≤ A := by
            calc
              (j + 1) * M ≤ (j + 1) * M + d * M := Nat.le_add_right _ _
              _ ≤ (j + 1) * M + d * M + r := Nat.le_add_right _ _
              _ = A := by
                rw [← hA, hd]
                simp [Nat.succ_eq_add_one, Nat.add_mul, Nat.add_assoc]
          have hgt : j * M < A := by
            omega
          simp [if_neg (Nat.not_le.mpr hgt), hq0, hq1, hq2]
        · have hj : q + 3 ≤ j := by omega
          obtain ⟨d, hd⟩ : ∃ d, j = q + 3 + d := Nat.exists_eq_add_of_le hj
          have hle : A ≤ j * M := by
            rw [hd, ← hA]
            simp only [Nat.add_mul]
            omega
          have hfar : 2 * M - 1 < j * M - A := by
            rw [hd, ← hA]
            simp only [Nat.add_mul]
            omega
          rw [if_pos hle, unitPolynomial_sq_coeff_zero M (j * M - A) hfar]
          simp [hq0, hq1, hq2]

private lemma predecessor_kernel_identity (M A j : ℕ) (hM : 0 < M) (hj : 0 < j) :
    (if A ≤ j * M - 1 then
        (unitPolynomial M ^ 2).coeff (j * M - 1 - A)
     else 0) =
      (if A / M + 1 = j then (M : ℚ) - ((A % M : ℕ) : ℚ) else 0) +
      (if A / M + 2 = j then ((A % M : ℕ) : ℚ) else 0) := by
  let q := A / M
  let r := A % M
  have hr : r < M := Nat.mod_lt A hM
  have hA : q * M + r = A := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod A M
  change (if A ≤ j * M - 1 then
      (unitPolynomial M ^ 2).coeff (j * M - 1 - A)
    else 0) =
    (if q + 1 = j then (M : ℚ) - (r : ℚ) else 0) +
    (if q + 2 = j then (r : ℚ) else 0)
  by_cases hq1 : q + 1 = j
  · subst j
    have hle : A ≤ (q + 1) * M - 1 := by
      simp only [Nat.add_mul, one_mul]
      omega
    have hsub : (q + 1) * M - 1 - A = M - 1 - r := by
      simp only [Nat.add_mul, one_mul]
      omega
    rw [if_pos hle, hsub,
      unitPolynomial_sq_coeff_low M (M - 1 - r) (by omega)]
    simp [hM.ne']
    rw [Nat.cast_sub (by omega : r ≤ M - 1),
      Nat.cast_sub (by omega : 1 ≤ M)]
    ring
  · by_cases hq2 : q + 2 = j
    · subst j
      have hle : A ≤ (q + 2) * M - 1 := by
        simp only [Nat.add_mul]
        omega
      have hsub : (q + 2) * M - 1 - A = 2 * M - 1 - r := by
        simp only [Nat.add_mul]
        omega
      rw [if_pos hle, hsub,
        unitPolynomial_sq_coeff_high M (2 * M - 1 - r) hM
          (by omega) (by omega)]
      simp [hq1, hM.ne']
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * M),
        Nat.cast_sub (by omega : r ≤ 2 * M - 1)]
      have hcast : ((2 * M - 1 : ℕ) : ℚ) = 2 * (M : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * M)]
        norm_num
      rw [hcast]
      rw [Nat.cast_mul]
      ring
    · by_cases hjq : j ≤ q
      · obtain ⟨d, hd⟩ : ∃ d, q = j + d := Nat.exists_eq_add_of_le hjq
        have hjM : 0 < j * M := Nat.mul_pos hj hM
        have hgt : j * M - 1 < A := by
          rw [← hA, hd]
          simp only [Nat.add_mul]
          omega
        simp [if_neg (Nat.not_le.mpr hgt), hq1, hq2]
      · have hfarq : q + 3 ≤ j := by omega
        obtain ⟨d, hd⟩ : ∃ d, j = q + 3 + d :=
          Nat.exists_eq_add_of_le hfarq
        have hle : A ≤ j * M - 1 := by
          rw [hd, ← hA]
          simp only [Nat.add_mul]
          omega
        have hfar : 2 * M - 1 < j * M - 1 - A := by
          rw [hd, ← hA]
          simp only [Nat.add_mul]
          omega
        rw [if_pos hle, unitPolynomial_sq_coeff_zero M (j * M - 1 - A) hfar]
        simp [hq1, hq2]

set_option linter.constructorNameAsVariable false in
private lemma periodNumerator_seven_coeff_multiple (j : ℕ) :
    (periodNumerator 7).coeff (j * prefixPeriod 6) =
      zeroMoment 6 j +
        (if 0 < j then
          fiberStat (j - 1) (prefixPeriod 6 + 1) (-1) (-2)
         else 0) +
        (if 1 < j then fiberStat (j - 2) (-1) 1 1 else 0) := by
  classical
  rw [periodNumerator_seven_coeff, zeroMoment_eq_sum_ite]
  simp_rw [multiple_kernel_identity (prefixPeriod 6) _ j (prefixPeriod_pos 6)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hfirst :
      (∑ x ∈ prefixBox 6,
        if prefixMass 6 x / prefixPeriod 6 + 1 = j then
          (prefixPeriod 6 + 1 : ℚ) -
            ((prefixMass 6 x % prefixPeriod 6 : ℕ) : ℚ) -
            2 * (if prefixMass 6 x % prefixPeriod 6 = 0 then 1 else 0 : ℚ)
        else 0) =
        if 0 < j then fiberStat (j - 1) (prefixPeriod 6 + 1) (-1) (-2)
        else 0 := by
    by_cases hj : 0 < j
    · rw [if_pos hj, fiberStat_eq_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hpred : prefixMass 6 x / prefixPeriod 6 = j - 1 ↔
          prefixMass 6 x / prefixPeriod 6 + 1 = j := by omega
      simp only [hpred]
      by_cases hq : prefixMass 6 x / prefixPeriod 6 + 1 = j <;>
        by_cases hr : prefixMass 6 x % prefixPeriod 6 = 0 <;>
        simp [hq, hr] <;> ring
    · have hj_eq : j = 0 := by omega
      subst j
      simp
  have hsecond :
      (∑ x ∈ prefixBox 6,
        if prefixMass 6 x / prefixPeriod 6 + 2 = j then
          ((prefixMass 6 x % prefixPeriod 6 : ℕ) : ℚ) - 1 +
            (if prefixMass 6 x % prefixPeriod 6 = 0 then 1 else 0 : ℚ)
        else 0) =
        if 1 < j then fiberStat (j - 2) (-1) 1 1 else 0 := by
    by_cases hj : 1 < j
    · rw [if_pos hj, fiberStat_eq_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hpred : prefixMass 6 x / prefixPeriod 6 = j - 2 ↔
          prefixMass 6 x / prefixPeriod 6 + 2 = j := by omega
      simp only [hpred]
      by_cases hq : prefixMass 6 x / prefixPeriod 6 + 2 = j <;>
        by_cases hr : prefixMass 6 x % prefixPeriod 6 = 0 <;>
        simp [hq, hr] <;> ring
    · have hjle : j ≤ 1 := by omega
      obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · simp
      · simp
  rw [hfirst, hsecond]

set_option linter.constructorNameAsVariable false in
private lemma periodNumerator_seven_coeff_predecessor (j : ℕ) (hj : 0 < j) :
    (periodNumerator 7).coeff (j * prefixPeriod 6 - 1) =
      fiberStat (j - 1) (prefixPeriod 6) (-1) 0 +
        (if 1 < j then fiberStat (j - 2) 0 1 0 else 0) := by
  classical
  rw [periodNumerator_seven_coeff]
  simp_rw [predecessor_kernel_identity (prefixPeriod 6) _ j
    (prefixPeriod_pos 6) hj]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ x ∈ prefixBox 6,
        if prefixMass 6 x / prefixPeriod 6 + 1 = j then
          (prefixPeriod 6 : ℚ) -
            ((prefixMass 6 x % prefixPeriod 6 : ℕ) : ℚ)
        else 0) = fiberStat (j - 1) (prefixPeriod 6) (-1) 0 := by
    rw [fiberStat_eq_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hpred : prefixMass 6 x / prefixPeriod 6 = j - 1 ↔
        prefixMass 6 x / prefixPeriod 6 + 1 = j := by omega
    simp only [hpred]
    by_cases hq : prefixMass 6 x / prefixPeriod 6 + 1 = j <;>
      simp [hq] <;> ring
  have hsecond :
      (∑ x ∈ prefixBox 6,
        if prefixMass 6 x / prefixPeriod 6 + 2 = j then
          ((prefixMass 6 x % prefixPeriod 6 : ℕ) : ℚ)
        else 0) =
        if 1 < j then fiberStat (j - 2) 0 1 0 else 0 := by
    by_cases hj1 : 1 < j
    · rw [if_pos hj1, fiberStat_eq_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hpred : prefixMass 6 x / prefixPeriod 6 = j - 2 ↔
          prefixMass 6 x / prefixPeriod 6 + 2 = j := by omega
      simp only [hpred]
      by_cases hq : prefixMass 6 x / prefixPeriod 6 + 2 = j <;>
        simp [hq]
    · have hj_eq : j = 1 := by omega
      subst j
      simp
  rw [hfirst, hsecond]

private lemma computedMoment_stage_four_zero (p : ℕ) (hp : p ≤ 3) :
    computedMoment 4 0 p =
      if p = 0 then 349 else if p = 1 then 452578 else
        if p = 2 then 645075578 else 965137501048 := by
  have hstage0 (q p : ℕ) :
      computedMoment 0 q p = if q = 0 then if p = 0 then 1 else 0 else 0 := by
    rw [computedMoment]
  have hstage1 (q p : ℕ) :
      computedMoment 1 q p = if q = 0 then if p = 0 then 2 else 1 else 0 := by
    by_cases hq0 : q = 0
    · subst q
      rw [computedMoment]
      simp_rw [hstage0]
      norm_num [Finset.sum_range_succ]
      rw [Polynomial.coeff_zero_eq_eval_zero]
      change (lowKernel (prefixPeriod 0) p).eval ((0 : ℕ) : ℚ) = _
      have hlow := lowKernel_eval (prefixPeriod 0) 0 p (by omega)
      rw [hlow]
      by_cases hp0 : p = 0
      · subst p
        norm_num [prefixPeriod, sylvester]
      · simp [prefixPeriod, sylvester, Finset.sum_range_succ, hp0]
    · by_cases hq1 : q = 1
      · subst q
        rw [computedMoment]
        simp_rw [hstage0]
        norm_num [Finset.sum_range_succ]
        rw [Polynomial.coeff_zero_eq_eval_zero]
        change (highKernel (prefixPeriod 0) p).eval ((0 : ℕ) : ℚ) = _
        have hhigh := highKernel_eval (prefixPeriod 0) 0 p
        rw [hhigh]
        simp
      · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
        have hpred : q - 1 ≠ 0 := by omega
        rw [computedMoment]
        simp_rw [hstage0]
        simp [hq0, hqpos, hpred]
  have hdot (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree < n) :
      (∑ a ∈ Finset.range n, P.coeff a * computedMoment 1 0 a) =
        P.eval 0 + P.eval 1 := by
    simp_rw [hstage1]
    simp only [if_pos, ite_mul, one_mul]
    rw [Polynomial.eval_eq_sum_range' hP, Polynomial.eval_eq_sum_range' hP,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      norm_num
      ring
    · simp [ha0]
  have hzero (P : Polynomial ℚ) (n : ℕ) :
      (∑ a ∈ Finset.range n, P.coeff a * computedMoment 1 1 a) = 0 := by
    simp_rw [hstage1]
    simp
  have hstage2 (q p : ℕ) (hp : p ≤ 5) :
      computedMoment 2 q p =
        if q = 0 then
          if p = 0 then 5 else if p = 1 then 14 else if p = 2 then 54 else
            if p = 3 then 224 else if p = 4 then 978 else 4424
        else if q = 1 then 1 else 0 := by
    by_cases hq0 : q = 0
    · subst q
      rw [computedMoment]
      simp only [lt_self_iff_false, if_false, add_zero, if_pos]
      rw [hdot (lowKernel (prefixPeriod 1) p) (p + 2) (by
        have := lowKernel_natDegree_le (prefixPeriod 1) p
        omega)]
      have hlow0 := lowKernel_eval (prefixPeriod 1) 0 p (by omega)
      have hlow1 := lowKernel_eval (prefixPeriod 1) 1 p (by
        norm_num [prefixPeriod, sylvester])
      change (lowKernel (prefixPeriod 1) p).eval ((0 : ℕ) : ℚ) +
        (lowKernel (prefixPeriod 1) p).eval ((1 : ℕ) : ℚ) = _
      rw [hlow0, hlow1]
      interval_cases p <;>
        norm_num [prefixPeriod, sylvester, Finset.sum_range_succ]
    · by_cases hq1 : q = 1
      · subst q
        rw [computedMoment]
        simp only [if_false, if_true, add_zero, Nat.reduceSubDiff]
        rw [hzero, zero_add,
          hdot (highKernel (prefixPeriod 1) p) (p + 2) (by
            have := highKernel_natDegree_le (prefixPeriod 1) p
            omega)]
        have hhigh0 := highKernel_eval (prefixPeriod 1) 0 p
        have hhigh1 := highKernel_eval (prefixPeriod 1) 1 p
        change (highKernel (prefixPeriod 1) p).eval ((0 : ℕ) : ℚ) +
          (highKernel (prefixPeriod 1) p).eval ((1 : ℕ) : ℚ) = _
        rw [hhigh0, hhigh1]
        simp
      · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
        have hpred : q - 1 ≠ 0 := by omega
        rw [computedMoment]
        simp_rw [hstage1]
        simp [hq0, hq1, hqpos, hpred]
  have hm20 (a : ℕ) (ha : a ≤ 5) :
      computedMoment 2 0 a =
        (0 : ℚ) ^ a + 2 ^ a + 3 ^ a + 4 ^ a + 5 ^ a := by
    rw [hstage2 0 a ha]
    interval_cases a <;> norm_num
  have hm21 (a : ℕ) (ha : a ≤ 5) : computedMoment 2 1 a = (1 : ℚ) ^ a := by
    rw [hstage2 1 a ha]
    norm_num
  have hdot20 (P : Polynomial ℚ) (n : ℕ) (hn : n ≤ 6)
      (hP : P.natDegree < n) :
      (∑ a ∈ Finset.range n, P.coeff a * computedMoment 2 0 a) =
        P.eval 0 + P.eval 2 + P.eval 3 + P.eval 4 + P.eval 5 := by
    simp_rw [Polynomial.eval_eq_sum_range' hP]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hm20 a (by have := Finset.mem_range.mp ha; omega)]
    ring
  have hdot21 (P : Polynomial ℚ) (n : ℕ) (hn : n ≤ 6)
      (hP : P.natDegree < n) :
      (∑ a ∈ Finset.range n, P.coeff a * computedMoment 2 1 a) = P.eval 1 := by
    rw [Polynomial.eval_eq_sum_range' hP]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hm21 a (by have := Finset.mem_range.mp ha; omega)]
  have hzero2 (q : ℕ) (hq : 2 ≤ q) (P : Polynomial ℚ) (n : ℕ) (hn : n ≤ 6) :
      (∑ a ∈ Finset.range n, P.coeff a * computedMoment 2 q a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [hstage2 q a (by have := Finset.mem_range.mp ha; omega)]
    simp [show q ≠ 0 by omega, show q ≠ 1 by omega]
  have hstage3 (q p : ℕ) (hp : p ≤ 4) :
      computedMoment 3 q p =
        if q = 0 then
          if p = 0 then 21 else if p = 1 then 554 else if p = 2 then 17242 else
            if p = 3 then 572468 else 19800166
        else if q = 1 then
          if p = 0 then 20 else if p = 1 then 306 else if p = 2 then 6578 else
            if p = 3 then 168852 else 4806926
        else if q = 2 then 1 else 0 := by
    by_cases hq0 : q = 0
    · subst q
      rw [computedMoment]
      simp only [lt_self_iff_false, if_false, add_zero, if_pos]
      rw [hdot20 (lowKernel (prefixPeriod 2) p) (p + 2) (by omega) (by
        have := lowKernel_natDegree_le (prefixPeriod 2) p
        omega)]
      have hlow (r : ℕ) (hr : r ≤ 6) :
          (lowKernel (prefixPeriod 2) p).eval (r : ℚ) =
            ∑ x ∈ Finset.range (prefixPeriod 2 - r + 1),
              (((prefixPeriod 2 + 1) * r + prefixPeriod 2 * x : ℕ) : ℚ) ^ p :=
        lowKernel_eval (prefixPeriod 2) r p (by
          norm_num [prefixPeriod, sylvester]
          exact hr)
      have hlow0 := hlow 0 (by omega)
      have hlow2 := hlow 2 (by omega)
      have hlow3 := hlow 3 (by omega)
      have hlow4 := hlow 4 (by omega)
      have hlow5 := hlow 5 (by omega)
      norm_num only [Nat.cast_ofNat] at hlow0 hlow2 hlow3 hlow4 hlow5
      change (lowKernel (prefixPeriod 2) p).eval (0 : ℚ) +
          (lowKernel (prefixPeriod 2) p).eval (2 : ℚ) +
          (lowKernel (prefixPeriod 2) p).eval (3 : ℚ) +
          (lowKernel (prefixPeriod 2) p).eval (4 : ℚ) +
          (lowKernel (prefixPeriod 2) p).eval (5 : ℚ) = _
      rw [hlow0, hlow2, hlow3, hlow4, hlow5]
      interval_cases p <;>
        norm_num [prefixPeriod, sylvester, Finset.sum_range_succ]
    · by_cases hq1 : q = 1
      · subst q
        rw [computedMoment]
        simp only [if_pos, Nat.reduceSubDiff, if_false]
        rw [hdot21 (lowKernel (prefixPeriod 2) p) (p + 2) (by omega) (by
            have := lowKernel_natDegree_le (prefixPeriod 2) p
            omega),
          hdot20 (highKernel (prefixPeriod 2) p) (p + 2) (by omega) (by
            have := highKernel_natDegree_le (prefixPeriod 2) p
            omega)]
        have hlow : (lowKernel (prefixPeriod 2) p).eval (1 : ℚ) =
            ∑ x ∈ Finset.range (prefixPeriod 2 - 1 + 1),
              (((prefixPeriod 2 + 1) * 1 + prefixPeriod 2 * x : ℕ) : ℚ) ^ p :=
          lowKernel_eval (prefixPeriod 2) 1 p (by
            norm_num [prefixPeriod, sylvester])
        have hhigh0 := highKernel_eval (prefixPeriod 2) 0 p
        have hhigh2 := highKernel_eval (prefixPeriod 2) 2 p
        have hhigh3 := highKernel_eval (prefixPeriod 2) 3 p
        have hhigh4 := highKernel_eval (prefixPeriod 2) 4 p
        have hhigh5 := highKernel_eval (prefixPeriod 2) 5 p
        norm_num only [Nat.cast_ofNat] at hlow hhigh0 hhigh2 hhigh3 hhigh4 hhigh5
        simp only [Nat.zero_lt_succ, if_true, Nat.one_ne_zero, if_false]
        rw [hlow, hhigh0, hhigh2, hhigh3, hhigh4, hhigh5]
        interval_cases p <;>
          norm_num [prefixPeriod, sylvester, Finset.sum_range_succ]
      · by_cases hq2 : q = 2
        · subst q
          rw [computedMoment]
          simp only [if_pos, Nat.reduceSubDiff, if_false]
          rw [hzero2 2 (by omega) (lowKernel (prefixPeriod 2) p) (p + 2)
              (by omega), zero_add,
            hdot21 (highKernel (prefixPeriod 2) p) (p + 2) (by omega) (by
              have := highKernel_natDegree_le (prefixPeriod 2) p
              omega)]
          have hhigh := highKernel_eval (prefixPeriod 2) 1 p
          change (highKernel (prefixPeriod 2) p).eval ((1 : ℕ) : ℚ) = _
          rw [hhigh]
          simp
        · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
          have hqpred : 2 ≤ q - 1 := by omega
          rw [computedMoment]
          simp only [if_pos hqpos]
          rw [hzero2 q (by omega) (lowKernel (prefixPeriod 2) p) (p + 2) (by omega),
            hzero2 (q - 1) hqpred (highKernel (prefixPeriod 2) p) (p + 2) (by omega)]
          simp [hq0, hq1, hq2]
  have hdot30 (P : Polynomial ℚ) (n : ℕ) (hn : n ≤ 5)
      (hP : P.natDegree < n) :
      (∑ a ∈ Finset.range n, P.coeff a * computedMoment 3 0 a) =
        610490 * P.eval 0 - 2513825 * P.eval 1 + 3885343 * P.eval 2 -
          2671641 * P.eval 3 + 689654 * P.eval 4 := by
    simp_rw [Polynomial.eval_eq_sum_range' hP]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a < 5 := lt_of_lt_of_le (Finset.mem_range.mp ha) hn
    rw [hstage3 0 a (by have := Finset.mem_range.mp ha; omega)]
    interval_cases a <;> norm_num <;> ring
  have hb3 : bernoulli 3 = 0 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_three]
  rw [computedMoment]
  simp only [lt_self_iff_false, if_false, add_zero]
  rw [hdot30 _ _ (by omega) (by
    have := lowKernel_natDegree_le (prefixPeriod 3) p
    omega)]
  interval_cases p <;> norm_num [Finset.sum_range_succ, lowKernel,
    powerSumPolynomial, Polynomial.eval_finsetSum, prefixPeriod, sylvester,
    hb3, Nat.choose]

end D5.S0.FiniteGeometry.SylvesterSimplexEhrhartDimensionSevenCoefficient
