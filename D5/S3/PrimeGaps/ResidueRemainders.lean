/- GID: D5/S3/PrimeGaps/ResidueRemainders
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the coefficient remainder estimates for the replaced residue weights. -/

/- Ported from openai/LongGapsBetweenPrimes commit 8f5fa88c88b4750028c05b66b081d56a92418054.
   Modified by trureturing on 2026-09-04: repository routing and module split. -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import D5.S3.PrimeGaps.IntegerAverages

namespace LongGapsBetweenPrimes

noncomputable section

/-- The partial coefficient sum over small divisors coprime to `m`. -/
def coefficientRemainder (P m : ℕ) (D : ℝ) : ℝ :=
  ∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) ≤ D / m ∧ d.Coprime m), coefficient P d / d.totient

/-- Express the coefficient remainder as a sum over divisor indices. -/
lemma coefficientRemainder_eq_sum (P m : ℕ) (D : ℝ) :
    coefficientRemainder P m D =
      ∑ d : DivisorIndex P,
        if (d.val : ℝ) ≤ D / m ∧ d.val.Coprime m then
          coefficient P d.val / d.val.totient else 0 := by
  rw [coefficientRemainder, Finset.sum_filter]
  exact (sum_divisorIndex P _).symm

/-- The local basis product for one divisor and tuple coordinate. -/
def coordinateBasis {P k : ℕ}
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (d : DivisorIndex P) (i : Fin k) (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∏ p : PrimeIndex P, if p.val ∣ d.val then f p (some i) (t p) else 1

/-- Factor a tuple's product basis function over its coordinates. -/
lemma productBasis_tupleAssignment {P k : ℕ}
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (r : DivisorTuple P k)
    (hr : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (t : (p : PrimeIndex P) → Fin p.val) :
    productBasis f (tupleAssignment r) t = ∏ i, coordinateBasis f (r i) i t := by
  classical
  unfold productBasis coordinateBasis
  rw [← tupleAssignment_prod r hr]
  apply Finset.prod_congr rfl
  intro p _
  cases tupleAssignment r p <;> simp [hf]

/-- Expand a basis weight as a sum of products over tuple coordinates. -/
lemma basisWeight_eq_tupleSum {P k : ℕ} (D : ℝ)
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hf : ∀ p t, f p none t = 1) (t : (p : PrimeIndex P) → Fin p.val) :
    basisWeight P k D f t =
      ∑ r ∈ tupleRegion P k D, ∏ i, coefficient P (r i).val * coordinateBasis f (r i) i t := by
  rw [basisWeight, Finset.sum_coe_sort (tupleRegion P k D)
    (fun r => tupleAmplitude r * productBasis f (tupleAssignment r) t)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [productBasis_tupleAssignment f hf r (Finset.mem_filter.mp hr).2.1 t,
    tupleAmplitude, Finset.prod_mul_distrib]

/-- The local basis with coordinate `i` replaced by the constant `1 / (p - 1)`. -/
def replacedLocalBasis {p k : ℕ} (root : Fin k → Fin p) (i : Fin k)
    (j : Option (Fin k)) (t : Fin p) : ℝ :=
  match j with
  | none => 1
  | some j => if j = i then 1 / ((p : ℝ) - 1) else residueFactor (root j) t

/-- Replacing a coordinate reduces its divisor basis factor to the reciprocal totient. -/
lemma coordinateBasis_replaced {P k : ℕ} (hP : Squarefree P)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (i j : Fin k)
    (d : DivisorIndex P) (t : (p : PrimeIndex P) → Fin p.val) :
    coordinateBasis (fun p => replacedLocalBasis (root p) i) d j t =
      if j = i then 1 / (d.val.totient : ℝ) else
        coordinateBasis (fun p => rawLocalBasis (root p)) d j t := by
  classical
  by_cases h : j = i
  · simp only [coordinateBasis, replacedLocalBasis, if_pos h]
    rw [prod_primeIndex_dvd hP.ne_zero (Nat.dvd_of_mem_divisors d.property)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)),
      prod_primeFactors_inv_sub_one
        (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors d.property))]
  · simp [coordinateBasis, replacedLocalBasis, rawLocalBasis, h]

/-- The residue weight with one marked coordinate replaced by constants. -/
def replacedResidueWeight (P k : ℕ) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (i : Fin k)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  basisWeight P k D (fun p => replacedLocalBasis (root p) i) t

/-- Split the replaced weight into smaller tuples and coefficient remainders. -/
lemma replacedResidueWeight_split {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (i : Fin (k + 1))
    (t : (p : PrimeIndex P) → Fin p.val) :
    replacedResidueWeight P (k + 1) D root i t =
      ∑ r ∈ tupleRegion P k D, coefficientRemainder P (tupleProduct r) D *
        ∏ j, coefficient P (r j).val *
          coordinateBasis (fun p => rawLocalBasis (fun j => root p (i.succAbove j))) (r j) j t := by
  classical
  rw [replacedResidueWeight, basisWeight_eq_tupleSum D _ (fun _ _ => rfl),
    tupleSum_split i D (fun j d => coefficient P d.val *
      coordinateBasis (fun p => replacedLocalBasis (root p) i) d j t)]
  simp_rw [coordinateBasis_replaced hP]
  simp [coefficientRemainder_eq_sum, coordinateBasis, rawLocalBasis, div_eq_mul_inv]

/-- Bound the coefficient mass of divisors sharing a prime with `m` by a prime sum. -/
lemma coefficient_noncoprime_le {P m : ℕ} (hP : 1 < P) (hsq : Squarefree P)
    (hm : m ∣ P) (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) :
    (∑ d ∈ P.divisors.filter (fun d => ¬d.Coprime m), |coefficient P d| / d.totient) ≤
      ∑ p ∈ m.primeFactors, 4 / (p : ℝ) := by
  classical
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hsq.ne_zero (by simpa using hm)
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ p ∈ m.primeFactors,
        if p ∣ d then |coefficient P d| / d.totient else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro d _
      by_cases hdm : ¬d.Coprime m
      · rw [if_pos hdm]
        obtain ⟨p, hp, hpd, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hdm
        have h := Finset.single_le_sum
          (f := fun p => if p ∣ d then |coefficient P d| / d.totient else 0)
          (fun p _ => by split_ifs <;> positivity) (hp.mem_primeFactors hpm hm0)
        simpa only [if_pos hpd] using h
      · rw [if_neg hdm]
        positivity
    _ = ∑ p ∈ m.primeFactors,
        ∑ d ∈ P.divisors.filter (fun d => p ∣ d), |coefficient P d| / d.totient := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpP := (Nat.dvd_of_mem_primeFactors hp).trans hm
      exact coefficient_prime_incidence hP hsq (Nat.prime_of_mem_primeFactors hp) hpP
        (hcoeff p (Nat.mem_divisors.mpr ⟨hpP, hsq.ne_zero⟩))

/-- A lower bound on prime factors controls their reciprocal sum using `log m`. -/
lemma sum_primeFactors_inv_le {P m : ℕ} (hP : Squarefree P) (hm : m ∣ P)
    {M : ℝ} (hM : 0 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    (∑ p ∈ m.primeFactors, 4 / (p : ℝ)) ≤ 4 * Real.log m / (M * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (m.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log m := by
    calc
      _ = ∑ p ∈ m.primeFactors, Real.log 2 := by simp
      _ ≤ ∑ p ∈ m.primeFactors, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log (by norm_num)
          (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
      _ = Real.log m := by
        rw [← Real.log_prod (fun p hp =>
          Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero),
          ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd hm)]
  calc
    _ ≤ ∑ p ∈ m.primeFactors, 4 / M := by
      apply Finset.sum_le_sum
      intro p hp
      apply div_le_div_of_nonneg_left (by norm_num) hM
      exact hmin p ((Nat.prime_of_mem_primeFactors hp).mem_primeFactors
        ((Nat.dvd_of_mem_primeFactors hp).trans hm) hP.ne_zero)
    _ = (4 / M) * (m.primeFactors.card : ℝ) := by simp [mul_comm]
    _ ≤ (4 / M) * (Real.log m / Real.log 2) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hlog2).mpr hcard) (by positivity)
    _ = _ := by ring

/-- The coefficient remainder is nonnegative when its cutoff includes one. -/
lemma coefficientRemainder_nonneg {P m : ℕ} (hP : 1 < P) (hm : 0 < m)
    {D : ℝ} (hcut : (m : ℝ) ≤ D) : 0 ≤ coefficientRemainder P m D := by
  apply partial_cancellation_nonneg hP _ (Finset.filter_subset _ _)
  refine Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (by omega), ?_, by simp⟩
  exact (le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mpr (by simpa using hcut)

/-- Rankin's bound for the absolute coefficient tail. -/
lemma coefficient_tail_le {P : ℕ} {v β : ℝ} (hv : 1 ≤ v) (hβ : 0 ≤ β) :
    (∑ d ∈ P.divisors.filter (fun d : ℕ => v < (d : ℝ)), |coefficient P d| / d.totient) ≤
      v ^ (-β) * coefficientAbsMoment P β := by
  classical
  have h1 : (1 : ℕ) ∉ P.divisors.filter (fun d : ℕ => v < (d : ℝ)) := by
    simp only [Finset.mem_filter, Nat.cast_one, not_and]
    exact fun _ => not_lt_of_ge hv
  simpa only [Finset.filter_erase, Finset.erase_eq_of_notMem h1,
    coefficientAbsMoment, div_mul_eq_mul_div] using
    moment_tail_le (P.divisors.erase 1) (fun d => |coefficient P d| / d.totient)
      (fun d => (d : ℝ)) v β (zero_lt_one.trans_le hv) hβ
      (fun d _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (fun d _ => Nat.cast_nonneg _)

/-- Bound the coefficient remainder by the discarded tail and noncoprime mass. -/
lemma coefficientRemainder_le_tail_add_overlap {P m : ℕ} (hP : 1 < P)
    (hm : 0 < m) {D : ℝ} (hcut : (m : ℝ) ≤ D) :
    coefficientRemainder P m D ≤
      (∑ d ∈ P.divisors.filter (fun d : ℕ => D / m < (d : ℝ)), |coefficient P d| / d.totient) +
      ∑ d ∈ P.divisors.filter (fun d => ¬d.Coprime m), |coefficient P d| / d.totient := by
  classical
  have h1 : (1 : ℕ) ∈ P.divisors.filter
      (fun d : ℕ => (d : ℝ) ≤ D / m ∧ d.Coprime m) := by
    refine Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (by omega), ?_, by simp⟩
    exact (le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mpr (by simpa using hcut)
  rw [coefficientRemainder, partial_cancellation hP _ (Finset.filter_subset _ _) h1,
    ← Finset.filter_not]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d _
  have hnonneg : 0 ≤ |coefficient P d| / (d.totient : ℝ) := by positivity
  by_cases hd : (d : ℝ) ≤ D / m <;> by_cases hdm : d.Coprime m <;>
    simp [← not_le, hd, hdm, hnonneg]

/-- Bound the coefficient remainder by a power tail and an error from shared primes. -/
lemma coefficientRemainder_le {P m : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hm : m ∣ P)
    (hcut : (m : ℝ) ≤ D) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    coefficientRemainder P m D ≤ C * ((m : ℝ) / D) ^ β +
      4 * Real.log D / (M * Real.log 2) := by
  have hm0 : 0 < m := Nat.pos_of_mem_divisors
    (Nat.mem_divisors.mpr ⟨hm, h.squarefree.ne_zero⟩)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hv : 1 ≤ D / m := (le_div_iff₀ hmR).mpr (by simpa using hcut)
  apply (coefficientRemainder_le_tail_add_overlap h.one_lt hm0 hcut).trans
  apply add_le_add
  · calc
      _ ≤ (D / m) ^ (-β) * coefficientAbsMoment P β := coefficient_tail_le hv hβ
      _ ≤ (D / m) ^ (-β) * C := mul_le_mul_of_nonneg_left
        (h.absMoment_le β hβ (by linarith)) (Real.rpow_nonneg (by positivity) _)
      _ = C * ((m : ℝ) / D) ^ β := by
        rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
        exact mul_comm _ _
  · apply (coefficient_noncoprime_le h.one_lt h.squarefree hm h.abs_le_one).trans
    apply (sum_primeFactors_inv_le h.squarefree hm hM hmin).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.log_le_log hmR hcut) (by norm_num)) (by positivity)

/-- An exponential assignment row bound valid for every tuple length. -/
lemma assignment_row_bound_all {α : Type*} [Fintype α]
    (size : α → ℕ) {k : ℕ} (σ : α → Option (Fin k))
    {M D : ℝ} (hM : 1 < M) (hsize : ∀ p, M ≤ (size p : ℝ))
    (hcut : (assignmentProduct size σ : ℝ) ≤ D) :
    (∏ p, localRow (size p) k (σ p)) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) := by
  cases k with
  | zero =>
      have hσ (p : α) : σ p = none := Subsingleton.elim _ _
      simp [hσ, localRow]
  | succ k =>
      exact assignment_row_bound size (Nat.succ_pos k) σ hM hsize hcut

/-- The residue weight with an additional weight on each divisor tuple. -/
def weightedResidueWeight (P k : ℕ) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (b : DivisorTuple P k → ℝ)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∑ r : tupleRegion P k D, b r.val * tupleAmplitude r.val *
    productBasis (fun p => rawLocalBasis (root p)) (tupleAssignment r.val) t

/-- Expand the weighted residue sum as a product over tuple coordinates. -/
lemma weightedResidueWeight_eq_sum {P k : ℕ} (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (b : DivisorTuple P k → ℝ)
    (t : (p : PrimeIndex P) → Fin p.val) :
    weightedResidueWeight P k D root b t =
      ∑ r ∈ tupleRegion P k D, b r *
        ∏ i, coefficient P (r i).val *
          coordinateBasis (fun p => rawLocalBasis (root p)) (r i) i t := by
  rw [weightedResidueWeight, Finset.sum_coe_sort (tupleRegion P k D)
    (fun r => b r * tupleAmplitude r *
      productBasis (fun p => rawLocalBasis (root p)) (tupleAssignment r) t)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [productBasis_tupleAssignment _ (fun _ _ => rfl) r (Finset.mem_filter.mp hr).2.1 t,
    tupleAmplitude, Finset.prod_mul_distrib, mul_assoc]

/-- Bound the weighted second moment by the Gram factor times its diagonal mass. -/
lemma weightedResidueWeight_second_moment_le {P k : ℕ} (hP : Squarefree P)
    {D M : ℝ} (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (b : DivisorTuple P k → ℝ) :
    Finset.expect Finset.univ (fun t => weightedResidueWeight P k D root b t ^ 2) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) *
        ∑ r ∈ tupleRegion P k D, tupleMass r * b r ^ 2 := by
  classical
  have hsize (p : PrimeIndex P) : 1 < p.val :=
    (Nat.prime_of_mem_primeFactors p.property).one_lt
  have hmass :
      (∑ r : tupleRegion P k D, (b r.val * tupleNormalizedCoefficient r.val) ^ 2) =
        ∑ r ∈ tupleRegion P k D, tupleMass r * b r ^ 2 := by
    rw [← Finset.sum_attach (tupleRegion P k D) (fun r => tupleMass r * b r ^ 2)]
    apply Finset.sum_congr rfl
    intro r _
    rw [mul_pow, tupleNormalizedCoefficient_sq hP r.val
      (Finset.mem_filter.mp r.property).2.1, mul_comm]
  have hweight (t : (p : PrimeIndex P) → Fin p.val) :
      (∑ r : tupleRegion P k D, (b r.val * tupleNormalizedCoefficient r.val) *
        productBasis (fun p => localBasis (root p)) (tupleAssignment r.val) t) =
      weightedResidueWeight P k D root b t := by
    simp only [tupleNormalizedCoefficient, mul_assoc,
      assignmentNormalizer_mul_basis _ hsize, weightedResidueWeight]
  have hbound (r : tupleRegion P k D) :
      (∏ p : PrimeIndex P, localRow p.val k (tupleAssignment r.val p)) - 1 ≤
        Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) - 1 := by
    apply sub_le_sub_right _ 1
    apply assignment_row_bound_all (fun p : PrimeIndex P => p.val)
      (tupleAssignment r.val) hM (fun p => hmin p.val p.property)
    rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
    exact (Finset.mem_filter.mp r.property).2.2
  have h := indexed_product_second_moment (fun p : PrimeIndex P => p.val) hsize root hroot
    (fun r : tupleRegion P k D => tupleAssignment r.val) (tupleAssignment_injective hP D)
    (fun r => b r.val * tupleNormalizedCoefficient r.val) _ hbound
  simp only [hweight, hmass] at h
  linarith [(abs_le.mp h).2]

/-- A replaced weight is a weight on smaller tuples with coefficient-remainder factors. -/
lemma replacedResidueWeight_eq_weighted {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (i : Fin (k + 1))
    (t : (p : PrimeIndex P) → Fin p.val) :
    replacedResidueWeight P (k + 1) D root i t =
      weightedResidueWeight P k D (fun p j => root p (i.succAbove j))
        (fun r => coefficientRemainder P (tupleProduct r) D) t := by
  rw [replacedResidueWeight_split hP, weightedResidueWeight_eq_sum]

/-- Control weighted diagonal mass by tilted and zero coefficient moments. -/
lemma weighted_diagonal_le {P k : ℕ} {D a b γ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (v : DivisorTuple P k → ℝ)
    (hv : ∀ r ∈ tupleRegion P k D, v r ^ 2 ≤ a * (tupleProduct r : ℝ) ^ γ + b) :
    (∑ r ∈ tupleRegion P k D, tupleMass r * v r ^ 2) ≤
      a * coefficientMoment P γ ^ k + b * coefficientMoment P 0 ^ k := by
  classical
  calc
    _ ≤ ∑ r ∈ tupleRegion P k D,
        tupleMass r * (a * (tupleProduct r : ℝ) ^ γ + b) := by
      exact Finset.sum_le_sum fun r hr =>
        mul_le_mul_of_nonneg_left (hv r hr) (tupleMass_nonneg r)
    _ ≤ ∑ r : DivisorTuple P k,
        tupleMass r * (a * (tupleProduct r : ℝ) ^ γ + b) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro r _ _
      exact mul_nonneg (tupleMass_nonneg r)
        (add_nonneg (mul_nonneg ha (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hb)
    _ = a * (∑ r : DivisorTuple P k, tupleMass r * (tupleProduct r : ℝ) ^ γ) +
        b * (∑ r : DivisorTuple P k, tupleMass r) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by rw [sum_tupleMass_mul_rpow, sum_tupleMass]

/-- Bound the squared coefficient remainder by its tail and overlap contributions. -/
lemma coefficientRemainder_square_le {P m : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hm : m ∣ P)
    (hcut : (m : ℝ) ≤ D) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    coefficientRemainder P m D ^ 2 ≤
      (2 * C ^ 2 * D ^ (-(2 * β))) * (m : ℝ) ^ (2 * β) +
        2 * (4 * Real.log D / (M * Real.log 2)) ^ 2 := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero h.squarefree.ne_zero hm)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hD : 0 < D := hm'.trans_le hcut
  have hs := pow_le_pow_left₀ (coefficientRemainder_nonneg h.one_lt hm0 hcut)
    (coefficientRemainder_le h hβ hm hcut hM hmin) 2
  have hp : (((m : ℝ) / D) ^ β) ^ 2 = D ^ (-(2 * β)) * (m : ℝ) ^ (2 * β) := by
    rw [← Real.rpow_mul_natCast (div_nonneg hm'.le hD.le), Real.rpow_neg hD.le,
      Real.div_rpow hm'.le hD.le]
    norm_num
    rw [mul_comm β 2]
    ring
  have hsq := sq_nonneg (C * ((m : ℝ) / D) ^ β - 4 * Real.log D / (M * Real.log 2))
  nlinarith [hp]

/-- Bound a replaced weight's second moment using tilted and zero coefficient moments. -/
lemma replacedResidueWeight_second_moment_le {P k : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 0 < D)
    (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (i : Fin (k + 1)) :
    Finset.expect Finset.univ (fun t => replacedResidueWeight P (k + 1) D root i t ^ 2) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) *
        ((2 * C ^ 2 * D ^ (-(2 * β))) * coefficientMoment P (2 * β) ^ k +
          2 * (4 * Real.log D / (M * Real.log 2)) ^ 2 * coefficientMoment P 0 ^ k) := by
  classical
  simp_rw [replacedResidueWeight_eq_weighted h.squarefree]
  apply (weightedResidueWeight_second_moment_le h.squarefree hM hmin
    (fun p j => root p (i.succAbove j))
    (fun p a b hab => by simpa using hroot p hab)
    (fun r => coefficientRemainder P (tupleProduct r) D)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply weighted_diagonal_le (by positivity) (by positivity)
  intro r hr
  obtain ⟨hpair, hcut⟩ := (Finset.mem_filter.mp hr).2
  exact coefficientRemainder_square_le h hβ (tupleProduct_dvd r hpair) hcut
    (zero_lt_one.trans hM) hmin

/-- Avoiding one coordinate's roots makes the original and replaced weights equal. -/
lemma residueWeight_eq_replaced_of_uncovered {P k : ℕ} (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (i : Fin k)
    (t : (p : PrimeIndex P) → Fin p.val) (hi : ∀ p, t p ≠ root p i) :
    residueWeight P k D root t = replacedResidueWeight P k D root i t := by
  have hlocal (p : PrimeIndex P) (j : Option (Fin k)) :
      rawLocalBasis (root p) j (t p) = replacedLocalBasis (root p) i j (t p) := by
    cases j with
    | none => rfl
    | some j =>
        by_cases h : j = i <;>
          simp [rawLocalBasis, replacedLocalBasis, h, residueFactor, hi]
  simp only [residueWeight, replacedResidueWeight, basisWeight, productBasis, hlocal]

/-- Every replaced local basis value has absolute value at most one. -/
lemma abs_replacedLocalBasis_le_one {p k : ℕ} (hp : 1 < p)
    (root : Fin k → Fin p) (i : Fin k) (j : Option (Fin k)) (t : Fin p) :
    |replacedLocalBasis root i j t| ≤ 1 := by
  cases j with
  | none => simp [replacedLocalBasis]
  | some j =>
      simp only [replacedLocalBasis]
      split_ifs
      · have hp' : (2 : ℝ) ≤ p := by exact_mod_cast Nat.succ_le_of_lt hp
        rw [abs_of_nonneg (div_nonneg zero_le_one (by linarith))]
        exact (div_le_one (by linarith)).mpr (by linarith)
      · exact abs_residueFactor_le_one hp _ _

/-- The replaced weight's second-moment averaging error is at most `16 * D ^ 6 / T`. -/
lemma replacedResidueWeight_interval_error {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) (i : Fin k) :
    |integerAverage T (fun n => replacedResidueWeight P k D root i (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => replacedResidueWeight P k D root i t ^ 2)| ≤
        16 * D ^ 6 / T :=
  basisWeight_interval_error hP hT hD root hroot hcoeff (fun p => replacedLocalBasis (root p) i)
    (fun _ _ => rfl)
    (fun p j t => abs_replacedLocalBasis_le_one
      (Nat.mem_primeFactors.mp p.property).1.one_lt _ i j t)

/-- A second-moment gap yields an integer meeting a root in every coordinate. -/
lemma exists_simultaneous_root_of_moments {P k T : ℕ} {D L U : ℝ}
    (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (hlower : L ≤ integerAverage T (fun n => residueWeight P k D root (residueVector P n) ^ 2))
    (hupper : ∀ i,
      integerAverage T (fun n => replacedResidueWeight P k D root i (residueVector P n) ^ 2) ≤ U)
    (hgap : (k : ℝ) * U < L) :
    ∃ n < T, ∀ i : Fin k, ∃ p : PrimeIndex P, residueVector P n p = root p i := by
  classical
  by_contra! h
  have hpointwise (n : ℕ) (hn : n ∈ Finset.range T) :
      residueWeight P k D root (residueVector P n) ^ 2 ≤
        ∑ i, replacedResidueWeight P k D root i (residueVector P n) ^ 2 := by
    obtain ⟨i, hi⟩ := h n (Finset.mem_range.mp hn)
    rw [residueWeight_eq_replaced_of_uncovered D root i (residueVector P n) hi]
    apply Finset.single_le_sum ?_ (Finset.mem_univ i)
    intro j _
    exact sq_nonneg _
  apply (not_le_of_gt hgap)
  calc
    L ≤ integerAverage T (fun n => residueWeight P k D root (residueVector P n) ^ 2) := hlower
    _ ≤ ∑ i, integerAverage T
        (fun n => replacedResidueWeight P k D root i (residueVector P n) ^ 2) := by
      unfold integerAverage
      rw [← Finset.sum_div, Finset.sum_comm]
      exact div_le_div_of_nonneg_right (Finset.sum_le_sum hpointwise) (Nat.cast_nonneg T)
    _ ≤ ∑ _i : Fin k, U := Finset.sum_le_sum (fun i _ => hupper i)
    _ = (k : ℝ) * U := by simp

/-- Any coefficient-estimate constant is at least one. -/
lemma CoefficientEstimates.one_le_constant {P : ℕ} {β C : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) : 1 ≤ C := by
  simpa [coefficientAbsMoment_zero h.one_lt] using h.absMoment_le 0 le_rfl (by positivity)

/-- The exponential factor controlling Gram matrix row sums. -/
def gramBound (k : ℕ) (M D : ℝ) : ℝ :=
  Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M))

/-- A normalized second-moment bound for a replaced residue weight. -/
def uncoveredBound (k : ℕ) (β C M D : ℝ) : ℝ :=
  gramBound k M D * (2 * C ^ 2 * D ^ (-(2 * β)) * Real.exp ((k : ℝ) * C * (2 * β)) +
    2 * (4 * Real.log D / (M * Real.log 2)) ^ 2)

/-- The normalized uncovered bound is nonnegative. -/
lemma uncoveredBound_nonneg (k : ℕ) (β C M : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ uncoveredBound k β C M D := by unfold uncoveredBound gramBound; positivity

/-- Bound a replaced weight's second moment by `uncoveredBound` times the zero moment. -/
lemma replacedResidueWeight_normalized_bound {P k : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 0 < D)
    (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (i : Fin (k + 1)) :
    Finset.expect Finset.univ (fun t => replacedResidueWeight P (k + 1) D root i t ^ 2) ≤
      uncoveredBound k β C M D * coefficientMoment P 0 ^ k := by
  have hγ : 0 ≤ 2 * β := mul_nonneg (by norm_num) hβ
  have hmoment := coefficientMoment_pow_le h.one_lt
    (zero_le_one.trans (h.one_le_constant hβ)) hγ
    (h.moment_control (2 * β) hγ le_rfl) k
  apply (replacedResidueWeight_second_moment_le h hβ hD hM hmin root hroot i).trans
  unfold uncoveredBound gramBound
  calc
    _ ≤ Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) *
        ((2 * C ^ 2 * D ^ (-(2 * β))) *
            (coefficientMoment P 0 ^ k * Real.exp ((k : ℝ) * C * (2 * β))) +
          2 * (4 * Real.log D / (M * Real.log 2)) ^ 2 * coefficientMoment P 0 ^ k) := by
      gcongr
    _ = _ := by ring

/-- The normalized diagonal mass loses only a power tail and prime collisions. -/
lemma diagonalMass_normalized_lower {P M k : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 0 < D)
    (hM : 0 < M) (hmin : ∀ p ∈ P.primeFactors, M < p) :
    (1 - (D ^ (-β) * Real.exp ((k : ℝ) * C * β) + 16 * (k : ℝ) ^ 2 / M)) *
      coefficientMoment P 0 ^ k ≤ diagonalMass P k D := by
  have hmoment := coefficientMoment_pow_le h.one_lt
    (zero_le_one.trans (h.one_le_constant hβ)) hβ
    (h.moment_control β hβ (by linarith)) k
  have hloss := diagonalMass_tail_collision (k := k) h hM hmin hD hβ
  have htail := mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg hD.le (-β))
  nlinarith

end

end LongGapsBetweenPrimes
