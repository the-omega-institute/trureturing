/- GID: D5/S3/PrimeGaps/AssignmentStructure
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the prime-coordinate assignment structure and its second-moment identities. -/

/- Ported from openai/LongGapsBetweenPrimes commit 8f5fa88c88b4750028c05b66b081d56a92418054.
   Modified by trureturing on 2026-09-04: repository routing and module split. -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import D5.S3.PrimeGaps.GreedyResidues
import D5.S3.PrimeGaps.NormalizerBounds

namespace LongGapsBetweenPrimes

noncomputable section

/-- The tilt scale reciprocal to the logarithmic upper sieve cutoff. -/
def sieveBeta (x : ℝ) : ℝ := 1 / sieveUpperLog x

/-- A common constant controlling the coefficient moments. -/
def weightConstant : ℝ :=
  1 + absoluteMomentBound normalizerLower + coefficientControl normalizerLower

/-- The common coefficient constant exceeds one. -/
lemma weightConstant_gt_one : 1 < weightConstant := by
  unfold weightConstant
  linarith [absoluteMomentBound_pos normalizerLower_pos,
    coefficientControl_pos normalizerLower_pos]

/-- The coefficient estimates needed by the finite weighted sieve argument. -/
structure CoefficientEstimates (P : ℕ) (β C : ℝ) : Prop where
  /-- The sieve modulus exceeds one. -/
  one_lt : 1 < P
  /-- The sieve modulus is squarefree. -/
  squarefree : Squarefree P
  /-- Every divisor coefficient has absolute value at most one. -/
  abs_le_one : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1
  /-- The absolute moment is uniformly bounded for tilts up to `2 * β`. -/
  absMoment_le : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 2 * β → coefficientAbsMoment P γ ≤ C
  /-- The absolute moment is also controlled relative to the normalizer. -/
  moment_control : ∀ γ : ℝ, 0 ≤ γ → γ ≤ 2 * β →
    coefficientAbsMoment P γ ≤ C * normalizer P

/-- The sieve coefficients eventually satisfy all required uniform estimates. -/
lemma eventually_sieve_coefficient_estimates : ∀ᶠ x : ℝ in Filter.atTop,
    0 < sieveBeta x ∧ CoefficientEstimates (sieveP x) (sieveBeta x) weightConstant := by
  have hunit := (Filter.Tendsto.const_mul_atTop normalizerLower_pos tendsto_log_sieveZ).eventually
    (Filter.eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_sieve_normalizer_lower,
    tendsto_sieveZ.eventually (Filter.eventually_ge_atTop 2),
    tendsto_log_sieveZ.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ)), hunit]
    with x hB hZ hlogZ hx hlx hunit'
  obtain ⟨hZY, hB⟩ := hB
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := by linarith
  have hupper : 0 < sieveUpperLog x := div_pos hx0 (pow_pos hlx0 5)
  have hP : 1 < sieveP x := by
    have hp0 : 0 < sieveP x := auxiliaryProduct_pos _ _
    by_contra h
    have he : sieveP x = 1 := by omega
    have hb0 : normalizer (sieveP x) = 0 := by simp [he, normalizer]
    rw [hb0] at hB
    exact (not_le_of_gt normalizerLower_pos) hB
  have hY : 2 ≤ sieveY x := hZ.trans hZY
  have hY0 : (0 : ℝ) < sieveY x := by exact_mod_cast (by omega : 0 < sieveY x)
  have hYlog : Real.log (sieveY x : ℝ) ≤ sieveUpperLog x := by
    have h := Real.log_le_log hY0 (Nat.floor_le (Real.exp_pos (sieveUpperLog x)).le)
    simpa only [Real.log_exp] using h
  have hscale (γ : ℝ) (hγ : 0 ≤ γ) (hγβ : γ ≤ 2 * sieveBeta x) :
      γ * Real.log (sieveY x : ℝ) ≤ 2 := by
    calc
      _ ≤ γ * sieveUpperLog x := mul_le_mul_of_nonneg_left hYlog hγ
      _ ≤ (2 * sieveBeta x) * sieveUpperLog x := mul_le_mul_of_nonneg_right hγβ hupper.le
      _ = 2 := by unfold sieveBeta; field_simp
  have hC1 : absoluteMomentBound normalizerLower ≤ weightConstant := by
    unfold weightConstant
    have h := coefficientControl_pos normalizerLower_pos
    linarith
  have hC2 : coefficientControl normalizerLower ≤ weightConstant := by
    unfold weightConstant
    have h := absoluteMomentBound_pos normalizerLower_pos
    linarith
  refine ⟨one_div_pos.mpr hupper, ⟨hP, auxiliaryProduct_squarefree _ _, ?_, ?_, ?_⟩⟩
  · intro d hd
    exact auxiliary_coefficient_le_one hP (by omega : 1 < sieveZ x)
      (hunit'.trans (mul_le_mul_of_nonneg_right hB (by linarith : 0 ≤ Real.log (sieveZ x : ℝ)))) hd
  · intro γ hγ hγβ
    exact (auxiliary_coefficientAbsMoment_le hZY hZ hlogZ hP normalizerLower_pos hB hγ
      (hscale γ hγ hγβ)).trans hC1
  · intro γ hγ hγβ
    exact (auxiliary_coefficientAbsMoment_control hZY hZ hlogZ hP normalizerLower_pos hB hγ
      (hscale γ hγ hγβ)).trans (mul_le_mul_of_nonneg_right hC2 (normalizer_pos hP).le)

/-- Squared coefficient mass normalized to a probability on divisors. -/
def divisorProbability (P : ℕ) (d : DivisorIndex P) : ℝ :=
  (coefficient P d.val ^ 2 / d.val.totient) / coefficientMoment P 0

/-- The normalized divisor mass is nonnegative. -/
lemma divisorProbability_nonneg {P : ℕ} (hP : P ≠ 0) (d : DivisorIndex P) :
    0 ≤ divisorProbability P d := by
  exact div_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    (zero_le_one.trans (coefficientMoment_ge_one hP 0))

/-- The normalized divisor masses sum to one. -/
lemma sum_divisorProbability {P : ℕ} (hP : P ≠ 0) :
    (∑ d : DivisorIndex P, divisorProbability P d) = 1 := by
  unfold divisorProbability
  rw [← Finset.sum_div,
    sum_divisorIndex P (fun d => coefficient P d ^ 2 / (d.totient : ℝ)),
    ← coefficientMoment_zero]
  exact div_self (ne_of_gt (zero_lt_one.trans_le (coefficientMoment_ge_one hP 0)))

/-- Tuple mass is a fixed scale times the product of the divisor probabilities. -/
lemma tupleMass_eq_probability {P k : ℕ} (hP : P ≠ 0) (r : DivisorTuple P k) :
    tupleMass r = coefficientMoment P 0 ^ k * ∏ i, divisorProbability P (r i) := by
  have hA : coefficientMoment P 0 ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (coefficientMoment_ge_one hP 0))
  rw [mul_comm, ← div_eq_iff (pow_ne_zero k hA)]
  simp [tupleMass, divisorProbability, Finset.prod_div_distrib]

/-- A prime divides a random divisor with probability at most `4 / p`. -/
lemma divisorProbability_prime_incidence {P p : ℕ} {β C : ℝ}
    (h : CoefficientEstimates P β C) (hp : p.Prime) (hpP : p ∣ P) :
    (∑ d : DivisorIndex P, divisorProbability P d * if p ∣ d.val then 1 else 0) ≤ 4 / (p : ℝ) := by
  classical
  have hP : P ≠ 0 := h.squarefree.ne_zero
  have hA : 1 ≤ coefficientMoment P 0 := coefficientMoment_ge_one hP 0
  simp only [divisorProbability]
  rw [sum_divisorIndex P (fun d =>
    (coefficient P d ^ 2 / d.totient) / coefficientMoment P 0 *
      if p ∣ d then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  calc
    _ ≤ ∑ d ∈ P.divisors.filter (fun d => p ∣ d),
        |coefficient P d| / d.totient := by
      apply Finset.sum_le_sum
      intro d hd
      have hc := h.abs_le_one d (Finset.mem_filter.mp hd).1
      have hs : coefficient P d ^ 2 ≤ |coefficient P d| := by
        nlinarith [sq_abs (coefficient P d), abs_nonneg (coefficient P d)]
      exact (div_le_self
        (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hA).trans
        (div_le_div_of_nonneg_right hs (Nat.cast_nonneg _))
    _ ≤ 4 / (p : ℝ) := coefficient_prime_incidence h.one_lt h.squarefree hp hpP
      (h.abs_le_one p (Nat.mem_divisors.mpr ⟨hpP, hP⟩))

/-- Failure of pairwise coprimality is witnessed by a shared prime factor. -/
lemma noncoprime_pair_iff_common_prime {P k : ℕ} (hP : P ≠ 0) (r : DivisorTuple P k) :
    (¬∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) ↔
      ∃ p : P.primeFactors, ∃ i j, i ≠ j ∧ p.val ∣ (r i).val ∧ p.val ∣ (r j).val := by
  classical
  simp only [not_forall, Nat.Prime.not_coprime_iff_dvd]
  constructor
  · rintro ⟨i, j, hij, p, hp, hpi, hpj⟩
    exact ⟨⟨p, hp.mem_primeFactors (hpi.trans (Nat.dvd_of_mem_divisors (r i).property)) hP⟩,
      i, j, hij, hpi, hpj⟩
  · rintro ⟨p, i, j, hij, hpi, hpj⟩
    exact ⟨i, j, hij, p, Nat.prime_of_mem_primeFactors p.property, hpi, hpj⟩

/-- The discarded mass from tuples sharing a prime, with an explicit constant. -/
theorem diagonal_collision_le {P M k : ℕ} {β C : ℝ}
    (h : CoefficientEstimates P β C) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M < p) :
    (∑ r : DivisorTuple P k, tupleMass r *
      if ¬∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val then 1 else 0) ≤
        (16 * (k : ℝ) ^ 2 / M) * coefficientMoment P 0 ^ k := by
  classical
  have hP : P ≠ 0 := h.squarefree.ne_zero
  have hA : 0 ≤ coefficientMoment P 0 ^ k :=
    pow_nonneg (zero_le_one.trans (coefficientMoment_ge_one hP 0)) k
  have hcollision := product_collision_bound (divisorProbability P)
    (divisorProbability_nonneg hP) (sum_divisorProbability hP)
    (fun (p : P.primeFactors) (d : DivisorIndex P) => p.val ∣ d.val) k
  have hincidence :
      (∑ p : P.primeFactors,
        (∑ d : DivisorIndex P, divisorProbability P d *
          if p.val ∣ d.val then 1 else 0) ^ 2) ≤ 16 / (M : ℝ) := by
    calc
      _ ≤ ∑ p : P.primeFactors, (4 / (p.val : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro p _
        have hnonneg : 0 ≤ ∑ d : DivisorIndex P, divisorProbability P d *
            if p.val ∣ d.val then 1 else 0 := by
          apply Finset.sum_nonneg
          intro d _
          exact mul_nonneg (divisorProbability_nonneg hP d) (by split_ifs <;> norm_num)
        exact pow_le_pow_left₀ hnonneg
          (divisorProbability_prime_incidence h
            (Nat.prime_of_mem_primeFactors p.property)
            (Nat.dvd_of_mem_primeFactors p.property)) 2
      _ = 16 * ∑ p ∈ P.primeFactors, 1 / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        change (∑ p ∈ P.primeFactors.attach, (4 / (p.val : ℝ)) ^ 2) = _
        rw [Finset.sum_attach P.primeFactors (fun p : ℕ => (4 / (p : ℝ)) ^ 2)]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ 16 * (1 / (M : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc
          _ ≤ ∑ p ∈ Finset.Ioc M (max M P), 1 / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (fun p hp => Finset.mem_Ioc.mpr ⟨hmin p hp,
                (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) (Nat.dvd_of_mem_primeFactors hp)).trans
                  (le_max_right _ _)⟩) (fun _ _ _ => by positivity)
          _ ≤ 1 / (M : ℝ) - 1 / ((max M P : ℕ) : ℝ) := by
            simpa only [one_div] using
              (sum_Ioc_inv_sq_le_sub (α := ℝ) hM.ne' (le_max_left M P))
          _ ≤ _ := sub_le_self _ (by positivity)
      _ = 16 / (M : ℝ) := by ring
  calc
    _ = coefficientMoment P 0 ^ k *
        ∑ r : DivisorTuple P k, (∏ i, divisorProbability P (r i)) *
          if ∃ p : P.primeFactors, ∃ i j,
            i ≠ j ∧ p.val ∣ (r i).val ∧ p.val ∣ (r j).val then 1 else 0 := by
      simp_rw [tupleMass_eq_probability hP, noncoprime_pair_iff_common_prime hP,
        mul_assoc]
      rw [Finset.mul_sum]
    _ ≤ coefficientMoment P 0 ^ k * ((k : ℝ) ^ 2 * (16 / (M : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact hcollision.trans (mul_le_mul_of_nonneg_left hincidence (sq_nonneg _))
    _ = _ := by ring

/-- The total diagonal mass over the truncated tuple region. -/
def diagonalMass (P k : ℕ) (D : ℝ) : ℝ := ∑ r ∈ tupleRegion P k D, tupleMass r

/-- The total diagonal mass is nonnegative. -/
lemma diagonalMass_nonneg (P k : ℕ) (D : ℝ) : 0 ≤ diagonalMass P k D :=
  Finset.sum_nonneg (fun r _ => tupleMass_nonneg r)

/-- The only losses in the diagonal are the product cutoff and shared primes. -/
theorem diagonalMass_tail_collision {P M k : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M < p) (hD : 0 < D) (hβ : 0 ≤ β) :
    coefficientMoment P 0 ^ k - diagonalMass P k D ≤
      D ^ (-β) * coefficientMoment P β ^ k +
        (16 * (k : ℝ) ^ 2 / M) * coefficientMoment P 0 ^ k := by
  classical
  calc
    _ ≤ (∑ r ∈ (Finset.univ : Finset (DivisorTuple P k)).filter
          (fun r => D < (tupleProduct r : ℝ)), tupleMass r) +
        ∑ r : DivisorTuple P k, tupleMass r *
          if ¬∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val then 1 else 0 := by
      rw [← sum_tupleMass, diagonalMass, tupleRegion]
      simp only [Finset.sum_filter]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro r _
      have hmass := tupleMass_nonneg r
      split_ifs <;> grind
    _ ≤ _ := add_le_add (diagonal_tail_le P k hD hβ) (diagonal_collision_le h hM hmin)

/-- Injective indexing bounds the row sum away from the diagonal by the full sum minus one. -/
lemma indexed_offdiag_sum_le {ι Λ : Type*} [Fintype ι] [Fintype Λ]
    [DecidableEq ι] (σ : ι → Λ) (hσ : Function.Injective σ)
    (K : Λ → Λ → ℝ) (hdiag : ∀ j, K j j = 1) (i : ι) :
    (∑ j : ι, if j = i then 0 else |K (σ i) (σ j)|) ≤
      (∑ τ : Λ, |K (σ i) τ|) - 1 := by
  classical
  rw [le_sub_iff_add_le]
  calc
    _ = ∑ j : ι, |K (σ i) (σ j)| := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp [hdiag, Finset.sum_ite, Finset.filter_ne']
    _ = ∑ τ ∈ Finset.univ.image σ, |K (σ i) τ| := by
      rw [Finset.sum_image hσ.injOn]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun τ _ _ => abs_nonneg (K (σ i) τ))

/-- Row bounds control the second moment of an indexed sum of product basis functions. -/
lemma indexed_product_second_moment {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ}
    (root : (p : α) → Fin k → Fin (size p)) (hroot : ∀ p, Function.Injective (root p))
    (σ : ι → α → Option (Fin k)) (hσ : Function.Injective σ) (c : ι → ℝ) (ε : ℝ)
    (hbound : ∀ i, (∏ p, localRow (size p) k (σ i p)) - 1 ≤ ε) :
    |Finset.expect Finset.univ (fun t =>
        (∑ i, c i * productBasis (fun p => localBasis (root p)) (σ i) t) ^ 2) -
      ∑ i, c i ^ 2| ≤ ε * ∑ i, c i ^ 2 := by
  classical
  have hmoment : Finset.expect Finset.univ (fun t =>
      (∑ i, c i * productBasis (fun p => localBasis (root p)) (σ i) t) ^ 2) =
      ∑ i, ∑ j, c i * c j * productKernel size (σ i) (σ j) := by
    simp_rw [pow_two, Finset.sum_mul_sum]
    simp_rw [Finset.expect_sum_comm]
    simp_rw [mul_mul_mul_comm (c _) _ (c _) _, ← Finset.mul_expect,
      average_productBasis_localBasis size hsize root hroot]
  rw [hmoment]
  apply quadratic_form_near_diagonal c (fun i j => productKernel size (σ i) (σ j)) ε
    (fun i j => productKernel_symm size (σ i) (σ j))
    (fun i => productKernel_diag size (σ i))
  intro i
  exact (indexed_offdiag_sum_le σ hσ (productKernel size)
    (productKernel_diag size) i).trans (by simpa [sum_abs_productKernel size hsize] using hbound i)

/-- Prime divisors of `P` regarded as a finite index type. -/
abbrev PrimeIndex (P : ℕ) := {p : ℕ // p ∈ P.primeFactors}

/-- Assign each used prime to a tuple coordinate containing it. -/
def tupleAssignment {P k : ℕ} (r : DivisorTuple P k) : PrimeIndex P → Option (Fin k) := by
  classical
  exact fun p => if h : ∃ i, p.val ∣ (r i).val then some (Classical.choose h) else none

/-- A prime divides at most one coordinate of a pairwise coprime tuple. -/
lemma prime_coordinate_unique {P k p : ℕ} (hp : p.Prime) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    {i j : Fin k} (hi : p ∣ (r i).val) (hj : p ∣ (r j).val) : i = j := by
  by_contra hij
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hi, hj⟩) (hpair i j hij)

/-- In a pairwise coprime tuple, a prime is assigned exactly to the coordinate it divides. -/
lemma tupleAssignment_eq_some {P k : ℕ} (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (p : PrimeIndex P) (i : Fin k) : tupleAssignment r p = some i ↔ p.val ∣ (r i).val := by
  classical
  unfold tupleAssignment
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact Classical.choose_spec h
    · exact prime_coordinate_unique (Nat.prime_of_mem_primeFactors p.property) r hpair
        (Classical.choose_spec h)
  · simp only [false_iff]
    exact fun hi => h ⟨i, hi⟩

/-- A truncated tuple is determined by its prime assignment when `P` is squarefree. -/
lemma tupleAssignment_injective {P k : ℕ} (hP : Squarefree P) (D : ℝ) :
    Function.Injective (fun r : tupleRegion P k D => tupleAssignment r.val) := by
  classical
  intro r s hrs
  dsimp only at hrs
  apply Subtype.ext
  funext i
  apply Subtype.ext
  apply (Nat.Squarefree.ext_iff
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors (r.val i).property))
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors (s.val i).property))).mpr
  intro p hp
  by_cases hpP : p ∣ P
  · let p' : PrimeIndex P := ⟨p, hp.mem_primeFactors hpP hP.ne_zero⟩
    rw [← tupleAssignment_eq_some r.val (Finset.mem_filter.mp r.property).2.1 p' i,
      ← tupleAssignment_eq_some s.val (Finset.mem_filter.mp s.property).2.1 p' i, hrs]
  · constructor <;> intro h
    · exact (hpP (h.trans (Nat.dvd_of_mem_divisors (r.val i).property))).elim
    · exact (hpP (h.trans (Nat.dvd_of_mem_divisors (s.val i).property))).elim

/-- Regroup a product over assigned primes by tuple coordinates. -/
lemma tupleAssignment_prod {P k : ℕ} {M : Type*} [CommMonoid M]
    (r : DivisorTuple P k) (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val)
    (f : PrimeIndex P → Fin k → M) :
    (∏ p : PrimeIndex P, match tupleAssignment r p with | none => 1 | some i => f p i) =
      ∏ i, ∏ p : PrimeIndex P, if p.val ∣ (r i).val then f p i else 1 := by
  classical
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p _
  simp_rw [← tupleAssignment_eq_some r hpair p]
  cases tupleAssignment r p <;> simp

/-- Restrict a product over primes dividing `P` to those dividing `d`. -/
lemma prod_primeIndex_dvd {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P)
    {M : Type*} [CommMonoid M] (f : ℕ → M) :
    (∏ p : PrimeIndex P, if p.val ∣ d then f p.val else 1) = ∏ p ∈ d.primeFactors, f p := by
  classical
  have h := Finset.prod_attach P.primeFactors (fun p => if p ∣ d then f p else 1)
  simp only [Finset.attach_eq_univ] at h
  rw [h, ← Finset.prod_filter, Nat.primeFactors_filter_dvd_of_dvd hP hd]

/-- The product of pairwise coprime divisors of `P` divides `P`. -/
lemma tupleProduct_dvd {P k : ℕ} (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) : tupleProduct r ∣ P := by
  exact Fintype.prod_dvd_of_isRelPrime
    (fun i j hij => Nat.coprime_iff_isRelPrime.mp (hpair i j hij))
    (fun i => Nat.dvd_of_mem_divisors (r i).property)

/-- A prime is assigned precisely when it divides the tuple product. -/
lemma tupleAssignment_isSome {P k : ℕ} (r : DivisorTuple P k) (p : PrimeIndex P) :
    (tupleAssignment r p).isSome ↔ p.val ∣ tupleProduct r := by
  classical
  simp [tupleAssignment, tupleProduct,
    (Nat.prime_of_mem_primeFactors p.property).prime.dvd_finsetProd_iff]

/-- The product of assigned primes equals the tuple product for squarefree `P`. -/
lemma assignmentProduct_tupleAssignment {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    assignmentProduct (fun p : PrimeIndex P => p.val) (tupleAssignment r) = tupleProduct r := by
  classical
  unfold assignmentProduct assignmentSupport
  simp_rw [Finset.prod_filter, tupleAssignment_isSome]
  rw [prod_primeIndex_dvd hP.ne_zero (tupleProduct_dvd r hpair) (fun p => p),
    Nat.prod_primeFactors_of_squarefree
      (hP.squarefree_of_dvd (tupleProduct_dvd r hpair))]

/-- The constant function and unnormalized residue factors. -/
def rawLocalBasis {p k : ℕ} (root : Fin k → Fin p) (i : Option (Fin k)) (t : Fin p) : ℝ :=
  match i with
  | none => 1
  | some j => residueFactor (root j) t

/-- The factor converting normalized product basis functions to unnormalized ones. -/
def assignmentNormalizer {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : ℝ :=
  ∏ p, match σ p with | none => 1 | some _ => (Real.sqrt ((size p : ℝ) - 1))⁻¹

/-- The product of local variances on an assignment's support. -/
def assignmentVariance {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : ℝ :=
  ∏ p, match σ p with | none => 1 | some _ => 1 / ((size p : ℝ) - 1)

/-- The square of the assignment normalizer equals the assignment variance. -/
lemma assignmentNormalizer_sq {α : Type*} [Fintype α] (size : α → ℕ)
    (hsize : ∀ p, 1 < size p) {k : ℕ} (σ : α → Option (Fin k)) :
    assignmentNormalizer size σ ^ 2 = assignmentVariance size σ := by
  unfold assignmentNormalizer assignmentVariance
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  have hp : (1 : ℝ) ≤ size p := by exact_mod_cast (hsize p).le
  cases σ p <;> simp [inv_pow, Real.sq_sqrt (sub_nonneg.mpr hp), one_div]

/-- Multiplying by the assignment normalizer removes the local basis normalization. -/
lemma assignmentNormalizer_mul_basis {α : Type*} [Fintype α] (size : α → ℕ)
    (hsize : ∀ p, 1 < size p) {k : ℕ} (root : (p : α) → Fin k → Fin (size p))
    (σ : α → Option (Fin k)) (t : (p : α) → Fin (size p)) :
    assignmentNormalizer size σ * productBasis (fun p => localBasis (root p)) σ t =
      productBasis (fun p => rawLocalBasis (root p)) σ t := by
  unfold assignmentNormalizer productBasis
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  have hp : Real.sqrt ((size p : ℝ) - 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr (by exact_mod_cast hsize p)))
  cases σ p <;> simp [localBasis, rawLocalBasis, hp]

/-- For squarefree `d`, the product of `1 / (p - 1)` equals `1 / φ(d)`. -/
lemma prod_primeFactors_inv_sub_one {d : ℕ} (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1)) = 1 / (d.totient : ℝ) := by
  rw [Finset.prod_div_distrib, Finset.prod_const_one,
    totient_eq_prod_sub_one_of_squarefree hd, Nat.cast_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]

/-- A tuple's assignment variance is the product of its reciprocal totients. -/
lemma assignmentVariance_tuple {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    assignmentVariance (fun p : PrimeIndex P => p.val) (tupleAssignment r) =
      ∏ i, 1 / ((r i).val.totient : ℝ) := by
  rw [assignmentVariance, tupleAssignment_prod r hpair (fun p _ => 1 / ((p.val : ℝ) - 1))]
  apply Finset.prod_congr rfl
  intro i _
  have hd := (Nat.mem_divisors.mp (r i).property).1
  have hsq : Squarefree (r i).val := fun q hq => hP q (hq.trans hd)
  rw [prod_primeIndex_dvd hP.ne_zero hd (fun p : ℕ => 1 / ((p : ℝ) - 1)),
    prod_primeFactors_inv_sub_one hsq]

/-- The product of coefficients attached to a divisor tuple. -/
def tupleAmplitude {P k : ℕ} (r : DivisorTuple P k) : ℝ := ∏ i, coefficient P (r i).val

/-- The tuple amplitude rescaled for expansion in the normalized basis. -/
def tupleNormalizedCoefficient {P k : ℕ} (r : DivisorTuple P k) : ℝ :=
  tupleAmplitude r * assignmentNormalizer (fun p : PrimeIndex P => p.val) (tupleAssignment r)

/-- A normalized tuple coefficient has square equal to its diagonal mass. -/
lemma tupleNormalizedCoefficient_sq {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    tupleNormalizedCoefficient r ^ 2 = tupleMass r := by
  rw [tupleNormalizedCoefficient, mul_pow,
    assignmentNormalizer_sq _ (fun p => (Nat.prime_of_mem_primeFactors p.property).one_lt),
    assignmentVariance_tuple hP r hpair]
  simp only [tupleAmplitude, tupleMass, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, mul_one_div]

/-- The truncated divisor sum weighted by coefficients and local residue factors. -/
def residueWeight (P k : ℕ) (D : ℝ) (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (t : (p : PrimeIndex P) → Fin p.val) : ℝ :=
  ∑ r : tupleRegion P k D,
    tupleAmplitude r.val * productBasis (fun p => rawLocalBasis (root p)) (tupleAssignment r.val) t

/-- The tuple weight has the diagonal second moment claimed in (3.9). -/
theorem residueWeight_second_moment {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (ε : ℝ) (hbound : ∀ r : tupleRegion P k D,
      (∏ p : PrimeIndex P, localRow p.val k (tupleAssignment r.val p)) - 1 ≤ ε) :
    |Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2) - diagonalMass P k D| ≤
      ε * diagonalMass P k D := by
  classical
  have hsize (p : PrimeIndex P) : 1 < p.val :=
    (Nat.prime_of_mem_primeFactors p.property).one_lt
  have hmass : (∑ r : tupleRegion P k D, tupleNormalizedCoefficient r.val ^ 2) =
      diagonalMass P k D := by
    rw [diagonalMass, ← Finset.sum_attach (tupleRegion P k D) tupleMass]
    apply Finset.sum_congr rfl
    intro r _
    exact tupleNormalizedCoefficient_sq hP r.val (Finset.mem_filter.mp r.property).2.1
  have hweight (t : (p : PrimeIndex P) → Fin p.val) :
      (∑ r : tupleRegion P k D, tupleNormalizedCoefficient r.val *
        productBasis (fun p => localBasis (root p)) (tupleAssignment r.val) t) =
      residueWeight P k D root t := by
    simp only [tupleNormalizedCoefficient, mul_assoc,
      assignmentNormalizer_mul_basis _ hsize, residueWeight]
  simpa only [hweight, hmass] using
    indexed_product_second_moment (fun p : PrimeIndex P => p.val) hsize root hroot
      (fun r : tupleRegion P k D => tupleAssignment r.val) (tupleAssignment_injective hP D)
      (fun r => tupleNormalizedCoefficient r.val) ε hbound

/-- An explicit exponential bound for the second moment's deviation from the diagonal mass. -/
lemma residueWeight_second_moment_bound {P k : ℕ} (hP : Squarefree P) (hk : 1 ≤ k)
    {M D : ℝ} (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p)) :
    |Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2) - diagonalMass P k D| ≤
      (Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) - 1) * diagonalMass P k D := by
  apply residueWeight_second_moment hP D root hroot
  intro r
  apply sub_le_sub_right _ 1
  apply assignment_row_bound (fun p : PrimeIndex P => p.val) hk (tupleAssignment r.val) hM
    (fun p => hmin p.val p.property)
  rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
  exact (Finset.mem_filter.mp r.property).2.2

end

end LongGapsBetweenPrimes
