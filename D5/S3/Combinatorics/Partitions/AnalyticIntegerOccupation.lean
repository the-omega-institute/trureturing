/- GID: D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/AnalyticIntegerOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed integer-frequency occupations with absolute convergence supplied by the public odd-occupation majorant. -/

import D5.S3.Combinatorics.Partitions.AnalyticOddOccupation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators

namespace D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation

open D5.S3.Combinatorics.Partitions.ColouredOddOccupation
open D5.S3.Combinatorics.Partitions.AnalyticOddOccupation

def integerEnergy (ι : Type*) (d : (ι × ℕ) →₀ ℕ) : ℕ :=
  Finsupp.weight (fun x : ι × ℕ => x.2 + 1) d

def occupationCount {ι : Type*} (d : (ι × ℕ) →₀ ℕ) : ℕ :=
  d.toMultiset.card

def signedIntegerMonomial {ι : Type*} (q : ℂ) (d : (ι × ℕ) →₀ ℕ) : ℂ :=
  (-1 : ℂ) ^ occupationCount d * q ^ integerEnergy ι d

private theorem oddWeight_le_twice (n : ℕ) :
    oddWeight n ≤ 2 * (n + 1) := by
  dsimp [oddWeight]
  omega

theorem oddEnergy_le_twice_integerEnergy (ι : Type*)
    (d : (ι × ℕ) →₀ ℕ) :
    colouredEnergy ι d ≤ 2 * integerEnergy ι d := by
  classical
  simp only [colouredEnergy, integerEnergy, Finsupp.weight_apply,
    Finsupp.sum, nsmul_eq_mul]
  change (∑ x ∈ d.support, d x * oddWeight x.2) ≤
    2 * (∑ x ∈ d.support, d x * (x.2 + 1))
  calc
    _ ≤ ∑ x ∈ d.support, d x * (2 * (x.2 + 1)) := by
      apply Finset.sum_le_sum
      intro x hx
      exact Nat.mul_le_mul_left (d x) (oddWeight_le_twice x.2)
    _ = 2 * (∑ x ∈ d.support, d x * (x.2 + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring

private theorem occupationCount_eq_occurrences_length {D : Type*}
    (d : (D × ℕ) →₀ ℕ) :
    occupationCount d = (d.toMultiset.toList).length := by
  exact (Multiset.length_toList _).symm

private theorem signed_norm (ι : Type*) (q : ℂ) (d : (ι × ℕ) →₀ ℕ) :
    ‖signedIntegerMonomial q d‖ = ‖q‖ ^ integerEnergy ι d := by
  simp [signedIntegerMonomial, occupationCount, integerEnergy]

private theorem monomial_signed (ι : Type*) (q : ℂ) (d : (ι × ℕ) →₀ ℕ) :
    AnalyticOddOccupation.monomial (fun a : ι × ℕ => -q ^ (a.2 + 1)) d =
      signedIntegerMonomial q d := by
  classical
  unfold AnalyticOddOccupation.monomial signedIntegerMonomial integerEnergy
    occupationCount
  rw [Finsupp.prod]
  have hneg : ∀ x : ι × ℕ,
      (-q ^ (x.2 + 1)) ^ d x = (-1 : ℂ) ^ d x *
        (q ^ (x.2 + 1)) ^ d x := by
    intro x
    have hx : -q ^ (x.2 + 1) = (-1 : ℂ) * q ^ (x.2 + 1) := by ring
    rw [hx, mul_pow]
  simp_rw [hneg]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [Finsupp.card_toMultiset]
  simp only [Finsupp.sum, id_eq]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  simp [Nat.mul_comm]

theorem sqrt_norm_majorant (ι : Type*) {q : ℂ} (hq : ‖q‖ < 1)
    (d : (ι × ℕ) →₀ ℕ) :
    ‖signedIntegerMonomial q d‖ ≤
      (Real.sqrt ‖q‖) ^ colouredEnergy ι d := by
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hr0 : 0 ≤ Real.sqrt ‖q‖ := Real.sqrt_nonneg _
  have hrsq : (Real.sqrt ‖q‖) ^ 2 = ‖q‖ := Real.sq_sqrt hq0
  have hr1 : Real.sqrt ‖q‖ < 1 := by
    nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg ‖q‖]
  calc
    ‖signedIntegerMonomial q d‖ = ‖q‖ ^ integerEnergy ι d := signed_norm ι q d
    _ = (Real.sqrt ‖q‖ ^ 2) ^ integerEnergy ι d := by rw [hrsq]
    _ = Real.sqrt ‖q‖ ^ (2 * integerEnergy ι d) := by rw [← pow_mul]
    _ ≤ Real.sqrt ‖q‖ ^ colouredEnergy ι d :=
      pow_le_pow_of_le_one hr0 hr1.le
        (oddEnergy_le_twice_integerEnergy ι d)

theorem summable_norm_signed_integer_occupations (ι : Type*) [Fintype ι]
    {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun d : (ι × ℕ) →₀ ℕ => ‖signedIntegerMonomial q d‖) := by
  have hr0 : 0 ≤ Real.sqrt ‖q‖ := Real.sqrt_nonneg _
  have hr1 : Real.sqrt ‖q‖ < 1 := by
    nlinarith [Real.sq_sqrt (norm_nonneg q), Real.sqrt_nonneg ‖q‖]
  refine (summable_real_odd_occupations ι hr0 hr1).of_nonneg_of_le ?_ ?_
  · intro d
    exact norm_nonneg _
  · intro d
    exact sqrt_norm_majorant ι hq d

theorem hasProd_signed_integer_occupations (ι : Type*) [Fintype ι]
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd
      (fun a : ι × ℕ => (1 - (-q ^ (a.2 + 1)))⁻¹)
      (∑' d : (ι × ℕ) →₀ ℕ,
        signedIntegerMonomial q d) := by
  let z : ι × ℕ → ℂ := fun a => -q ^ (a.2 + 1)
  have hnorm : Summable (fun d : (ι × ℕ) →₀ ℕ =>
      ‖AnalyticOddOccupation.monomial z d‖) := by
    apply (summable_norm_signed_integer_occupations ι hq).congr
    intro d
    rw [show AnalyticOddOccupation.monomial z d = signedIntegerMonomial q d by
      exact monomial_signed ι q d]
  have hz : ∀ a : ι × ℕ, ‖z a‖ < 1 := by
    intro a
    dsimp [z]
    simp only [norm_neg, Complex.norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hp := hasProd_inverse_eq_occupation_sum z hnorm hz
  have hsum : (∑' d : (ι × ℕ) →₀ ℕ,
      AnalyticOddOccupation.monomial z d) =
      ∑' d : (ι × ℕ) →₀ ℕ, signedIntegerMonomial q d :=
    tsum_congr (fun d => monomial_signed ι q d)
  rw [hsum] at hp
  simpa [z] using hp

end D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation

#print axioms D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.sqrt_norm_majorant
#print axioms D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.summable_norm_signed_integer_occupations
#print axioms D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation.hasProd_signed_integer_occupations
