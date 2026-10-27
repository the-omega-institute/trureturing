/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianActualNormBudget
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual Gaussian head/tail norms, full tail-H budget, and exact mass-zero charge. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianInfiniteJacobi

/-! Actual source norms and complete tail budgets, independent of the finite matrix certificate. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace FiniteGaussianCap475
open FiniteGaussianCap4
open FiniteGaussianCap4.LaguerreSevenHalf

/-- Norm of the actual sixteen-even-mode head. -/
theorem finiteGaussian_actual_head_norm {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * finiteGaussianPartialSum c site 32 x ^ 2) =
      ∑ k ∈ Finset.range 16, finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2 := by
  have hzero (x : ℝ) : finiteGaussianPartialSum c site 0 x = 0 := by
    simp [finiteGaussianPartialSum, gaussianPartialSum]
  simpa only [Nat.zero_add, Nat.reduceMul, hzero, sub_zero] using
    finiteGaussian_even_prefix_difference_norm c site reflection hc hs 0 16

/-- The full physical norm splits into the actual head and complete remainder.
Both sides are derived from the native finite-prefix graph norm theorem. -/
theorem finiteGaussian_actual_head_tail_norm {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * gaussianFeature c site x ^ 2) =
      (∑ k ∈ Finset.range 16, finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2) +
      (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
        (gaussianFeature c site x - finiteGaussianPartialSum c site 32 x) ^ 2) := by
  have hzero (x : ℝ) : finiteGaussianPartialSum c site 0 x = 0 := by
    simp [finiteGaussianPartialSum, gaussianPartialSum]
  have htotal : HasSum
      (fun k : ℕ => finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2)
      (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * gaussianFeature c site x ^ 2) := by
    simpa only [Nat.zero_add, Nat.reduceMul, hzero, sub_zero] using
      (finiteGaussian_actual_remainder_norm c site reflection hc hs 0).2
  have htail := (finiteGaussian_actual_remainder_norm c site reflection hc hs 16).2
  have hsplit := htotal.summable.sum_add_tsum_nat_add 16
  rw [htotal.tsum_eq] at hsplit
  have hsplit' :
      (∑ k ∈ Finset.range 16, finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2) +
        (∑' n : ℕ, finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * gaussianFeature c site x ^ 2 := by
    simpa only [Nat.add_comm] using hsplit
  rw [htail.tsum_eq] at hsplit'
  exact hsplit'.symm

/-- The complete tail-H series has exactly its original 44+3/4 norm debit. -/
theorem finiteGaussian_actual_tailH_budget {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    (∑' n : ℕ, tailH (16 + n : ℕ) *
      finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2) =
      (1 / 10 : ℝ) * (∑' n : ℕ, (2 * (16 + n : ℕ) + 9 / 4 : ℝ) ^ 2 *
        finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2) -
      (179 / 4 : ℝ) * (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
        (gaussianFeature c site x - finiteGaussianPartialSum c site 32 x) ^ 2) := by
  have hi : Function.Injective (fun n : ℕ => 16 + n) := by
    intro a b h
    change 16 + a = 16 + b at h
    omega
  have hp : Summable (fun n : ℕ => (2 * (16 + n : ℕ) + 9 / 4 : ℝ) ^ 2 *
      finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2) := by
    simpa only [Function.comp_def] using
      (finiteGaussian_actual_jacobi_summability c site).2.2.1.comp_injective hi
  have ht : HasSum
      (fun n : ℕ => finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2)
      (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
        (gaussianFeature c site x - finiteGaussianPartialSum c site 32 x) ^ 2) := by
    simpa only [Nat.reduceMul] using
      (finiteGaussian_actual_remainder_norm c site reflection hc hs 16).2
  have hsum := (hp.hasSum.mul_left (1 / 10 : ℝ)).sub (ht.mul_left (179 / 4 : ℝ))
  have htail : HasSum
      (fun n : ℕ => tailH (16 + n : ℕ) *
        finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2)
      ((1 / 10 : ℝ) * (∑' n : ℕ, (2 * (16 + n : ℕ) + 9 / 4 : ℝ) ^ 2 *
        finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2) -
      (179 / 4 : ℝ) * (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
        (gaussianFeature c site x - finiteGaussianPartialSum c site 32 x) ^ 2)) := by
    convert hsum using 1
    funext n
    unfold tailH
    ring
  exact htail.tsum_eq

/-- Zero actual central mass transfers the entire missing tail charge to
minus the head charge. Convergence comes from the actual Mellin supplier. -/
theorem finiteGaussian_actual_zero_tail_charge {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (hmass : ∑ i, c i = 0) :
    (∑' n : ℕ,
      (normalizedCentralMellin (2 * (16 + n)) / normalizedCentralMellin 0) *
        finiteGaussianNormalizedCoefficient c site (2 * (16 + n))) =
      -(∑ k ∈ Finset.range 16,
        (normalizedCentralMellin (2 * k) / normalizedCentralMellin 0) *
          finiteGaussianNormalizedCoefficient c site (2 * k)) := by
  have hzero := (finite_gaussian_central_mass_zero c site hmass).1
  have hsplit := hzero.summable.sum_add_tsum_nat_add 16
  rw [hzero.tsum_eq] at hsplit
  have hsplit' :
      (∑ k ∈ Finset.range 16,
        (normalizedCentralMellin (2 * k) / normalizedCentralMellin 0) *
          finiteGaussianNormalizedCoefficient c site (2 * k)) +
      (∑' n : ℕ,
        (normalizedCentralMellin (2 * (16 + n)) / normalizedCentralMellin 0) *
          finiteGaussianNormalizedCoefficient c site (2 * (16 + n))) = 0 := by
    simpa only [Nat.add_comm] using hsplit
  linarith

/-- The unchanged complete-tail H has a uniform lower bound on every term. -/
theorem cap475_tailH_ge_seventy (n : ℕ) : (70 : ℝ) ≤ tailH (16 + n : ℕ) := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  unfold tailH
  push_cast
  nlinarith [sq_nonneg (n : ℝ)]

/-- Actual complete tail energy dominates seventy times the actual remainder
norm. Summability and the norm identity are both supplied by the same source. -/
theorem finiteGaussian_actual_tailH_seventy_norm {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    70 * (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
      (gaussianFeature c site x - finiteGaussianPartialSum c site 32 x) ^ 2) ≤
      ∑' n : ℕ, tailH (16 + n : ℕ) *
        finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2 := by
  have hnorm := (finiteGaussian_actual_remainder_norm c site reflection hc hs 16).2
  have hleft := hnorm.mul_left (70 : ℝ)
  have hle := hleft.summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (cap475_tailH_ge_seventy n)
      (sq_nonneg (finiteGaussianNormalizedCoefficient c site (2 * (16 + n)))))
    (finiteGaussian_actual_positive_tailH c site).1
  rw [hleft.tsum_eq] at hle
  exact hle

end FiniteGaussianCap475
