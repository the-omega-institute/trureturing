/- GID: D5/S3/TotalVariation/BanicR312Settlement
   generality: I
   mirror-B: D5/B/S3/TotalVariation/BanicR312Settlement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/TotalVariation/BanicR312Settlement.claim; result=D5/S3/TotalVariation/BanicR312Settlement.result; claim=D5/S3/TotalVariation/BanicR312Settlement.claim
   digest: A fourth bin increases cyclic multinomial dispersion at four draws, refuting Remark 3.12’s conjunction. -/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S3.TotalVariation.BanicR312Settlement

open scoped BigOperators ENNReal

/-- Bin counts, bounded by the sample size; the law below enforces their total. -/
abbrev CountVector (n N : ℕ) := Fin n → Fin (N + 1)

instance countVectorMeasurableSpace (n N : ℕ) : MeasurableSpace (CountVector n N) := ⊤

/-- The source's multinomial mass, specialized to p_i = 1/n. -/
noncomputable def multinomialMass (n N : ℕ) (k : CountVector n N) : ℝ≥0∞ :=
  if (∑ i : Fin n, (k i).val) = N then
    ((N.factorial : ℝ≥0∞) / ∏ i : Fin n, ((k i).val.factorial : ℝ≥0∞)) *
      (1 / (n : ℝ≥0∞)) ^ N
  else 0

/-- The actual count-vector law, using the source's mass function. -/
noncomputable def multinomialLaw (n N : ℕ) : MeasureTheory.Measure (CountVector n N) :=
  ∑ k : CountVector n N, multinomialMass n N k • MeasureTheory.Measure.dirac k

/-- X_{n+1}=X_1 is implemented by Mathlib's cyclic permutation. -/
def cyclicVariation (n N : ℕ) (k : CountVector n N) : ℝ :=
  ∑ i : Fin n, |((k (finRotate n i)).val : ℝ) - ((k i).val : ℝ)|

/-- The source's sigma_c^2(n,N) = Var(d^c)/N. -/
noncomputable def dispersionSquared (n N : ℕ) : ℝ :=
  ProbabilityTheory.variance (cyclicVariation n N) (multinomialLaw n N) / (N : ℝ)

/-- The nonnegative dispersion sigma_c(n,N). -/
noncomputable def dispersion (n N : ℕ) : ℝ :=
  Real.sqrt (dispersionSquared n N)

/-- Remark 3.12: both global monotonicities, on the original parameter domain. -/
def claim : Prop :=
  (∀ (n N : ℕ), 3 ≤ n → 1 ≤ N → dispersion (n + 1) N ≤ dispersion n N) ∧
  (∀ (n N : ℕ), 3 ≤ n → 1 ≤ N → dispersion n N ≤ dispersion n (N + 1))

open MeasureTheory ProbabilityTheory

/-- Integer numerator of the point mass with its common factor removed. -/
private def weight (n N : ℕ) (k : CountVector n N) : ℕ :=
  if (∑ i : Fin n, (k i).val) = N then Nat.multinomial Finset.univ (fun i => (k i).val)
  else 0

private theorem mass_eq_weight (n N : ℕ) (k : CountVector n N) :
    multinomialMass n N k = (weight n N k : ℝ≥0∞) * (1 / (n : ℝ≥0∞)) ^ N := by
  by_cases h : (∑ i : Fin n, (k i).val) = N
  · simp only [multinomialMass, weight, ite_eq_left h]
    congr 1
    have hs := Nat.multinomial_spec Finset.univ (fun i : Fin n => (k i).val)
    rw [h] at hs
    have hp : ∏ i : Fin n, (((k i).val.factorial : ℕ) : ℝ≥0∞) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (Nat.factorial_ne_zero _))
    have ht : ∏ i : Fin n, (((k i).val.factorial : ℕ) : ℝ≥0∞) ≠ ∞ :=
      ENNReal.prod_ne_top (fun _ _ => ENNReal.natCast_ne_top _)
    rw [← Nat.cast_prod, ← hs, Nat.cast_mul, mul_comm, ENNReal.mul_div_cancel_right]
    · simpa only [Nat.cast_prod] using hp
    · simpa only [Nat.cast_prod] using ht
  · simp [multinomialMass, weight, h]

/-- The cyclic variation computed with natural numbers. -/
private def variationNat (n N : ℕ) (k : CountVector n N) : ℕ :=
  ∑ i : Fin n, (((k (finRotate n i)).val - (k i).val) + ((k i).val - (k (finRotate n i)).val))

private theorem variation_eq_nat (n N : ℕ) (k : CountVector n N) :
    cyclicVariation n N k = (variationNat n N k : ℝ) := by
  rw [cyclicVariation, variationNat, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  let a := (k (finRotate n i)).val
  let b := (k i).val
  change |(a : ℝ) - (b : ℝ)| = ((a - b + (b - a) : ℕ) : ℝ)
  rcases le_total b a with h | h
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

private def moment (n N power : ℕ) : ℕ :=
  ∑ k : CountVector n N, weight n N k * variationNat n N k ^ power

private theorem law_probability (n N : ℕ) (hn : n ≠ 0)
    (hm : moment n N 0 = n ^ N) : IsProbabilityMeasure (multinomialLaw n N) := by
  have hsum : ∑ k : CountVector n N, weight n N k = n ^ N := by
    simpa [moment] using hm
  constructor
  rw [multinomialLaw, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one, mass_eq_weight, ← Finset.sum_mul, ← Nat.cast_sum, hsum, Nat.cast_pow]
  rw [← mul_pow, one_div, ENNReal.mul_inv_cancel (by exact_mod_cast hn) (by simp), one_pow]

private theorem integral_moment (n N power : ℕ) (hn : n ≠ 0) :
    (∫ k, cyclicVariation n N k ^ power ∂multinomialLaw n N) =
      (moment n N power : ℝ) * (1 / (n : ℝ)) ^ N := by
  let _ : MeasurableSingletonClass (CountVector n N) := ⟨fun _ => trivial⟩
  have hfinite (k : CountVector n N) : multinomialMass n N k ≠ ∞ := by
    rw [mass_eq_weight]
    have hn' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
    exact ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by simp [hn']))
  rw [multinomialLaw, integral_finsetSum_measure (fun k _ =>
    (integrable_dirac (by simp)).smul_measure (hfinite k))]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul, mass_eq_weight,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_natCast, variation_eq_nat, moment, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem dispersionSquared_eq_moments (n N : ℕ) (hn : n ≠ 0)
    (hm : moment n N 0 = n ^ N) :
    dispersionSquared n N =
      ((moment n N 2 : ℝ) * (1 / (n : ℝ)) ^ N -
        ((moment n N 1 : ℝ) * (1 / (n : ℝ)) ^ N) ^ 2) / N := by
  let := law_probability n N hn hm
  have hmeas : Measurable (cyclicVariation n N) := measurable_from_top
  have hLp : MemLp (cyclicVariation n N) 2 (multinomialLaw n N) := by
    apply MemLp.of_bound hmeas.aestronglyMeasurable (∑ k : CountVector n N, |cyclicVariation n N k|)
    exact Filter.Eventually.of_forall (fun k => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun j => |cyclicVariation n N j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ k))
  unfold dispersionSquared
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, integral_moment n N 2 hn]
  rw [show (∫ k, cyclicVariation n N k ∂multinomialLaw n N) =
      (moment n N 1 : ℝ) * (1 / (n : ℝ)) ^ N by
    simpa only [pow_one] using integral_moment n N 1 hn]

private theorem moments_four_four :
    moment 4 4 0 = 4 ^ 4 ∧ moment 4 4 1 = 1120 ∧ moment 4 4 2 = 5888 := by
  decide +kernel

private theorem v_four_four : dispersionSquared 4 4 = (247 : ℝ) / 256 := by
  obtain ⟨h0, h1, h2⟩ := moments_four_four
  rw [dispersionSquared_eq_moments 4 4 (by decide) h0, h1, h2]
  norm_num

private theorem moments_three_four :
    moment 3 4 0 = 3 ^ 4 ∧ moment 3 4 1 = 312 ∧ moment 3 4 2 = 1488 := by
  decide +kernel

private theorem v_three_four : dispersionSquared 3 4 = (644 : ℝ) / 729 := by
  obtain ⟨h0, h1, h2⟩ := moments_three_four
  rw [dispersionSquared_eq_moments 3 4 (by decide) h0, h1, h2]
  norm_num

private theorem variance_bins_reverse : dispersionSquared 3 4 < dispersionSquared 4 4 := by
  rw [v_three_four, v_four_four]
  norm_num

private theorem dispersion_bins_reverse : dispersion 3 4 < dispersion 4 4 := by
  apply Real.sqrt_lt_sqrt _ variance_bins_reverse
  rw [v_three_four]
  norm_num

/-- The bin-count reversal refutes the conjunction in Remark 3.12. -/
theorem result : ¬ claim := by
  intro h
  exact (not_le_of_gt dispersion_bins_reverse) (h.1 3 4 (by decide) (by decide))

end D5.S3.TotalVariation.BanicR312Settlement
