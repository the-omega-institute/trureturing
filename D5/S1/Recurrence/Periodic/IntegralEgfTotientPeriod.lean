/- GID: D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/IntegralEgfTotientPeriod
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The integral e.g.f. bridge proves Bala's general and A305550 totient periods. -/

import D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Topology.Instances.Rat

/-!
# Totient periods for integral exponential substitutions

For every integral power series G, the factorial-scaled coefficients of
G(exp(X) - 1) are the factorial-weighted Stirling transform of its coefficients.
This proves the broader conjecture in `Library/ArithSums/bala2022egfgeneral.md`.
The same broader sentence on A305550 and A004123 is one conjecture, settled once.

For A305550, Q counts Mathlib's distinct-part partitions. Its ordinary generating
product is imported from Mathlib, and continuity of substitution gives exactly
Product_{j>=1} (1 + (exp(X) - 1)^j). The e.g.f. identity is proved for the integer
sequence defined below, as required by `Library/ArithSums/bala2022a305550.md`.
Neither the onset n >= m nor the period phi(m) is asserted to be minimal.

Freeze prerequisite: D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod
(and its transitive StirlingPowerFactorialPrimePeriod prerequisite).
The periodicity theorem and Stirling inclusion-exclusion identity are reused.
The new coefficient argument expands powers of exp(X)-1, truncates substitution
in each degree using X-power divisibility, and cancels the factorial denominator.
-/

open PowerSeries Finset
open D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod
open scoped PowerSeries.WithPiTopology

namespace D5.S1.Recurrence.Periodic.IntegralEgfTotientPeriod

private theorem exp_shift_power (n k : ℕ) :
    (n.factorial : ℚ) * coeff n ((exp ℚ - 1) ^ k) =
      (k.factorial : ℚ) * (Nat.stirlingSecond n k : ℚ) := by
  have he : (exp ℚ - 1) ^ k = ∑ j ∈ range (k + 1),
      C ((-1 : ℚ) ^ (k - j) * (k.choose j : ℚ)) * (exp ℚ) ^ j := by
    rw [sub_eq_add_neg, add_pow]
    apply sum_congr rfl
    intro j hj
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [he, map_sum, mul_sum]
  have hi := congrArg (Int.castRingHom ℚ)
    (D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion n k)
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at hi
  rw [hi]
  apply sum_congr rfl
  intro j hj
  rw [coeff_C_mul, exp_pow_eq_rescale_exp, coeff_rescale, coeff_exp]
  change (n.factorial : ℚ) * ((-1) ^ (k - j) * (k.choose j : ℚ) *
    ((j : ℚ) ^ n * (1 / (n.factorial : ℚ)))) = _
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

private theorem exp_shift_zero : constantCoeff (exp ℚ - 1) = 0 := by simp

private theorem coeff_shift_subst (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (f.subst (exp ℚ - 1)) =
      ∑ k ∈ range (n + 1), coeff k f * coeff n ((exp ℚ - 1) ^ k) := by
  rw [coeff_subst' (.of_constantCoeff_zero exp_shift_zero)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  by_contra h
  have hnk : n < k := by
    have h' : ¬ k < n + 1 := by simpa only [Finset.mem_coe, mem_range] using h
    omega
  have hz : coeff n ((exp ℚ - 1) ^ k) = 0 :=
    X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr exp_shift_zero) k) n hnk
  exact hk (by simp [hz])

/-- If G has integral coefficient function g, then
n! [X^n] G(exp(X)-1) = T(g,n) = sum_{k<=n} g(k) k! S(n,k).
This equality in the rationals also proves integrality of every scaled coefficient. -/
theorem egf_shift_eq_stirling_transform (g : ℕ → ℤ) (n : ℕ) :
    (n.factorial : ℚ) * coeff n ((mk (fun k => (g k : ℚ))).subst (exp ℚ - 1)) =
      (T g n : ℚ) := by
  rw [coeff_shift_subst]
  simp only [coeff_mk, mul_sum, T, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply sum_congr rfl
  intro k hk
  rw [← mul_assoc, mul_comm (n.factorial : ℚ), mul_assoc, exp_shift_power]
  ring

/-- The integer count of partitions into distinct positive parts (A000009). -/
noncomputable def Q (n : ℕ) : ℤ := (Nat.Partition.distincts n).card

/-- The ordinary distinct-parts generating product, in coefficientwise topology. -/
theorem distinct_parts_generating_identity :
    HasProd (fun j : ℕ => (1 : PowerSeries ℚ) + X ^ (j + 1))
      (mk (fun k => (Q k : ℚ))) := by
  simpa [Q, sum_range_succ, Nat.Partition.countRestricted_two] using
    Nat.Partition.hasProd_powerSeriesMk_card_countRestricted ℚ (m := 2) (by omega)

/-- The integer sequence of the e.g.f. G(exp(X)-1), where G has coefficients g.
The rational numerator is used to extract an integer; the bridge proves the
scaled coefficient is integral, so this extraction loses no information. -/
noncomputable def egfCoefficient (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ((n.factorial : ℚ) * coeff n ((mk (fun k => (g k : ℚ))).subst (exp ℚ - 1))).num

private theorem egfCoefficient_eq (g : ℕ → ℤ) (n : ℕ) : egfCoefficient g n = T g n := by
  simp only [egfCoefficient, egf_shift_eq_stirling_transform, Rat.num_intCast]

/-- OEIS A305550, in its offset-zero indexing. -/
noncomputable def a (n : ℕ) : ℤ := egfCoefficient Q n

private theorem continuous_shift_subst :
    Continuous (fun f : PowerSeries ℚ => f.subst (exp ℚ - 1)) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp only [coeff_shift_subst]
  exact (continuous_finsetSum _ (fun k hk =>
    (WithPiTopology.continuous_coeff ℚ k).mul continuous_const)).tendsto f

private theorem egf_product :
    HasProd (fun j : ℕ => (1 : PowerSeries ℚ) + (exp ℚ - 1) ^ (j + 1))
      ((mk (fun k => (Q k : ℚ))).subst (exp ℚ - 1)) := by
  have h := distinct_parts_generating_identity.map
    (substAlgHom (R := ℚ) (.of_constantCoeff_zero exp_shift_zero))
    (by simpa only [coe_substAlgHom] using continuous_shift_subst)
  simp only [Function.comp_def, map_add, map_one, map_pow, substAlgHom_X] at h
  simpa only [coe_substAlgHom] using h

/-- The sequence a really has the defining product e.g.f. of OEIS A305550. -/
theorem generating_equation :
    mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
      ∏' j : ℕ, ((1 : PowerSeries ℚ) + (exp ℚ - 1) ^ (j + 1)) := by
  rw [egf_product.tprod_eq]
  ext n
  rw [coeff_mk, a, egfCoefficient_eq, ← egf_shift_eq_stirling_transform]
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- Bala's broader conjecture: every e.g.f. G(exp(X)-1) with integral G has
period phi(m) modulo m from n >= m. The formal object is its integer coefficient
sequence egfCoefficient g, identified with n ↦ T g n by the bridge lemma
`egf_shift_eq_stirling_transform` and numerator extraction. -/
theorem bala_conjecture_egf_general (g : ℕ → ℤ) (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (egfCoefficient g (n + Nat.totient m) : ZMod m) = (egfCoefficient g n : ZMod m) := by
  simp only [egfCoefficient_eq]
  exact stirling_transform_totient_period g m n hm hn

/-- Bala's A305550 conjecture for the sequence with e.g.f. proved in
generating_equation, with onset n >= m for every positive modulus. -/
theorem bala_conjecture_a305550 (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    (a (n + Nat.totient m) : ZMod m) = (a n : ZMod m) := by
  exact bala_conjecture_egf_general Q m n hm hn

#print axioms egf_shift_eq_stirling_transform
#print axioms Q
#print axioms distinct_parts_generating_identity
#print axioms egfCoefficient
#print axioms a
#print axioms generating_equation
#print axioms bala_conjecture_egf_general
#print axioms bala_conjecture_a305550

end D5.S1.Recurrence.Periodic.IntegralEgfTotientPeriod
