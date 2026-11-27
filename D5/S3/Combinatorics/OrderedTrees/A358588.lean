/- GID: D5/S3/Combinatorics/OrderedTrees/A358588
   generality: I
   mirror-B: D5/B/S3/Combinatorics/OrderedTrees/A358588
   mirror-E: none(waiver:ordered-tree-leaf-pruning)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: The actual ordered tree counts satisfy Wu’s generating function and signed recurrence. -/

import D5.S3.Combinatorics.OrderedTrees.LeafGapCount
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Chai Wah Wu's generating function and recurrence for OEIS A358588. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Combinatorics.OrderedTrees.LeafPruning
open PowerSeries
open scoped PowerSeries BigOperators

namespace D5.S3.Combinatorics.OrderedTrees.A358588

private noncomputable def geometricSeries : ℤ⟦X⟧ := mk 1
private def weightedGeometricSeries : ℤ⟦X⟧ := mk (fun u ↦ 2 * (u : ℤ) + 1)

private theorem weightedGeometricSeries_eq : weightedGeometricSeries = 2 * geometricSeries ^ 2 - geometricSeries := by
  have hg := mk_one_pow_eq_mk_choose_add ℤ 1
  change geometricSeries ^ 2 = _ at hg
  rw [hg]
  ext n
  simp [weightedGeometricSeries, geometricSeries, Nat.choose_one_right]
  ring

private theorem weightedGeometricSeries_identity : (1 - X)^2 * weightedGeometricSeries = 1 + X := by
  have h : (1 - X) * geometricSeries = 1 := by
    rw [mul_comm]
    exact mk_one_mul_one_sub_eq_one ℤ
  rw [weightedGeometricSeries_eq]
  calc
    (1 - X)^2 * (2 * geometricSeries ^ 2 - geometricSeries)
      = 2 * ((1 - X) * geometricSeries)^2 - (1 - X) * ((1 - X) * geometricSeries) := by ring
    _ = 1 + X := by rw [h]; ring

private noncomputable def skeletonArgument : ℤ⟦X⟧ := X * geometricSeries^2
private theorem hasSubst_skeletonArgument : HasSubst skeletonArgument :=
  .of_constantCoeff_zero' (by simp [skeletonArgument])
private noncomputable def decorationSeries : ℤ⟦X⟧ :=
  X^5 * geometricSeries^5 * weightedGeometricSeries.subst skeletonArgument

private theorem rational_identity :
    ((1 - X)^3 * (1 - 3 * X + X^2)^2) * decorationSeries =
      X^5 * (1 - X + X^2) := by
  have h : (1 - X) * geometricSeries = 1 := by
    rw [mul_comm]
    exact mk_one_mul_one_sub_eq_one ℤ
  have hw : (1 - skeletonArgument)^2 * weightedGeometricSeries.subst skeletonArgument = 1 + skeletonArgument := by
    have hh := congrArg (substAlgHom (R := ℤ) hasSubst_skeletonArgument) weightedGeometricSeries_identity
    simpa only [map_mul, map_pow, map_sub, map_one, map_add, substAlgHom_X, coe_substAlgHom] using hh
  have hp : (1 - 3 * X + X^2) * geometricSeries^2 = 1 - skeletonArgument := by
    have hh : ((1 - X) * geometricSeries)^2 = 1 := by rw [h, one_pow]
    unfold skeletonArgument
    linear_combination hh
  have hq : (1 - X)^2 * (1 + skeletonArgument) = 1 - X + X^2 := by
    have hh : ((1 - X) * geometricSeries)^2 = 1 := by rw [h, one_pow]
    unfold skeletonArgument
    linear_combination X * hh
  unfold decorationSeries
  calc
    _ = X^5 * (((1 - X) * geometricSeries) * ((1 - 3 * X + X^2) * geometricSeries^2)^2 *
          ((1 - X)^2 * weightedGeometricSeries.subst skeletonArgument)) := by ring
    _ = X^5 * ((1 - X)^2 * ((1 - skeletonArgument)^2 * weightedGeometricSeries.subst skeletonArgument)) := by rw [h, hp]; ring
    _ = X^5 * (1 - X + X^2) := by rw [hw, hq]

private theorem finite_subst (j n : ℕ) (hj : j ≤ n) :
    coeff j (weightedGeometricSeries.subst skeletonArgument) =
      coeff j (∑ u ∈ Finset.range (n + 1), C (2 * (u : ℤ) + 1) * skeletonArgument^u) := by
  classical
  rw [coeff_subst' hasSubst_skeletonArgument]
  simp only [weightedGeometricSeries, coeff_mk, smul_eq_mul, map_sum, coeff_C_mul]
  apply finsum_eq_sum_of_support_subset
  intro u hu
  apply Finset.mem_range.mpr
  by_contra! h
  have hju : ¬ u ≤ j := by omega
  simp [Function.mem_support, skeletonArgument, mul_pow, coeff_X_pow_mul', hju] at hu

private theorem coeff_term (n u : ℕ) :
    coeff n ((X^5 * geometricSeries^5) * (C (2 * (u : ℤ) + 1) * skeletonArgument^u)) =
      if u + 5 ≤ n then (2 * (u : ℤ) + 1) * ((n + u - 1).choose (2 * u + 4) : ℤ)
      else 0 := by
  have hterm :
      (X^5 * geometricSeries^5) * (C (2 * (u : ℤ) + 1) * skeletonArgument^u) =
      C (2 * (u : ℤ) + 1) * (X^(u + 5) * geometricSeries^((2 * u + 4) + 1)) := by
    unfold skeletonArgument
    rw [mul_pow, ← pow_mul, show 2 * u + 4 + 1 = 5 + 2 * u by omega, pow_add, pow_add]
    ring
  rw [hterm, coeff_C_mul, coeff_X_pow_mul']
  have hg := mk_one_pow_eq_mk_choose_add ℤ (2 * u + 4)
  change geometricSeries ^ (2 * u + 4 + 1) = _ at hg
  rw [hg]
  by_cases hu : u + 5 ≤ n
  · simp only [hu, ite_true, coeff_mk]
    rw [show 2 * u + 4 + (n - (u + 5)) = n + u - 1 by omega]
  · simp [hu]

private theorem actual_series : mk (fun n ↦ (count n : ℤ)) = decorationSeries := by
  ext n
  have he : coeff n decorationSeries =
      coeff n ((X^5 * geometricSeries^5) *
        (∑ u ∈ Finset.range (n + 1), C (2 * (u : ℤ) + 1) * skeletonArgument^u)) := by
    unfold decorationSeries
    rw [coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [finite_subst ij.2 n (by have hh := Finset.mem_antidiagonal.mp hij; omega)]
  rw [he, Finset.mul_sum, map_sum, coeff_mk, count_eq_sum]
  push_cast
  rw [← Finset.sum_subset
    (s₁ := Finset.range (n - 4)) (s₂ := Finset.range (n + 1)) (Finset.range_mono (by omega))]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [coeff_term, ite_eq_left]
    have h := Finset.mem_range.mp hu
    omega
  · intro u _ hu
    rw [coeff_term, ite_eq_right]
    have h := Finset.mem_range.not.mp hu
    omega

private theorem actual_rational :
    ((1 - X)^3 * (1 - 3 * X + X^2)^2) * mk (fun n ↦ (count n : ℤ)) =
      X^5 * (1 - X + X^2) := by
  rw [actual_series, rational_identity]

private theorem initial :
    count 1 = 0 ∧ count 2 = 0 ∧ count 3 = 0 ∧ count 4 = 0 ∧
      count 5 = 1 ∧ count 6 = 8 ∧ count 7 = 41 := by
  refine ⟨count_eq_zero_of_lt_five 1 (by decide), count_eq_zero_of_lt_five 2 (by decide),
    count_eq_zero_of_lt_five 3 (by decide), count_eq_zero_of_lt_five 4 (by decide), ?_⟩
  simp only [count_eq_sum]
  decide

private theorem recurrence (n : ℕ) (hn : 7 < n) :
    (count n : ℤ) = 9 * count (n - 1) - 32 * count (n - 2) + 58 * count (n - 3) -
      58 * count (n - 4) + 32 * count (n - 5) - 9 * count (n - 6) + count (n - 7) := by
  let a : ℤ⟦X⟧ := mk (fun n ↦ (count n : ℤ))
  have he : ((1 - X)^3 * (1 - 3 * X + X^2)^2) * a =
      a - C (9 : ℤ) * (X^1 * a) + C (32 : ℤ) * (X^2 * a) - C (58 : ℤ) * (X^3 * a) + C (58 : ℤ) * (X^4 * a) -
        C (32 : ℤ) * (X^5 * a) + C (9 : ℤ) * (X^6 * a) - X^7 * a := by
    simp only [map_ofNat]
    ring
  have hi : X^5 * (1 - X + X^2 : ℤ⟦X⟧) = X^5 - X^6 + X^7 := by ring
  have h := congrArg (coeff n) (show _ * a = _ from actual_rational)
  rw [he, hi] at h
  simp only [map_sub, map_add, coeff_X_pow, coeff_C_mul, coeff_X_pow_mul', a, coeff_mk,
    show ¬ n = 5 by omega, show ¬ n = 6 by omega, show ¬ n = 7 by omega,
    show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
    show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, ite_true, ite_false] at h
  linear_combination h

private theorem actual_quotient :
    mk (fun n ↦ (count n : ℤ)) =
      X^5 * (1 - X + X^2) * invOfUnit ((1 - X)^3 * (1 - 3 * X + X^2)^2) 1 := by
  let D : ℤ⟦X⟧ := (1 - X)^3 * (1 - 3 * X + X^2)^2
  have hD : D.constantCoeff = ↑(1 : ℤˣ) := by simp [D]
  have hI := invOfUnit_mul D (1 : ℤˣ) hD
  calc
    _ = (invOfUnit D 1 * D) * mk (fun n ↦ (count n : ℤ)) := by rw [hI, one_mul]
    _ = invOfUnit D 1 * (D * mk (fun n ↦ (count n : ℤ))) := by rw [mul_assoc]
    _ = _ := by rw [show D * mk (fun n ↦ (count n : ℤ)) = _ from actual_rational]; exact mul_comm _ _

/-- At every index the actual ordered-tree count has the stated finite cardinality,
Wu's ordinary generating function (with zero constant term), the seven initial
values, and the signed integer recurrence for indices greater than seven.
The fraction uses its sign-normalized denominator with constant coefficient one. -/
theorem result (n : ℕ) :
    (Set.Finite {t : Tree | t.vertices = n ∧ t.height = t.internal} ∧
      count n = Set.ncard {t : Tree | t.vertices = n ∧ t.height = t.internal}) ∧
    count 0 = 0 ∧
    mk (fun k ↦ (count k : ℤ)) =
      X^5 * (1 - X + X^2) * invOfUnit ((1 - X)^3 * (1 - 3 * X + X^2)^2) 1 ∧
    (count 1 = 0 ∧ count 2 = 0 ∧ count 3 = 0 ∧ count 4 = 0 ∧
      count 5 = 1 ∧ count 6 = 8 ∧ count 7 = 41) ∧
    (7 < n →
      (count n : ℤ) = 9 * count (n - 1) - 32 * count (n - 2) + 58 * count (n - 3) -
        58 * count (n - 4) + 32 * count (n - 5) - 9 * count (n - 6) + count (n - 7)) :=
  ⟨count_spec n, count_eq_zero_of_lt_five 0 (by decide), actual_quotient, initial, recurrence n⟩

end D5.S3.Combinatorics.OrderedTrees.A358588
