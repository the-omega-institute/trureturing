/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeScalar
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeScalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Coeff, mathlib/module/Mathlib.Algebra.BigOperators.Intervals]
   utility: none
   digest: Rational scalar polynomial representation of the actual geometric crown face counts. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopePositive
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open scoped BigOperators
open Polynomial

/-- The scalar weight, with division in the rational field. -/
def crownScalarWeight (n m : ℕ) : ℚ :=
  (n : ℚ) / m * Nat.choose (n + m - 1) (2 * m - 1)

/-- The scalar polynomial; the exceptional vertices and edge are added separately. -/
noncomputable def crownScalarPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ m ∈ Finset.Icc 1 n, C (crownScalarWeight n m) * (1 + X) ^ (n + m)

/-- Every coefficient represents the actual geometric face count, including
    both exceptional corrections, for every positive crown size and every dimension. -/
theorem crownGeometricFaceCount_eq_scalar_coeff (n d : ℕ) (hn : 0 < n) :
    (crownGeometricFaceCount n d : ℚ) =
      (if d = 0 then 2 else 0) + (if d = 1 then 1 else 0) +
        (crownScalarPolynomial n).coeff d := by
  classical
  -- The polynomial of the guarded binomial factor in a fixed profile.
  have hcoeff (i m : ℕ) (hmi : 2 * m ≤ i) :
      (((1 + X) ^ (2 * m) * X ^ (i - 2 * m) : Polynomial ℚ).coeff d) =
        if d ≤ i then (Nat.choose (2 * m) (i - d) : ℚ) else 0 := by
    rw [coeff_mul_X_pow']
    by_cases hlo : i - 2 * m ≤ d
    · rw [if_pos hlo, coeff_one_add_X_pow]
      by_cases hhi : d ≤ i
      · rw [if_pos hhi]
        congr 1
        have he : d - (i - 2 * m) = 2 * m - (i - d) := by omega
        rw [he, Nat.choose_symm (by omega : i - d ≤ 2 * m)]
      · rw [if_neg hhi, Nat.choose_eq_zero_of_lt (by omega)]
        rfl
    · rw [if_neg hlo, if_pos (by omega : d ≤ i),
        Nat.choose_eq_zero_of_lt (by omega)]
      rfl
  -- The profile count vanishes beyond either of its two genuine support bounds.
  have hsupport (i m : ℕ) (hm : 1 ≤ m) (hi : 2 ≤ i)
      (hout : n < m ∨ n + m < i) :
      Nat.choose i (2 * m) * Nat.choose (n + m - 1) (i - 1) = 0 := by
    by_cases hmi : 2 * m ≤ i
    · have hlarge : n + m - 1 < i - 1 := by rcases hout with h | h <;> omega
      rw [Nat.choose_eq_zero_of_lt hlarge, mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega : i < 2 * m), zero_mul]
  -- Normalize a supported profile using the two pinned binomial identities.
  have hweight (i m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (hmi : 2 * m ≤ i) :
      (2 * n : ℚ) / i * Nat.choose i (2 * m) * Nat.choose (n + m - 1) (i - 1) =
        crownScalarWeight n m * Nat.choose (n - m) (i - 2 * m) := by
    have hi : 1 ≤ i := by omega
    have hs := Nat.add_one_mul_choose_eq (i - 1) (2 * m - 1)
    rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel (by omega : 1 ≤ 2 * m)] at hs
    have hc := Nat.choose_mul (n := n + m - 1) (k := i - 1)
      (s := 2 * m - 1) (by omega)
    rw [show n + m - 1 - (2 * m - 1) = n - m by omega,
      show i - 1 - (2 * m - 1) = i - 2 * m by omega] at hc
    have hs' : (i : ℚ) * Nat.choose (i - 1) (2 * m - 1) =
        Nat.choose i (2 * m) * (2 * m : ℚ) := by exact_mod_cast hs
    have hc' : (Nat.choose (n + m - 1) (i - 1) : ℚ) *
        Nat.choose (i - 1) (2 * m - 1) =
        Nat.choose (n + m - 1) (2 * m - 1) * Nat.choose (n - m) (i - 2 * m) := by
      exact_mod_cast hc
    have him : (i : ℚ) ≠ 0 := by positivity
    have hmm : (m : ℚ) ≠ 0 := by positivity
    calc
      _ = (n : ℚ) / m * ((Nat.choose (n + m - 1) (i - 1) : ℚ) *
          Nat.choose (i - 1) (2 * m - 1)) := by
        field_simp
        nlinarith [congrArg (fun x : ℚ => n * Nat.choose (n + m - 1) (i - 1) * x) hs']
      _ = _ := by rw [hc']; unfold crownScalarWeight; ring
  let P : ℕ → ℕ → Polynomial ℚ := fun i m =>
    C ((2 * n : ℚ) / i * Nat.choose i (2 * m) * Nat.choose (n + m - 1) (i - 1)) *
      ((1 + X) ^ (2 * m) * X ^ (i - 2 * m))
  -- Extend the triangular domain by zero terms, exchange sums, and shift i = 2m+j.
  have hpoly : (∑ i ∈ Finset.Icc 2 (2 * n), ∑ m ∈ Finset.Icc 1 (i / 2), P i m) =
      crownScalarPolynomial n := by
    calc
      _ = ∑ i ∈ Finset.Icc 2 (2 * n), ∑ m ∈ Finset.Icc 1 n, P i m := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_Icc.mp hi
        apply Finset.sum_subset
        · intro m hm
          have hm' := Finset.mem_Icc.mp hm
          exact Finset.mem_Icc.mpr ⟨hm'.1, by omega⟩
        · intro m hm hnot
          have hm' := Finset.mem_Icc.mp hm
          have hlt : i < 2 * m := by simp only [Finset.mem_Icc] at hnot; omega
          simp [P, Nat.choose_eq_zero_of_lt hlt]
      _ = ∑ m ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 2 (2 * n), P i m :=
        Finset.sum_comm
      _ = ∑ m ∈ Finset.Icc 1 n,
          C (crownScalarWeight n m) * (1 + X) ^ (n + m) := by
        apply Finset.sum_congr rfl
        intro m hm
        obtain ⟨hm, hmn⟩ := Finset.mem_Icc.mp hm
        have htrim : (∑ i ∈ Finset.Icc 2 (2 * n), P i m) =
            ∑ i ∈ Finset.Icc (2 * m) (n + m), P i m := by
          symm
          apply Finset.sum_subset
          · intro i hi
            obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
            exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          · intro i hi hnot
            have hi' := Finset.mem_Icc.mp hi
            by_cases hmi : 2 * m ≤ i
            · have hz := hsupport i m hm hi'.1 (Or.inr (by
                simp only [Finset.mem_Icc] at hnot; omega))
              have hz' : (Nat.choose i (2 * m) : ℚ) *
                  Nat.choose (n + m - 1) (i - 1) = 0 := by exact_mod_cast hz
              simp only [P, mul_assoc, hz', mul_zero, map_zero, zero_mul]
            · simp [P, Nat.choose_eq_zero_of_lt (by omega : i < 2 * m)]
        rw [htrim]
        have hshift : (∑ i ∈ Finset.Icc (2 * m) (n + m), P i m) =
            ∑ j ∈ Finset.range (n - m + 1), P (j + 2 * m) m := by
          have he : n + m + 1 - 2 * m = n - m + 1 := by omega
          simpa only [Finset.Ico_add_one_right_eq_Icc, he, Nat.add_comm] using
            (Finset.sum_Ico_eq_sum_range (fun i => P i m) (2 * m) (n + m + 1))
        rw [hshift]
        calc
          _ = ∑ j ∈ Finset.range (n - m + 1),
              C (crownScalarWeight n m) * (1 + X) ^ (2 * m) *
                (X ^ j * C (Nat.choose (n - m) j : ℚ)) := by
            apply Finset.sum_congr rfl
            intro j _
            dsimp only [P]
            rw [hweight (j + 2 * m) m hm hmn (by omega)]
            simp only [Nat.add_sub_cancel, map_mul]
            ring
          _ = C (crownScalarWeight n m) * (1 + X) ^ (2 * m) *
              (1 + X) ^ (n - m) := by
            rw [← Finset.mul_sum]
            congr 1
            simpa only [one_pow, mul_one, C_eq_natCast, add_comm X 1] using
              (add_pow (X : Polynomial ℚ) 1 (n - m)).symm
          _ = C (crownScalarWeight n m) * (1 + X) ^ (n + m) := by
            rw [mul_assoc, ← pow_add, show 2 * m + (n - m) = n + m by omega]
      _ = crownScalarPolynomial n := rfl
  -- Exactness is obtained from actual profile cardinalities, before casting division.
  have hcast (i m : ℕ) (hi : i ∈ Finset.Icc 2 (2 * n))
      (hm : m ∈ Finset.Icc 1 (i / 2)) :
      (((2 * n * Nat.choose i (2 * m) * Nat.choose (n + m - 1) (i - 1)) *
        (if d ≤ i then Nat.choose (2 * m) (i - d) else 0)) / i : ℕ) =
      ((P i m).coeff d : ℚ) := by
    obtain ⟨hi, hin⟩ := Finset.mem_Icc.mp hi
    obtain ⟨hm, hmi⟩ := Finset.mem_Icc.mp hm
    have hdiv : i ∣ 2 * n * Nat.choose i (2 * m) * Nat.choose (n + m - 1) (i - 1) := by
      by_cases hn2 : 2 ≤ n
      · let : NeZero (2 * n) := ⟨by omega⟩
        exact ⟨Nat.card (PrescribedOddConnectedCyclePartition (2 * n) i (2 * m)),
          (card_prescribedOddConnectedCyclePartition_identity n i m hn2 hi).symm⟩
      · have hn1 : n = 1 := by omega
        have hi2 : i = 2 := by omega
        have hm1 : m = 1 := by omega
        subst n; subst i; subst m
        norm_num
    rw [Nat.cast_div (dvd_mul_of_dvd_left hdiv _) (by positivity : (i : ℚ) ≠ 0)]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ite, Nat.cast_zero,
      P, coeff_C_mul, hcoeff i m (by omega)]
    ring
  rw [crownGeometricFaceCount_eq_of_pos n d hn]
  push_cast
  congr 1
  rw [← hpoly, finsetSum_coeff]
  simp only [finsetSum_coeff]
  rw [Finset.sum_subtype (Finset.Icc 2 (2 * n)) (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_subtype (Finset.Icc 1 (i.val / 2)) (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro m hm
  exact hcast i.val m.val i.property m.property

#print axioms crownGeometricFaceCount_eq_scalar_coeff

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
