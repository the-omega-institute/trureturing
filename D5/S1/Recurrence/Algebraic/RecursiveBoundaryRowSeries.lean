/- GID: D5/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/RecursiveBoundaryRowSeries
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Unique recursive arrays and exact formal row series for arbitrary boundaries. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
A boundary sequence over a commutative ring determines the entire array by
column recursion. Its rows admit a finite expansion with an explicitly
divisible remainder. Consequently every row is a formal composition and each
entry is a finite sum of coefficients of powers of a normalized reciprocal.
No topology, nonzero boundary condition, or prescribed zeroth row is used.
-/

set_option autoImplicit false

open PowerSeries Finset

namespace D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries

variable {R : Type*} [CommRing R]

/-- The array built column by column from its prescribed first column. -/
def array (a : ℕ → R) : ℕ → ℕ → R
  | n, 0 => a n
  | n, k + 1 => array a (n + 1) k -
      ∑ j : Fin (k + 1), array a n j * a (k - j)
termination_by _n k => k
decreasing_by
  all_goals simp_wf
  omega

/-- The boundary and the full successor recurrence, including both sum endpoints. -/
def IsExtension (a : ℕ → R) (T : ℕ → ℕ → R) : Prop :=
  (∀ n, T n 0 = a n) ∧ ∀ n k,
    T n (k + 1) = T (n + 1) k - ∑ j ∈ range (k + 1), T n j * a (k - j)

/-- The formal generating series of a row of an actual array. -/
noncomputable def row (T : ℕ → ℕ → R) (n : ℕ) : PowerSeries R := mk (T n)

/-- The constant-one series carrying the boundary. -/
noncomputable def source (a : ℕ → R) : PowerSeries R := 1 + X * mk a

/-- The multiplicative inverse determined by the unit constant coefficient. -/
noncomputable def reciprocal (a : ℕ → R) : PowerSeries R := invOfUnit (source a) 1

/-- The zero-constant inner series used in formal substitution. -/
noncomputable def inner (a : ℕ → R) : PowerSeries R := X * reciprocal a

/-- The boundary tail beginning at an arbitrary row index. -/
noncomputable def tail (a : ℕ → R) (n : ℕ) : PowerSeries R := mk fun j => a (n + j)

/-- Existence and uniqueness of the recursive array, its finite row expansion,
the divisibility of the remainder, and both exact infinite-row formulas. -/
theorem result (a : ℕ → R) :
    IsExtension a (array a) ∧
    (∀ T, IsExtension a T → T = array a) ∧
    (∀ n N, row (array a) n =
      reciprocal a * (∑ j ∈ range N, C (a (n + j)) * inner a ^ j) +
      inner a ^ N * row (array a) (n + N)) ∧
    (∀ n N, (X : PowerSeries R) ^ N ∣
      inner a ^ N * row (array a) (n + N)) ∧
    (∀ n, row (array a) n = reciprocal a * (tail a n).subst (inner a)) ∧
    ∀ n k, array a n k =
      ∑ j ∈ range (k + 1), a (n + j) * coeff (k - j) (reciprocal a ^ (j + 1)) := by
  classical
  have ha : IsExtension a (array a) := by
    refine ⟨fun n => by rw [array], ?_⟩
    intro n k
    rw [array]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j => array a n j * a (k - j)) (k + 1)
  have hu : ∀ T, IsExtension a T → T = array a := by
    intro T hT
    have heq : ∀ k n, T n k = array a n k := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro n
        cases k with
        | zero => exact (hT.1 n).trans (ha.1 n).symm
        | succ k =>
          rw [hT.2, ha.2, ih k (by omega) (n + 1)]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [ih j (mem_range.mp hj) n]
    funext n k
    exact heq k n
  let F := source a
  let I := reciprocal a
  let Y := inner a
  have hF0 : constantCoeff F = 1 := by simp [F, source]
  have hIF : I * F = 1 := invOfUnit_mul F 1 hF0
  have hFI : F * I = 1 := mul_invOfUnit F 1 hF0
  have hYS : HasSubst Y := HasSubst.of_constantCoeff_zero' (by simp [Y, inner])
  have hrow : ∀ n, F * row (array a) n = C (a n) + X * row (array a) (n + 1) := by
    intro n
    ext k
    cases k with
    | zero => simp [F, source, row, ha.1]
    | succ k =>
      change coeff (k + 1) ((1 + X * mk a) * row (array a) n) = _
      rw [add_mul, one_mul, mul_assoc, map_add, coeff_succ_X_mul,
        map_add, coeff_succ_X_mul, mul_comm (mk a) (row (array a) n)]
      simp only [row, coeff_mk, coeff_C, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, ↓reduceIte, zero_add]
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [coeff_mk]
      rw [ha.2]
      ring
  have hstep : ∀ n, row (array a) n = I * C (a n) + Y * row (array a) (n + 1) := by
    intro n
    calc
      row (array a) n = I * (F * row (array a) n) := by rw [← mul_assoc, hIF, one_mul]
      _ = I * (C (a n) + X * row (array a) (n + 1)) := by rw [hrow]
      _ = I * C (a n) + Y * row (array a) (n + 1) := by dsimp [Y, inner, I]; ring
  have hfinite : ∀ n N, row (array a) n =
      I * (∑ j ∈ range N, C (a (n + j)) * Y ^ j) +
      Y ^ N * row (array a) (n + N) := by
    intro n N
    induction N with
    | zero => simp
    | succ N ih =>
      calc
        row (array a) n = I * (∑ j ∈ range N, C (a (n + j)) * Y ^ j) +
            Y ^ N * (I * C (a (n + N)) + Y * row (array a) (n + N + 1)) := by
              conv_lhs => rw [ih]
              rw [hstep (n + N)]
        _ = I * (∑ j ∈ range (N + 1), C (a (n + j)) * Y ^ j) +
            Y ^ (N + 1) * row (array a) (n + (N + 1)) := by
              rw [sum_range_succ, pow_succ, ← Nat.add_assoc]
              ring
  have hrem : ∀ n N, (X : PowerSeries R) ^ N ∣ Y ^ N * row (array a) (n + N) := by
    intro n N
    refine ⟨I ^ N * row (array a) (n + N), ?_⟩
    dsimp [Y, inner, I]
    rw [mul_pow, mul_assoc]
  have hbridge : ∀ n, (tail a n).subst Y = F * row (array a) n := by
    intro n
    ext d
    have ht : F * row (array a) n =
        (∑ j ∈ range (d + 1), C (a (n + j)) * Y ^ j) +
        F * (Y ^ (d + 1) * row (array a) (n + (d + 1))) := by
      conv_lhs => rw [hfinite n (d + 1)]
      rw [mul_add, ← mul_assoc F I, hFI, one_mul]
    have hz := X_pow_dvd_iff.mp (dvd_mul_of_dvd_right (hrem n (d + 1)) F) d
      (Nat.lt_succ_self d)
    have ht' := congrArg (coeff d) ht
    rw [map_add, hz, add_zero, map_sum] at ht'
    rw [ht', coeff_subst' hYS]
    rw [finsum_eq_finsetSum_of_support_subset _ (s := range (d + 1))]
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [tail, coeff_mk, coeff_C_mul, smul_eq_mul]
    · intro j hj
      apply mem_range.mpr
      by_contra hnot
      have hdj : ¬ j ≤ d := by omega
      have hzj : coeff j (tail a n) • coeff d (Y ^ j) = 0 := by
        change coeff j (tail a n) • coeff d ((X * I) ^ j) = 0
        rw [mul_pow, coeff_X_pow_mul', if_neg hdj, smul_zero]
      exact hj hzj
  have hcomposition : ∀ n, row (array a) n = I * (tail a n).subst Y := by
    intro n
    calc
      row (array a) n = I * (F * row (array a) n) := by rw [← mul_assoc, hIF, one_mul]
      _ = I * (tail a n).subst Y := by rw [hbridge]
  refine ⟨ha, hu, hfinite, hrem, hcomposition, ?_⟩
  intro n k
  have ht := congrArg (coeff k) (hfinite n (k + 1))
  have hz := X_pow_dvd_iff.mp (hrem n (k + 1)) k (Nat.lt_succ_self k)
  rw [map_add, hz, add_zero, mul_sum, map_sum] at ht
  simp only [row, coeff_mk] at ht
  rw [ht]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (mem_range.mp hj)
  have he : I * (C (a (n + j)) * Y ^ j) = C (a (n + j)) * (X ^ j * I ^ (j + 1)) := by
    change I * (C (a (n + j)) * (X * I) ^ j) = _
    rw [mul_pow, pow_succ]
    ring
  rw [he, coeff_C_mul, coeff_X_pow_mul', if_pos hjk]

end D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries
