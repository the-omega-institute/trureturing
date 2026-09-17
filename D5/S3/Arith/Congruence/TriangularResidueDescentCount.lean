/- GID: D5/S3/Arith/Congruence/TriangularResidueDescentCount
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/TriangularResidueDescentCount
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Intervals, mathlib/module/Mathlib.Data.Nat.ModEq, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Count the descents in the triangular-number permutation modulo each positive power of two. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace D5.S3.Arith.Congruence.TriangularResidueDescentCount

/-- The `k`-th triangular number reduced modulo `2 ^ n`, as in OEIS A329278. -/
def T (n k : ℕ) : ℕ :=
  (k * (k + 1) / 2) % 2 ^ n

/-- The number of adjacent strict descents in row `n` of OEIS A329278. -/
def descents (n : ℕ) : ℕ :=
  ((Finset.range (2 ^ n - 1)).filter (fun k => T n (k + 1) < T n k)).card

/-- Kagey's conjectured descent count for the triangular-number permutation modulo `2 ^ n`. -/
theorem kagey_a329278 : ∀ n : ℕ, 0 < n → descents n = 2 ^ (n - 1) - 1 := by
  intro n hn
  let M := 2 ^ n
  let A := fun k : ℕ => k * (k + 1) / 2
  have hM : 0 < M := by simp [M]
  have hA (k : ℕ) : A (k + 1) = A k + (k + 1) := by
    have heven : 2 ∣ k * (k + 1) :=
      even_iff_two_dvd.mp (Nat.even_mul_succ_self k)
    have hnum : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
    simp only [A, hnum, Nat.add_div_of_dvd_right heven]
    omega
  have hprefix : ∀ j : ℕ, j ≤ M - 1 →
      ((Finset.range j).filter (fun k => T n (k + 1) < T n k)).card = A j / M := by
    intro j hj
    induction j with
    | zero => simp [A]
    | succ j ih =>
        have hjM : j + 1 < M := by omega
        have hjmod : (j + 1) % M = j + 1 := Nat.mod_eq_of_lt hjM
        have ih' := ih (by omega)
        by_cases hwrap : M ≤ A j % M + (j + 1)
        · have hmod : A (j + 1) % M + M = A j % M + (j + 1) := by
            rw [hA]
            have hwrap' : M ≤ A j % M + (j + 1) % M := by
              simpa only [hjmod] using hwrap
            simpa only [hjmod] using Nat.add_mod_add_of_le_add_mod hwrap'
          have hdesc : T n (j + 1) < T n j := by
            change A (j + 1) % M < A j % M
            omega
          have hdiv : A (j + 1) / M = A j / M + 1 := by
            have hwrap' : M ≤ A j % M + (j + 1) % M := by
              simpa only [hjmod] using hwrap
            calc
              A (j + 1) / M = (A j + (j + 1)) / M := by rw [hA]
              _ = A j / M + (j + 1) / M + 1 :=
                Nat.add_div_eq_of_le_mod_add_mod hwrap' hM
              _ = A j / M + 1 := by rw [Nat.div_eq_of_lt hjM, add_zero]
          rw [Finset.range_add_one, Finset.filter_insert, if_pos hdesc,
            Finset.card_insert_of_notMem (by simp), ih', hdiv]
        · have hnowrap : A j % M + (j + 1) < M := by omega
          have hmod : A (j + 1) % M = A j % M + (j + 1) := by
            rw [hA]
            have hnowrap' : A j % M + (j + 1) % M < M := by
              simpa only [hjmod] using hnowrap
            simpa only [hjmod] using Nat.add_mod_of_add_mod_lt hnowrap'
          have hnotdesc : ¬ T n (j + 1) < T n j := by
            change ¬ A (j + 1) % M < A j % M
            omega
          have hdiv : A (j + 1) / M = A j / M := by
            have hnowrap' : A j % M + (j + 1) % M < M := by
              simpa only [hjmod] using hnowrap
            calc
              A (j + 1) / M = (A j + (j + 1)) / M := by rw [hA]
              _ = A j / M + (j + 1) / M := Nat.add_div_eq_of_add_mod_lt hnowrap'
              _ = A j / M := by rw [Nat.div_eq_of_lt hjM, add_zero]
          rw [Finset.range_add_one, Finset.filter_insert, if_neg hnotdesc, ih', hdiv]
  change ((Finset.range (M - 1)).filter (fun k => T n (k + 1) < T n k)).card =
    2 ^ (n - 1) - 1
  rw [hprefix (M - 1) le_rfl]
  let H := 2 ^ (n - 1)
  change A (M - 1) / M = H - 1
  have hM_eq : M = H * 2 := by
    change 2 ^ n = 2 ^ (n - 1) * 2
    calc
      2 ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
  have hH : 0 < H := by simp [H]
  have htwo_dvd : 2 ∣ M := by
    refine ⟨H, ?_⟩
    simpa [mul_comm] using hM_eq
  have hAend : A (M - 1) = (M - 1) * H := by
    simp only [A]
    rw [show M - 1 + 1 = M by omega, Nat.mul_div_assoc (M - 1) htwo_dvd, hM_eq]
    simp
  have htwosub : H * 2 - 1 = (H - 1) * 2 + 1 := by omega
  rw [hAend]
  apply Nat.div_eq_of_lt_le
  · rw [hM_eq]
    rw [htwosub]
    nlinarith [Nat.sub_add_cancel hH]
  · rw [hM_eq]
    rw [htwosub]
    nlinarith [Nat.sub_add_cancel hH]

#print axioms kagey_a329278

end D5.S3.Arith.Congruence.TriangularResidueDescentCount
