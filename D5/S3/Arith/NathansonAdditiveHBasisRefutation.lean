/- GID: D5/S3/Arith/NathansonAdditiveHBasisRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/NathansonAdditiveHBasisRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/NathansonAdditiveHBasisRefutation.claim; result=D5/S3/Arith/NathansonAdditiveHBasisRefutation.result; claim=D5/S3/Arith/NathansonAdditiveHBasisRefutation.claim
   digest: Refutes Nathanson Problem 12(2) using {-1,1,2} at h=2 and k=3. -/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.IntervalCases

open scoped Pointwise

namespace D5.S3.Arith.NathansonAdditiveHBasisRefutation

noncomputable section

/-- `ell_h(A)`: the largest `n` with `[0, n]` contained in the `h`-fold sumset. -/
def segmentLength (h : ℕ) (A : Finset ℤ) : ℕ :=
  sSup {n : ℕ | ∀ i : ℕ, i ≤ n → ((i : ℤ) ∈ h • A)}

/-- `n-flat_h(k)`: the largest covered initial segment among nonnegative `k`-sets. -/
def nonnegativeMaximum (h k : ℕ) : ℕ :=
  sSup {n : ℕ | ∃ B : Finset ℕ, B.card = k ∧ ∀ i : ℕ, i ≤ n → i ∈ h • B}

/-- Problem 12(2) of arXiv:2605.26425v3, on the domain where `ell_h(A)` is defined. -/
def claim : Prop :=
  ∀ h k : ℕ, 2 ≤ h → 2 ≤ k → ∀ A : Finset ℤ, A.card = k →
    (∃ a ∈ A, a < 0) → (0 : ℤ) ∈ h • A →
      segmentLength h A < nonnegativeMaximum h k

/-- Statement (2) is false at `h = 2`, `k = 3`, and `A = {-1, 1, 2}`. -/
theorem result : ¬ claim := by
  have hmaximumBdd : BddAbove
      {n : ℕ | ∃ B : Finset ℕ, B.card = 3 ∧ ∀ i : ℕ, i ≤ n → i ∈ 2 • B} := by
    refine ⟨8, ?_⟩
    intro n hn
    rcases hn with ⟨B, hcard, hcover⟩
    have hrange : Finset.range (n + 1) ⊆ 2 • B := by
      intro i hi
      exact hcover i (by
        have hi' := Finset.mem_range.mp hi
        omega)
    have hcardRange : n + 1 ≤ (2 • B).card := by
      simpa using Finset.card_le_card hrange
    have hcardSum : (2 • B).card ≤ B.card * B.card := by
      simpa [two_nsmul] using (Finset.card_add_le (s := B) (t := B))
    simp [hcard] at hcardSum
    omega
  have hmaximumLower : 4 ≤ nonnegativeMaximum 2 3 := by
    unfold nonnegativeMaximum
    apply le_csSup hmaximumBdd
    refine ⟨({0, 1, 2} : Finset ℕ), by decide, ?_⟩
    intro i hi
    interval_cases i <;> decide
  have hmaximumUpper : nonnegativeMaximum 2 3 ≤ 4 := by
    unfold nonnegativeMaximum
    apply csSup_le
    · refine ⟨0, ({0, 1, 2} : Finset ℕ), by decide, ?_⟩
      intro i hi
      have : i = 0 := by omega
      subst i
      decide
    · intro n hn
      rcases hn with ⟨B, hcard, hcover⟩
      by_contra hn4
      have hzeroSum : 0 ∈ 2 • B := hcover 0 (by omega)
      have honeSum : 1 ∈ 2 • B := hcover 1 (by omega)
      have hthreeSum : 3 ∈ 2 • B := hcover 3 (by omega)
      have hfiveSum : 5 ∈ 2 • B := hcover 5 (by omega)
      have hzero : 0 ∈ B := by
        rw [two_nsmul, Finset.mem_add] at hzeroSum
        rcases hzeroSum with ⟨a, ha, b, hb, hab⟩
        have : a = 0 ∧ b = 0 := by omega
        simpa [this.1] using ha
      have hone : 1 ∈ B := by
        rw [two_nsmul, Finset.mem_add] at honeSum
        rcases honeSum with ⟨a, ha, b, hb, hab⟩
        have hcases : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
        rcases hcases with hcases | hcases
        · simpa [hcases.2] using hb
        · simpa [hcases.1] using ha
      have htwoOrThree : 2 ∈ B ∨ 3 ∈ B := by
        rw [two_nsmul, Finset.mem_add] at hthreeSum
        rcases hthreeSum with ⟨a, ha, b, hb, hab⟩
        have haCases : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
        rcases haCases with ha0 | ha1 | ha2 | ha3
        · right
          have hb3 : b = 3 := by omega
          simpa [hb3] using hb
        · left
          have hb2 : b = 2 := by omega
          simpa [hb2] using hb
        · left
          simpa [ha2] using ha
        · right
          simpa [ha3] using ha
      rcases htwoOrThree with htwo | hthree
      · have hsubset : ({0, 1, 2} : Finset ℕ) ⊆ B := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact hzero
          · exact hone
          · exact htwo
        have heq : ({0, 1, 2} : Finset ℕ) = B := by
          apply Finset.eq_of_subset_of_card_le hsubset
          simp [hcard]
        rw [← heq] at hfiveSum
        exact (by decide : 5 ∉ 2 • ({0, 1, 2} : Finset ℕ)) hfiveSum
      · have hsubset : ({0, 1, 3} : Finset ℕ) ⊆ B := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact hzero
          · exact hone
          · exact hthree
        have heq : ({0, 1, 3} : Finset ℕ) = B := by
          apply Finset.eq_of_subset_of_card_le hsubset
          simp [hcard]
        rw [← heq] at hfiveSum
        exact (by decide : 5 ∉ 2 • ({0, 1, 3} : Finset ℕ)) hfiveSum
  have hmaximum : nonnegativeMaximum 2 3 = 4 :=
    Nat.le_antisymm hmaximumUpper hmaximumLower
  let A : Finset ℤ := {-1, 1, 2}
  have hsegmentBdd : BddAbove
      {n : ℕ | ∀ i : ℕ, i ≤ n → ((i : ℤ) ∈ 2 • A)} := by
    refine ⟨4, ?_⟩
    intro n hn
    have hnmem := hn n (by omega)
    dsimp [A] at hnmem
    simp [two_nsmul, Finset.mem_add] at hnmem
    omega
  have hsegmentLower : 4 ≤ segmentLength 2 A := by
    unfold segmentLength
    apply le_csSup hsegmentBdd
    intro i hi
    dsimp [A]
    interval_cases i <;> decide
  intro hclaim
  have hstrict := hclaim 2 3 (by omega) (by omega) A (by decide)
    (by
      refine ⟨-1, ?_, by omega⟩
      dsimp [A]
      decide)
    (by
      dsimp [A]
      decide)
  rw [hmaximum] at hstrict
  exact (Nat.not_lt_of_ge hsegmentLower) hstrict

example :
    2 ≤ (2 : ℕ) ∧ 2 ≤ (3 : ℕ) ∧
      ({-1, 1, 2} : Finset ℤ).card = 3 ∧
      (∃ a ∈ ({-1, 1, 2} : Finset ℤ), a < 0) ∧
      (0 : ℤ) ∈ 2 • ({-1, 1, 2} : Finset ℤ) := by
  decide

example : Nonempty (Finset ℤ) := ⟨∅⟩

#print axioms result

end

end D5.S3.Arith.NathansonAdditiveHBasisRefutation
