/- GID: D5/S1/Digit/Infinite/NoContinuousAdditionExtension
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/NoContinuousAdditionExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: No separately continuous binary operation on legal infinite digit streams extends natural number addition. -/

import D5.S1.Digit.Infinite.SuccessorContinuity
import D5.S1.Digit.Infinite.MultiplierObstruction

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.NoContinuousAdditionExtension

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.MultiplierObstruction
open scoped Topology
open Filter
open D5.S1.Digit
open D5.S1.Digit.GoldenBase4AutomataOracle

/-- A binary operation agrees with addition on every pair of natural number digit rows. -/
def ExtendsFiniteAddition (A : LegalDigits → LegalDigits → LegalDigits) : Prop :=
  ∀ n m : ℕ, A (zRow n) (zRow m) = zRow (n + m)

/-- No separately continuous binary operation on legal digit streams extends finite addition. -/
theorem result :
    ¬ ∃ A : LegalDigits → LegalDigits → LegalDigits,
      (∀ x, Continuous (A x)) ∧
      (∀ y, Continuous (fun x => A x y)) ∧ ExtendsFiniteAddition A := by
  classical
  have row_mem (n i : ℕ) :
      (zRow n).val i = true ↔ i ∈ (rawOfZeckendorf (Nat.zeckendorf n)).support := by
    have raw_mem : i ∈ (rawOfZeckendorf (Nat.zeckendorf n)).support ↔
        i + 2 ∈ Nat.zeckendorf n := by
      conv_rhs => rw [← rawToZeckendorf_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)]
      simp [rawToZeckendorf, Finsupp.mem_toMultiset]
    rw [raw_mem]
    change decide (zeckendorfBit n i = 1) = true ↔ _
    simp only [decide_eq_true_eq]
    by_cases h : i + 2 ∈ Nat.zeckendorf n <;>
      simp [zeckendorfBit, D5.S0.Conventions.wdigits, h]
  let weight (s : Finset ℕ) : ℕ := ∑ i ∈ s, Nat.fib (i + 2)
  have finite_row (s : Finset ℕ) (hs : ∀ i ∈ s, i + 1 ∉ s) (i : ℕ) :
      (zRow (weight s)).val i = decide (i ∈ s) := by
    let r : RawDigits := Finsupp.onFinset s (fun j => if j ∈ s then 1 else 0)
      (by intro j hj; by_contra h; simp [h] at hj)
    have hc : CanonicalRaw r := by
      constructor
      · intro j
        change (if j ∈ s then 1 else 0) ≤ 1
        split <;> omega
      · intro j hj
        change (if j ∈ s then 1 else 0) = 1 at hj
        have hj' : j ∈ s := by split at hj <;> simp_all
        change (if j + 1 ∈ s then 1 else 0) = 0
        simp [hs j hj']
    have hw : rawValue r = weight s := by
      unfold rawValue
      dsimp only [r]
      rw [Finsupp.sum_onFinset _ _ _ _ (by intros; simp)]
      apply Finset.sum_congr rfl
      intro j hj
      simp [hj, D5.S0.Conventions.wValue]
    have hr : rawOfZeckendorf (Nat.zeckendorf (weight s)) = r := by
      rw [← hw, ← rawToZeckendorf_eq_zeckendorf hc, rawOfZeckendorf_rawToZeckendorf]
    have hm := row_mem (weight s) i
    rw [hr, Finsupp.mem_support_iff] at hm
    change ((zRow (weight s)).val i = true ↔ (if i ∈ s then 1 else 0) ≠ 0) at hm
    by_cases hi : i ∈ s <;> cases hb : (zRow (weight s)).val i <;> simp_all
  let positions (p n : ℕ) : Finset ℕ := (Finset.range n).image (fun j => 2 * j + p)
  have mem_positions (p n i : ℕ) :
      i ∈ positions p n ↔ ∃ j < n, i = 2 * j + p := by
    simp [positions, eq_comm]
  have positions_legal (p n : ℕ) : ∀ i ∈ positions p n, i + 1 ∉ positions p n := by
    intro i hi hi'
    obtain ⟨j, hj, he⟩ := (mem_positions p n i).mp hi
    obtain ⟨j', hj', he'⟩ := (mem_positions p n (i + 1)).mp hi'
    omega
  have weight_positions (p n : ℕ) :
      weight (positions p n) = ∑ j ∈ Finset.range n, Nat.fib (2 * j + p + 2) := by
    dsimp [weight, positions]
    rw [Finset.sum_image]
    intro a ha b hb h
    dsimp at h
    omega
  have even_sum (n : ℕ) : weight (positions 0 n) + 1 = Nat.fib (2 * n + 1) := by
    rw [weight_positions]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      conv_rhs => rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, Nat.fib_add_two]
      simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at *
      omega
  have odd_sum (n : ℕ) : weight (positions 1 n) + 1 = Nat.fib (2 * n + 2) := by
    rw [weight_positions]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      conv_rhs => rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by omega, Nat.fib_add_two]
      simp only [Nat.add_assoc, Nat.reduceAdd] at *
      omega
  sorry

end D5.S1.Digit.Infinite.NoContinuousAdditionExtension
