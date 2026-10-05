/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeHallBranches
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeHallBranches
   mirror-E: none(waiver:binary-hall-branch-realization)
   anchors: [mathlib/module/Mathlib.Data.List.Infix]
   utility: none
   digest: Every binary Hall branch determines an infinite four-digit computed expansion. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallHull
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeIrrational
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeDigits
import Mathlib.Data.List.Infix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

/-- Binary splitting address: committed digits are encoded by `Fin 4` plus one.
The cursor is the first digit still available, encoded by `Fin 3` plus one.
A digit cylinder reverses orientation, so its physical right child commits the cursor
exactly when the number of committed digits is even. The last remaining digit is four. -/
def hallBinaryAddress (b : ℕ → Bool) : ℕ → List (Fin 4) × Fin 3
  | 0 => ([], 0)
  | n + 1 =>
    let p := hallBinaryAddress b n
    if b n = decide (p.1.length % 2 = 0) then
      (p.1 ++ [⟨p.2.val, by have := p.2.isLt; omega⟩], 0)
    else if h : p.2.val = 2 then (p.1 ++ [3], 0)
    else (p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩)

/-- No binary path can postpone commitment for more than three cuts. A diagonal
construction stabilizes all committed digits, and a cursor invariant constrains the
next digit even at nodes that have not yet completed a digit. The infinite stream is
realized by its irrational continued-fraction value and recovered computed expansion. -/
theorem hall_binary_branch_expansion (b : ℕ → Bool) :
    ∃ x ∈ hallCantor, ∀ n : ℕ,
      n ≤ 3 * (hallBinaryAddress b n).1.length + (hallBinaryAddress b n).2.val ∧
      (∀ i : ℕ, ∀ hi : i < (hallBinaryAddress b n).1.length,
        (GenContFract.of x).s.get? i =
          some ⟨1, (((hallBinaryAddress b n).1[i]).val + 1 : ℕ)⟩) ∧
      ∃ a : ℕ, (hallBinaryAddress b n).2.val + 1 ≤ a ∧ a ≤ 4 ∧
        (GenContFract.of x).s.get? (hallBinaryAddress b n).1.length =
          some ⟨1, (a : ℝ)⟩ := by
  classical
  let P (n : ℕ) := (hallBinaryAddress b n).1
  let J (n : ℕ) := (hallBinaryAddress b n).2.val
  have hJ (n : ℕ) : J n < 3 := (hallBinaryAddress b n).2.isLt
  have hstep (n : ℕ) :
      (∃ a : Fin 4, P (n + 1) = P n ++ [a] ∧ J (n + 1) = 0 ∧ J n ≤ a.val) ∨
      (P (n + 1) = P n ∧ J (n + 1) = J n + 1) := by
    dsimp only [P, J]
    rw [hallBinaryAddress]
    split
    · exact Or.inl ⟨_, rfl, rfl, le_rfl⟩
    · split
      · exact Or.inl ⟨3, rfl, rfl, (hJ n).le⟩
      · exact Or.inr ⟨rfl, rfl⟩
  have htime : ∀ n, n ≤ 3 * (P n).length + J n := by
    intro n
    induction n with
    | zero => simp [P, J, hallBinaryAddress]
    | succ n ih =>
        rcases hstep n with ⟨a, hp, hj, _⟩ | ⟨hp, hj⟩
        · rw [hp, hj, List.length_append, List.length_singleton]
          have := hJ n
          omega
        · rw [hp, hj]
          omega
  have hprefix : ∀ n m, n ≤ m → P n <+: P m := by
    intro n m hnm
    induction hnm with
    | refl => exact List.prefix_refl _
    | @step m hnm ih =>
        rcases hstep m with ⟨a, hp, _, _⟩ | ⟨hp, _⟩
        · rw [hp]
          exact ih.trans (List.prefix_append _ _)
        · rw [hp]; exact ih
  have hin (i : ℕ) : i < (P (3 * (i + 1))).length := by
    have := htime (3 * (i + 1))
    have := hJ (3 * (i + 1))
    omega
  let A (i : ℕ) : Fin 4 := (P (3 * (i + 1)))[i]'(hin i)
  have hmatch (n i : ℕ) (hi : i < (P n).length) : A i = (P n)[i] := by
    let N := max n (3 * (i + 1))
    have h₁ := (hprefix (3 * (i + 1)) N (le_max_right _ _)).getElem (hin i)
    have h₂ := (hprefix n N (le_max_left _ _)).getElem hi
    exact h₁.trans h₂.symm
  have htrace : ∀ n m, n ≤ m →
      ((P n).length = (P m).length → J n ≤ J m) ∧
      (∀ h : (P n).length < (P m).length, J n ≤ ((P m)[(P n).length]).val) := by
    intro n m hnm
    induction hnm with
    | refl => exact ⟨fun _ => le_rfl, fun h => False.elim (Nat.lt_irrefl _ h)⟩
    | @step m hnm ih =>
        have hlen := (hprefix n m hnm).length_le
        rcases hstep m with ⟨a, hp, hj, hja⟩ | ⟨hp, hj⟩
        · constructor
          · intro heq
            rw [hp, List.length_append, List.length_singleton] at heq
            omega
          · intro h
            by_cases hlt : (P n).length < (P m).length
            · simpa only [hp, List.getElem_append_left hlt] using ih.2 hlt
            · have heq : (P n).length = (P m).length := by omega
              have hv : ((P (m + 1))[(P n).length]).val = a.val := by
                simp [hp, heq]
              rw [hv]
              exact (ih.1 heq).trans hja
        · constructor
          · intro heq
            rw [hp] at heq
            rw [hj]
            exact (ih.1 heq).trans (Nat.le_succ _)
          · intro h
            have hlt : (P n).length < (P m).length := by simpa only [hp] using h
            simpa only [hp] using ih.2 hlt
  have hcursor (n : ℕ) : J n ≤ (A (P n).length).val := by
    have ht := htime n
    have hj := hJ n
    have hnm : n ≤ 3 * ((P n).length + 1) := by omega
    exact (htrace n _ hnm).2 (hin (P n).length)
  let g : GenContFract ℝ :=
    ⟨0, Stream'.Seq.ofStream (fun i => ⟨1, ((A i).val + 1 : ℕ)⟩)⟩
  have hg : ∀ i, ∃ a : ℕ, 0 < a ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩ := by
    intro i
    exact ⟨(A i).val + 1, Nat.succ_pos _, rfl⟩
  obtain ⟨x, hx, hx0, hx1, _, hcyl⟩ := integer_stream_value g rfl hg
  have hcomputed : GenContFract.of x = g := stream_digit_recovery g rfl hg x hcyl
  have hxC : x ∈ hallCantor := by
    refine ⟨hx, hx0, hx1, ?_⟩
    intro i
    refine ⟨(A i).val + 1, Nat.succ_pos _, by have := (A i).isLt; omega, ?_⟩
    rw [hcomputed]
    rfl
  refine ⟨x, hxC, ?_⟩
  intro n
  refine ⟨htime n, ?_, ?_⟩
  · intro i hi
    rw [hcomputed]
    change g.s.get? i = some ⟨1, (((P n)[i]).val + 1 : ℕ)⟩
    rw [← hmatch n i hi]
    rfl
  · refine ⟨(A (P n).length).val + 1, ?_, ?_, ?_⟩
    · change J n + 1 ≤ (A (P n).length).val + 1
      exact Nat.add_le_add_right (hcursor n) 1
    · have := (A (P n).length).isLt
      omega
    · rw [hcomputed]
      rfl

end D5.S1.Words.KAbelianLagrange
