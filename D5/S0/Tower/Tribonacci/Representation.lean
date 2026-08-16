/- GID: D5/S0/Tower/Tribonacci/Representation
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/Representation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Admissible Tribonacci words decode uniquely to their initial natural interval. -/

import D5.S0.Tower.Tribonacci.Names

namespace D5.S0.Tower.Tribonacci.Representation

open D5.S0.Tower.Tribonacci.Names

/- Library-search audit trail (2026-08-16):
   * The repository provides the frozen Tribonacci recurrence, admissibility
     predicate, prefix split, and exact name-layer cardinality in `Names`.
   * Pinned mathlib's `Data.Nat.Fib.Zeckendorf` proves Fibonacci uniqueness via
     `Nat.zeckendorfEquiv`, but has no no-111 Tribonacci representation theorem.
   * The Fibonacci proof supplies a normalization model only; no theorem there
     can be instantiated directly for the three-term recurrence. -/

/-- Decode an admissible word using the frozen weights `1, 2, 4, 7, 13, ...`. -/
def decode {Q : Nat} (name : TribonacciName Q) : Nat :=
  ∑ i : Fin Q, if name.1 i then tribonacci (i.1 + 2) else 0

/-- Removing the highest digit preserves Tribonacci admissibility. -/
theorem admissible_init (Q : Nat) (word : Fin (Q + 1) → Bool)
    (hadmissible : TribonacciAdmissible (Q + 1) word) :
    TribonacciAdmissible Q (Fin.init word) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      match Q with
      | 0 => trivial
      | 1 => trivial
      | 2 => trivial
      | n + 3 =>
          rw [admissible_add_three_iff n]
          constructor
          · have hfirst := (admissible_add_three_iff (n + 1) word).1 hadmissible |>.1
            change ¬ (word 0 ∧ word 1 ∧ word (Fin.castSucc (2 : Fin (n + 3))))
            rw [show Fin.castSucc (2 : Fin (n + 3)) = (2 : Fin (n + 4)) by
              apply Fin.ext
              rfl]
            exact hfirst
          · rw [Fin.tail_init_eq_init_tail]
            exact ih (n + 2) (by omega) (Fin.tail word)
              ((admissible_add_three_iff (n + 1) word).1 hadmissible |>.2)

/-- Every length-three window of an admissible word avoids `true, true, true`. -/
theorem admissible_no_three_at (Q i : Nat) (word : Fin Q → Bool)
    (hadmissible : TribonacciAdmissible Q word) (hi : i + 2 < Q) :
    ¬ (word ⟨i, by omega⟩ ∧ word ⟨i + 1, by omega⟩ ∧ word ⟨i + 2, hi⟩) := by
  induction i generalizing Q with
  | zero =>
      match Q with
      | 0 => omega
      | 1 => omega
      | 2 => omega
      | n + 3 =>
          change ¬ (word 0 ∧ word 1 ∧ word (2 : Fin (n + 3)))
          exact (admissible_add_three_iff n word).1 hadmissible |>.1
  | succ i ih =>
      match Q with
      | 0 => omega
      | Q + 1 =>
          have htail := admissible_tail Q word hadmissible
          have hrec := ih (Q := Q) (Fin.tail word) htail (by omega)
          change ¬ (word ⟨i + 1, by omega⟩ ∧ word ⟨i + 2, by omega⟩ ∧
            word ⟨i + 3, by omega⟩)
          change ¬ (word ⟨i + 1, by omega⟩ ∧ word ⟨i + 2, by omega⟩ ∧
            word ⟨i + 3, by omega⟩) at hrec
          exact hrec

/-- The admissible name obtained by removing the highest digit. -/
def initName {Q : Nat} (name : TribonacciName (Q + 1)) : TribonacciName Q :=
  ⟨Fin.init name.1, admissible_init Q name.1 name.2⟩

/-- Decoding splits into the lower prefix and the highest weighted digit. -/
theorem decode_snoc {Q : Nat} (name : TribonacciName (Q + 1)) :
    decode name = decode (initName name) +
      if name.1 (Fin.last Q) then tribonacci (Q + 2) else 0 := by
  simp only [decode, Fin.sum_univ_castSucc, initName, Fin.init, Fin.val_castSucc,
    Fin.val_last]
  rfl

/-- Every length-`Q` admissible word decodes below the next Tribonacci weight. -/
theorem decode_lt_tribonacci (Q : Nat) (name : TribonacciName Q) :
    decode name < tribonacci (Q + 2) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      match Q with
      | 0 => simp [decode, tribonacci]
      | 1 =>
          change (if name.1 0 then 1 else 0) < 2
          cases name.1 0 <;> decide
      | 2 =>
          change (if name.1 0 then 1 else 0) + (if name.1 1 then 2 else 0) < 4
          cases name.1 0 <;> cases name.1 1 <;> decide
      | n + 3 =>
          let prefixTwo := initName name
          let prefixOne := initName prefixTwo
          let lowName := initName prefixOne
          have hprefix : decode lowName < tribonacci (n + 2) :=
            ih n (by omega) lowName
          change decode (initName prefixOne) < tribonacci (n + 2) at hprefix
          have hforbidden := admissible_no_three_at (n + 3) n name.1 name.2 (by omega)
          have hindexZero : prefixOne.1 (Fin.last n) = name.1 ⟨n, by omega⟩ := by
            apply congrArg name.1
            apply Fin.ext
            rfl
          have hindexOne : prefixTwo.1 (Fin.last (n + 1)) =
              name.1 ⟨n + 1, by omega⟩ := by
            apply congrArg name.1
            apply Fin.ext
            rfl
          have hindexTwo : name.1 (Fin.last (n + 2)) = name.1 ⟨n + 2, by omega⟩ := by
            apply congrArg name.1
            apply Fin.ext
            rfl
          have htop : ¬ (prefixOne.1 (Fin.last n) ∧
              prefixTwo.1 (Fin.last (n + 1)) ∧ name.1 (Fin.last (n + 2))) := by
            rw [hindexZero, hindexOne, hindexTwo]
            exact hforbidden
          have hrecurrence : tribonacci (n + 5) =
              tribonacci (n + 4) + tribonacci (n + 3) + tribonacci (n + 2) := by
            simpa only [Nat.add_assoc, Nat.reduceAdd] using tribonacci_add_three (n + 2)
          have hmonoZero : tribonacci (n + 2) ≤ tribonacci (n + 3) := by
            have hrec := tribonacci_add_three n
            omega
          have hmonoOne : tribonacci (n + 3) ≤ tribonacci (n + 4) := by
            have hrec : tribonacci (n + 4) =
                tribonacci (n + 3) + tribonacci (n + 2) + tribonacci (n + 1) := by
              simpa only [Nat.add_assoc, Nat.reduceAdd] using tribonacci_add_three (n + 1)
            omega
          rw [decode_snoc name, decode_snoc prefixTwo, decode_snoc prefixOne]
          simp only [show n + 1 + 2 = n + 3 by omega,
            show n + 2 + 2 = n + 4 by omega, show n + 3 + 2 = n + 5 by omega]
          cases h0 : prefixOne.1 (Fin.last n) <;>
            cases h1 : prefixTwo.1 (Fin.last (n + 1)) <;>
            cases h2 : name.1 (Fin.last (n + 2)) <;>
            simp [h0, h1, h2] at htop ⊢ <;>
            omega

/-- Equivalently, the maximum possible decoded value is at most `T(Q+2)-1`. -/
theorem decode_le_sub_one (Q : Nat) (name : TribonacciName Q) :
    decode name ≤ tribonacci (Q + 2) - 1 := by
  have hbound := decode_lt_tribonacci Q name
  omega

theorem name_eq_of_init_eq_of_last_eq {Q : Nat} (left right : TribonacciName (Q + 1))
    (hinit : initName left = initName right)
    (hlast : left.1 (Fin.last Q) = right.1 (Fin.last Q)) : left = right := by
  have hwords : Fin.init left.1 = Fin.init right.1 := by
    exact congrArg Subtype.val hinit
  apply Subtype.ext
  rw [← Fin.snoc_init_self left.1, ← Fin.snoc_init_self right.1]
  rw [hwords, hlast]

/-- Integer decoding is injective on every fixed-length admissible name layer. -/
theorem decode_injective (Q : Nat) : Function.Injective (@decode Q) := by
  induction Q with
  | zero =>
      intro left right _
      apply Subtype.ext
      funext i
      exact Fin.elim0 i
  | succ Q ih =>
      intro left right hequal
      rw [decode_snoc left, decode_snoc right] at hequal
      cases hleft : left.1 (Fin.last Q) <;>
        cases hright : right.1 (Fin.last Q)
      · apply name_eq_of_init_eq_of_last_eq left right
        · exact ih (by simpa [hleft, hright] using hequal)
        · simp [hleft, hright]
      · have hbound := decode_lt_tribonacci Q (initName left)
        simp [hleft, hright] at hequal
        omega
      · have hbound := decode_lt_tribonacci Q (initName right)
        simp [hleft, hright] at hequal
        omega
      · apply name_eq_of_init_eq_of_last_eq left right
        · apply ih
          simp [hleft, hright] at hequal
          omega
        · simp [hleft, hright]

/-- The highest digit is selected exactly when its weight does not exceed the decoded value. -/
theorem last_eq_true_iff_weight_le_decode {Q : Nat} (name : TribonacciName (Q + 1)) :
    name.1 (Fin.last Q) = true ↔ tribonacci (Q + 2) ≤ decode name := by
  cases hlast : name.1 (Fin.last Q)
  · have hbound := decode_lt_tribonacci Q (initName name)
    rw [decode_snoc name]
    simp [hlast]
    omega
  · rw [decode_snoc name]
    simp [hlast]

/-- The bounded decoding map, with its range proof supplied by the maximum-value theorem. -/
def decodeFin {Q : Nat} (name : TribonacciName Q) : Fin (tribonacci (Q + 2)) :=
  ⟨decode name, decode_lt_tribonacci Q name⟩

theorem decodeFin_injective (Q : Nat) : Function.Injective (@decodeFin Q) := by
  intro left right hequal
  apply decode_injective Q
  exact congrArg Fin.val hequal

/-- Bounded decoding is bijective at every word length. -/
theorem decode_bijective (Q : Nat) : Function.Bijective (@decodeFin Q) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact decodeFin_injective Q
  · rw [Fintype.card_fin, tribonacci_name_card]

/-- Every natural below the next Tribonacci weight has an admissible length-`Q` representation. -/
theorem exists_decode_eq (Q n : Nat) (hn : n < tribonacci (Q + 2)) :
    ∃ name : TribonacciName Q, decode name = n := by
  obtain ⟨name, hname⟩ := (decode_bijective Q).2 ⟨n, hn⟩
  exact ⟨name, congrArg Fin.val hname⟩

/-- The maximum decoded value at length `Q` is exactly `T(Q+2)-1`. -/
theorem decode_max_value (Q : Nat) :
    (∀ name : TribonacciName Q, decode name ≤ tribonacci (Q + 2) - 1) ∧
      ∃ name : TribonacciName Q, decode name = tribonacci (Q + 2) - 1 := by
  constructor
  · exact decode_le_sub_one Q
  · have hpositive : 0 < tribonacci (Q + 2) := by
      induction Q with
      | zero => decide
      | succ Q ih =>
          rw [show Q + 1 + 2 = Q + 3 by omega, tribonacci_add_three Q]
          omega
    exact exists_decode_eq Q (tribonacci (Q + 2) - 1) (by omega)

/-- The integer decoding map is the canonical equivalence with its initial natural interval. -/
noncomputable def decodeEquiv (Q : Nat) :
    TribonacciName Q ≃ Fin (tribonacci (Q + 2)) :=
  Equiv.ofBijective (@decodeFin Q) (decode_bijective Q)

/-- The inverse representation map supplied by the decoding equivalence. -/
noncomputable def encode (Q : Nat) (n : Fin (tribonacci (Q + 2))) : TribonacciName Q :=
  (decodeEquiv Q).symm n

@[simp] theorem decode_encode (Q : Nat) (n : Fin (tribonacci (Q + 2))) :
    decode (encode Q n) = n.1 := by
  exact congrArg Fin.val ((decodeEquiv Q).apply_symm_apply n)

/-- The inverse map makes the greedy highest-weight choice. -/
theorem encode_last_eq_true_iff (Q : Nat) (n : Fin (tribonacci (Q + 3))) :
    (encode (Q + 1) n).1 (Fin.last Q) = true ↔ tribonacci (Q + 2) ≤ n.1 := by
  rw [last_eq_true_iff_weight_le_decode, decode_encode]

example :
    decode ⟨![false, false, false], by decide⟩ = 0 ∧
    decode ⟨![true, false, false], by decide⟩ = 1 ∧
    decode ⟨![false, true, false], by decide⟩ = 2 ∧
    decode ⟨![true, true, false], by decide⟩ = 3 ∧
    decode ⟨![false, false, true], by decide⟩ = 4 ∧
    decode ⟨![true, false, true], by decide⟩ = 5 ∧
    decode ⟨![false, true, true], by decide⟩ = 6 := by
  decide

example :
    decode ⟨![false, false, false, false], by decide⟩ = 0 ∧
    decode ⟨![true, false, false, false], by decide⟩ = 1 ∧
    decode ⟨![false, true, false, false], by decide⟩ = 2 ∧
    decode ⟨![true, true, false, false], by decide⟩ = 3 ∧
    decode ⟨![false, false, true, false], by decide⟩ = 4 ∧
    decode ⟨![true, false, true, false], by decide⟩ = 5 ∧
    decode ⟨![false, true, true, false], by decide⟩ = 6 ∧
    decode ⟨![false, false, false, true], by decide⟩ = 7 ∧
    decode ⟨![true, false, false, true], by decide⟩ = 8 ∧
    decode ⟨![false, true, false, true], by decide⟩ = 9 ∧
    decode ⟨![true, true, false, true], by decide⟩ = 10 ∧
    decode ⟨![false, false, true, true], by decide⟩ = 11 ∧
    decode ⟨![true, false, true, true], by decide⟩ = 12 := by
  decide

example (Q : Nat) : Function.Injective (@decode Q) :=
  decode_injective Q

example (Q n : Nat) (hn : n < tribonacci (Q + 2)) :
    ∃ name : TribonacciName Q, decode name = n :=
  exists_decode_eq Q n hn

noncomputable example (Q : Nat) : TribonacciName Q ≃ Fin (tribonacci (Q + 2)) :=
  decodeEquiv Q

end D5.S0.Tower.Tribonacci.Representation
