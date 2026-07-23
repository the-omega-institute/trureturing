/- GID: D5/S1/Digit/CompositeGas
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Explicit first-digit bijection and count recurrence for finite digit-gas words. -/

import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace D5.S1.Digit

/-- Adjacent digits in a gas word cannot both be nonzero. -/
def E6GasLegal {L c : ℕ} (word : Fin L → Fin (c + 1)) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < L),
    word ⟨i, by omega⟩ = 0 ∨ word ⟨i + 1, hi⟩ = 0

/-- Length-`L` words over `{0, ..., c}` satisfying the digit-gas constraint. -/
abbrev E6GasWord (L c : ℕ) :=
  {word : Fin L → Fin (c + 1) // E6GasLegal word}

/-- The singleton zero digit in the alphabet `{0, ..., c}`. -/
abbrev E6ZeroDigit (c : ℕ) :=
  {digit : Fin (c + 1) // digit = 0}

/-- The `c` nonzero digits in the alphabet `{0, ..., c}`. -/
abbrev E6NonzeroDigit (c : ℕ) :=
  {digit : Fin (c + 1) // digit ≠ 0}

/-- The number of length-`L` digit-gas words with per-position maximum `c`. -/
noncomputable def e6Count (L c : ℕ) : ℕ := by
  classical
  exact Fintype.card (E6GasWord L c)

private def e6DropFirst {L c : ℕ} (word : Fin (L + 1) → Fin (c + 1)) :
    Fin L → Fin (c + 1) :=
  fun i ↦ word i.succ

private def e6Prepend {L c : ℕ} (head : Fin (c + 1))
    (tail : Fin L → Fin (c + 1)) : Fin (L + 1) → Fin (c + 1) :=
  Fin.cases head tail

private theorem E6GasLegal_dropFirst {L c : ℕ}
    {word : Fin (L + 1) → Fin (c + 1)} (hword : E6GasLegal word) :
    E6GasLegal (e6DropFirst word) := by
  intro i hi
  simpa [e6DropFirst] using hword (i + 1) (by omega)

private theorem E6GasLegal_prepend_zero {L c : ℕ}
    (zeroDigit : E6ZeroDigit c) {word : Fin L → Fin (c + 1)}
    (hword : E6GasLegal word) :
    E6GasLegal (e6Prepend zeroDigit.1 word) := by
  intro i hi
  cases i with
  | zero => exact Or.inl zeroDigit.2
  | succ i => simpa [e6Prepend] using hword i (by omega)

private theorem E6GasLegal_prepend_nonzero_zero {L c : ℕ}
    (head : E6NonzeroDigit c) (zeroDigit : E6ZeroDigit c)
    {word : Fin L → Fin (c + 1)} (hword : E6GasLegal word) :
    E6GasLegal (e6Prepend head.1 (e6Prepend zeroDigit.1 word)) := by
  intro i hi
  cases i with
  | zero => exact Or.inr zeroDigit.2
  | succ i =>
      cases i with
      | zero => exact Or.inl zeroDigit.2
      | succ i => simpa [e6Prepend] using hword i (by omega)

/--
Split a length-`L+2` gas word at its first digit. A zero leaves a length-`L+1`
gas word. A nonzero first digit forces and records a zero second digit, leaving
a length-`L` gas word. Both branches retain their leading digits explicitly.
-/
def e6_gas_equiv (L c : ℕ) :
    E6GasWord (L + 2) c ≃
      (E6ZeroDigit c × E6GasWord (L + 1) c) ⊕
        (E6NonzeroDigit c × E6ZeroDigit c × E6GasWord L c) where
  toFun word :=
    if hzero : word.1 0 = 0 then
      Sum.inl
        (⟨word.1 0, hzero⟩,
          ⟨e6DropFirst word.1, E6GasLegal_dropFirst word.2⟩)
    else
      have hsecond : word.1 1 = 0 :=
        (word.2 0 (by omega)).resolve_left hzero
      Sum.inr
        (⟨word.1 0, hzero⟩,
          ⟨word.1 1, hsecond⟩,
          ⟨e6DropFirst (e6DropFirst word.1),
            E6GasLegal_dropFirst (E6GasLegal_dropFirst word.2)⟩)
  invFun split :=
    match split with
    | Sum.inl pair =>
        ⟨e6Prepend pair.1.1 pair.2.1,
          E6GasLegal_prepend_zero pair.1 pair.2.2⟩
    | Sum.inr pair =>
        ⟨e6Prepend pair.1.1 (e6Prepend pair.2.1.1 pair.2.2.1),
          E6GasLegal_prepend_nonzero_zero pair.1 pair.2.1 pair.2.2.2⟩
  left_inv word := by
    by_cases hzero : word.1 0 = 0
    · simp only [hzero, dite_true]
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun _ ↦ rfl) i
      exact hzero.symm
    · have hsecond : word.1 1 = 0 :=
        (word.2 0 (by omega)).resolve_left hzero
      simp only [hzero, dite_false]
      apply Subtype.ext
      funext i
      refine Fin.cases rfl ?_ i
      intro j
      exact Fin.cases rfl (fun _ ↦ rfl) j
  right_inv split := by
    cases split with
    | inl pair =>
        have hzero : e6Prepend pair.1.1 pair.2.1 0 = 0 := by
          simpa [e6Prepend] using pair.1.2
        simp only [hzero, dite_true]
        apply congrArg Sum.inl
        apply Prod.ext
        · apply Subtype.ext
          exact pair.1.2.symm
        · apply Subtype.ext
          funext i
          rfl
    | inr pair =>
        have hnonzero :
            e6Prepend pair.1.1 (e6Prepend pair.2.1.1 pair.2.2.1) 0 ≠ 0 := by
          simpa [e6Prepend] using pair.1.2
        simp only [hnonzero, dite_false]
        rfl

/-- The empty word is the unique length-zero digit-gas word. -/
@[simp] theorem e6_count_zero (c : ℕ) : e6Count 0 c = 1 := by
  classical
  simp [e6Count, E6GasWord, E6GasLegal]

/-- Every one-letter word is legal, so there are `c + 1` such words. -/
@[simp] theorem e6_count_one (c : ℕ) : e6Count 1 c = c + 1 := by
  classical
  simp [e6Count, E6GasWord, E6GasLegal]

/-- The first-digit bijection gives the digit-gas count recurrence. -/
theorem e6_count_recurrence (L c : ℕ) :
    e6Count (L + 2) c = e6Count (L + 1) c + c * e6Count L c := by
  classical
  rw [e6Count, Fintype.card_congr (e6_gas_equiv L c)]
  simp [e6Count, E6ZeroDigit, E6NonzeroDigit]

end D5.S1.Digit
