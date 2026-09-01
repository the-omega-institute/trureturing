/- GID: D5/S1/Digit/Admissibility/LeastDigitDecomposition
   generality: I
   mirror-B: D5/B/S1/Digit/Admissibility/LeastDigitDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: Positive canonical W digits split uniquely according to their least occupied position. -/

/- Library-search audit trail (2026-08-16):
   * D5 has no equivalent least-digit three-way decomposition theorem.
   * Pinned Mathlib's Zeckendorf module supplies representation and uniqueness,
     but no theorem splitting a representation by its least occupied digit.
   * The proof reuses `Finsupp.mapDomain_comapDomain`, `Finsupp.erase_add_single`,
     and the repository's `CanonicalRaw` bridge to Mathlib Zeckendorf digits. -/

import D5.S1.Digit.Raw

namespace D5.S1.Digit.Admissibility.LeastDigitDecomposition

open D5.S1.Digit

/-- Shift every occupied raw W-digit position upward by `offset`. -/
noncomputable def shiftDigits (offset : Nat) (r : RawDigits) : RawDigits :=
  Finsupp.mapDomain (fun i => offset + i) r

/-- Shifted raw digit strings have a unique preimage. -/
theorem shift_digits_injective (offset : Nat) : Function.Injective (shiftDigits offset) :=
  Finsupp.mapDomain_injective fun _ _ equality => Nat.add_left_cancel equality

/-- Read a raw digit string from `offset` onward and reindex its tail from zero. -/
noncomputable def dropDigits (offset : Nat) (r : RawDigits) : RawDigits :=
  Finsupp.comapDomain (fun i => offset + i) r fun _ _ _ _ equality =>
    Nat.add_left_cancel equality

@[simp] theorem drop_digits_apply (offset i : Nat) (r : RawDigits) :
    dropDigits offset r i = r (offset + i) := by
  rfl

private theorem shift_drop_digits_eq (offset : Nat) (r : RawDigits)
    (low : ∀ i, i < offset → r i = 0) :
    shiftDigits offset (dropDigits offset r) = r := by
  apply Finsupp.mapDomain_comapDomain
  · exact fun _ _ equality => Nat.add_left_cancel equality
  · intro i hi
    have hoffset : offset <= i := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hi) (low i (Nat.lt_of_not_ge h))
    exact Set.mem_range.mpr ⟨i - offset, Nat.add_sub_of_le hoffset⟩

private theorem canonical_drop_digits {r : RawDigits} (canonical : CanonicalRaw r)
    (offset : Nat) : CanonicalRaw (dropDigits offset r) := by
  constructor
  · intro i
    rw [drop_digits_apply]
    exact canonical.1 (offset + i)
  · intro i hi
    rw [drop_digits_apply] at hi ⊢
    simpa [Nat.add_assoc] using canonical.2 (offset + i) hi

private theorem canonical_erase {r : RawDigits} (canonical : CanonicalRaw r)
    (erased : Nat) : CanonicalRaw (r.erase erased) := by
  constructor
  · intro i
    by_cases hi : i = erased
    · subst i
      simp
    · rw [Finsupp.erase_ne hi]
      exact canonical.1 i
  · intro i hi
    by_cases hie : i = erased
    · subst i
      simp at hi
    · rw [Finsupp.erase_ne hie] at hi
      by_cases hnext : i + 1 = erased
      · subst erased
        simp
      · rw [Finsupp.erase_ne hnext]
        exact canonical.2 i hi

/--
A nonzero canonical raw W string has exactly one of the three least-digit forms:
no digit below position two, the least digit plus a two-place shift, or the second
digit plus a three-place shift. In every branch the canonical tail is unique.
-/
theorem canonical_raw_least_digit_decomposition (r : RawDigits)
    (canonical : CanonicalRaw r) (nonzero : r ≠ 0) :
    ((r 0 = 0 ∧ r 1 = 0) ∧
        ExistsUnique fun tail : RawDigits =>
          tail ≠ 0 ∧ CanonicalRaw tail ∧ r = shiftDigits 2 tail) ∨
      ((r 0 = 1 ∧ r 1 = 0) ∧
        ExistsUnique fun tail : RawDigits =>
          CanonicalRaw tail ∧ r = Finsupp.single 0 1 + shiftDigits 2 tail) ∨
      ((r 0 = 0 ∧ r 1 = 1) ∧
        ExistsUnique fun tail : RawDigits =>
          CanonicalRaw tail ∧ r = Finsupp.single 1 1 + shiftDigits 3 tail) := by
  by_cases hzero : r 0 = 0
  · by_cases hone : r 1 = 0
    · left
      refine ⟨⟨hzero, hone⟩, ?_⟩
      let tail := dropDigits 2 r
      have hshift : shiftDigits 2 tail = r := by
        apply shift_drop_digits_eq
        intro i hi
        have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl <;> assumption
      have htail_nonzero : tail ≠ 0 := by
        intro h
        rw [h, shiftDigits] at hshift
        simp at hshift
        exact nonzero hshift.symm
      refine ⟨tail, ⟨htail_nonzero, canonical_drop_digits canonical 2, hshift.symm⟩, ?_⟩
      intro other hother
      apply shift_digits_injective 2
      exact hother.2.2.symm.trans hshift.symm
    · right
      right
      have hone_one : r 1 = 1 := by
        have hone_le := canonical.1 1
        omega
      refine ⟨⟨hzero, hone_one⟩, ?_⟩
      let rest := r.erase 1
      let tail := dropDigits 3 rest
      have htwo : r 2 = 0 := canonical.2 1 hone_one
      have hshift : shiftDigits 3 tail = rest := by
        apply shift_drop_digits_eq
        intro i hi
        have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases this with rfl | rfl | rfl
        · simp [rest, hzero]
        · simp [rest]
        · simp [rest, htwo]
      have hrecompose : r = Finsupp.single 1 1 + shiftDigits 3 tail := by
        calc
          r = rest + Finsupp.single 1 (r 1) := (Finsupp.erase_add_single 1 r).symm
          _ = rest + Finsupp.single 1 1 := by rw [hone_one]
          _ = Finsupp.single 1 1 + shiftDigits 3 tail := by rw [hshift, add_comm]
      refine ⟨tail, ⟨canonical_drop_digits (canonical_erase canonical 1) 3,
        hrecompose⟩, ?_⟩
      intro other hother
      apply shift_digits_injective 3
      apply add_left_cancel (a := Finsupp.single 1 1)
      exact hother.2.symm.trans hrecompose
  · right
    left
    have hzero_one : r 0 = 1 := by
      have hzero_le := canonical.1 0
      omega
    have hone : r 1 = 0 := canonical.2 0 hzero_one
    refine ⟨⟨hzero_one, hone⟩, ?_⟩
    let rest := r.erase 0
    let tail := dropDigits 2 rest
    have hshift : shiftDigits 2 tail = rest := by
      apply shift_drop_digits_eq
      intro i hi
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl
      · simp [rest]
      · simp [rest, hone]
    have hrecompose : r = Finsupp.single 0 1 + shiftDigits 2 tail := by
      calc
        r = rest + Finsupp.single 0 (r 0) := (Finsupp.erase_add_single 0 r).symm
        _ = rest + Finsupp.single 0 1 := by rw [hzero_one]
        _ = Finsupp.single 0 1 + shiftDigits 2 tail := by rw [hshift, add_comm]
    refine ⟨tail, ⟨canonical_drop_digits (canonical_erase canonical 0) 2,
      hrecompose⟩, ?_⟩
    intro other hother
    apply shift_digits_injective 2
    apply add_left_cancel (a := Finsupp.single 0 1)
    exact hother.2.symm.trans hrecompose

#print axioms canonical_raw_least_digit_decomposition

end D5.S1.Digit.Admissibility.LeastDigitDecomposition
