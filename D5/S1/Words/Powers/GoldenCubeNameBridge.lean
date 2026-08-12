/- GID: D5/S1/Words/Powers/GoldenCubeNameBridge
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Golden cube root lengths are exactly the golden name level cardinalities. -/

import D5.S1.Words.Powers.GoldenCubeExistence
import D5.S0.Tower.GoldenGapFrequency

namespace D5.S1.Words.Powers

open D5.S1.Words
open D5.S0.Tower.GoldenNames
open D5.S0.Tower.GoldenGapFrequency

/-! ### Cube root lengths as tower level sizes

`golden_cube_root_length_iff_fib` classifies the lengths of golden cube roots as the
Fibonacci numbers `Nat.fib Q` with `4 ≤ Q`.  The naming tower counts its level-`Q` names by
`golden_name_card : Fintype.card (GoldenName Q) = Nat.fib (Q + 2)`.  The two statements index
the same Fibonacci sequence two apart, so the word-combinatorial classification is exactly the
sequence of tower level sizes, and the threshold `4 ≤ Q` becomes `2 ≤ Q` on the naming side.

This module carries only that index shift; both halves are already frozen.  It is a bridge
between two existing classifications, not a new theorem, and the shift is the entire content:
the cube side supplies no information about names, and the naming side supplies none about
words.  Nothing here asserts a structural correspondence between a cube root of length `n` and
any particular level-`Q` name -- only that the two cardinal sequences coincide.

The geometric restatement uses `golden_full_gap_counts`, which splits a level into its large
and small full gaps.  It is the same cardinal read off the gap geometry rather than off the
name set. -/

/-- Some nonempty word of length `n` occurs three times in a row in the golden word. -/
def IsGoldenCubeRootLength (n : Nat) : Prop :=
  ∃ i u, u ≠ [] ∧ u.length = n ∧ IsGoldenPowerFactor 3 u i

theorem isGoldenCubeRootLength_iff (n : Nat) :
    IsGoldenCubeRootLength n ↔
      ∃ i u, u ≠ [] ∧ u.length = n ∧ IsGoldenPowerFactor 3 u i :=
  Iff.rfl

/-- **The tower geometry bridge.** The golden cube root lengths are exactly the cardinalities
of the golden name levels `Q ≥ 2`. -/
theorem golden_cube_root_length_iff_name_card (n : Nat) :
    IsGoldenCubeRootLength n ↔ ∃ Q, 2 ≤ Q ∧ n = Fintype.card (GoldenName Q) := by
  rw [isGoldenCubeRootLength_iff, golden_cube_root_length_iff_fib]
  constructor
  · rintro ⟨Q, hQ, hn⟩
    refine ⟨Q - 2, by omega, ?_⟩
    rw [golden_name_card, hn]
    congr 1
    omega
  · rintro ⟨Q, hQ, hn⟩
    refine ⟨Q + 2, by omega, ?_⟩
    rw [hn, golden_name_card]

/-- The same bridge read off the gap geometry: a cube root length is a full-gap count. -/
theorem golden_cube_root_length_iff_gap_counts (n : Nat) :
    IsGoldenCubeRootLength n ↔ ∃ Q, 2 ≤ Q ∧ n = largeGapCount Q + smallGapCount Q := by
  rw [golden_cube_root_length_iff_name_card]
  constructor
  · rintro ⟨Q, hQ, hn⟩
    exact ⟨Q, hQ, hn.trans ((golden_full_gap_counts Q hQ).2.2).symm⟩
  · rintro ⟨Q, hQ, hn⟩
    exact ⟨Q, hQ, hn.trans (golden_full_gap_counts Q hQ).2.2⟩

/-- Every golden cube root has length at least `3`, the smallest level cardinality. -/
theorem three_le_of_isGoldenCubeRootLength {n : Nat} (h : IsGoldenCubeRootLength n) : 3 ≤ n := by
  rw [isGoldenCubeRootLength_iff, golden_cube_root_length_iff_fib] at h
  obtain ⟨Q, hQ, hn⟩ := h
  have hmono : Nat.fib 4 ≤ Nat.fib Q := Nat.fib_mono hQ
  have h4 : Nat.fib 4 = 3 := by decide
  omega

/-! ### Regression anchors

The four smallest level cardinalities, checked against `Nat.fib` by the kernel, together with
the cube root lengths they name.  The offset is visible here: level `2` has `3` names, and `3`
is `Nat.fib 4`, the smallest cube root length. -/

private theorem golden_name_card_small :
    Fintype.card (GoldenName 2) = 3 ∧ Fintype.card (GoldenName 3) = 5 ∧
      Fintype.card (GoldenName 4) = 8 ∧ Fintype.card (GoldenName 5) = 13 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [golden_name_card] <;> decide

private theorem golden_cube_root_length_small :
    IsGoldenCubeRootLength 3 ∧ IsGoldenCubeRootLength 5 ∧
      IsGoldenCubeRootLength 8 ∧ IsGoldenCubeRootLength 13 := by
  obtain ⟨h2, h3, h4, h5⟩ := golden_name_card_small
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [golden_cube_root_length_iff_name_card]
  · exact ⟨2, by omega, h2.symm⟩
  · exact ⟨3, by omega, h3.symm⟩
  · exact ⟨4, by omega, h4.symm⟩
  · exact ⟨5, by omega, h5.symm⟩

/-- The classification is not vacuous in the negative direction either: `4` is not a level
cardinality, so no nonempty word of length `4` occurs three times in a row. -/
private theorem golden_cube_root_length_four_false : ¬ IsGoldenCubeRootLength 4 := by
  rw [isGoldenCubeRootLength_iff, golden_cube_root_length_iff_fib]
  rintro ⟨Q, hQ, hn⟩
  rcases Nat.lt_or_ge Q 5 with hlt | hge
  · have hQ4 : Q = 4 := by omega
    subst hQ4
    have h4 : Nat.fib 4 = 3 := by decide
    omega
  · have hmono : Nat.fib 5 ≤ Nat.fib Q := Nat.fib_mono hge
    have h5 : Nat.fib 5 = 5 := by decide
    omega

#print axioms golden_cube_root_length_iff_name_card
#print axioms golden_cube_root_length_iff_gap_counts
#print axioms three_le_of_isGoldenCubeRootLength

end D5.S1.Words.Powers
