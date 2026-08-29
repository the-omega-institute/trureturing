/- GID: D5/S1/Words/Complexity/GoldenSubshiftMinimalAction
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/GoldenSubshiftMinimalAction
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   digest: The forward shift is a monoid action of the naturals on every word-subshift subtype, and under that action the golden subshift carries mathlib's AddAction.IsMinimal instance; iterated shift invariance is restated publicly because both existing derivations are private. -/

import D5.S1.Words.Complexity.GoldenSubshiftMinimality

open Set SymbolicDynamics
open D5.S1.Words.Complexity.SubshiftHausdorffDimension
open D5.S1.Words.Complexity.GoldenSubshiftMinimality

namespace D5.S1.Words.Complexity.GoldenSubshiftMinimalAction

noncomputable section

variable {A : Type*} [Fintype A]

/-- One forward shift keeps a subshift member inside the subshift, phrased for
`FullShift.shift 1` rather than for the explicit index translation. -/
private theorem shift_one_mem {x y : ℕ → A} (hy : y ∈ wordSubshift x) :
    FullShift.shift (1 : ℕ) y ∈ wordSubshift x := by
  have h : FullShift.shift (1 : ℕ) y = fun j ↦ y (j + 1) := by
    funext j
    simp [FullShift.shift, Nat.add_comm]
  rw [h]
  exact wordSubshift_shift_invariant x hy

/-- Every iterated forward shift of a subshift member stays in the subshift.
`GoldenSubshiftMinimality` derives this general form privately, while
`SubshiftTopology` privately derives only the special case where the member is the
generating word itself. Neither is reachable downstream, so the general form is
restated publicly here. -/
theorem shift_mem_wordSubshift {x y : ℕ → A} (hy : y ∈ wordSubshift x) (i : ℕ) :
    FullShift.shift i y ∈ wordSubshift x := by
  induction i with
  | zero => simpa using hy
  | succ n ih =>
      rw [FullShift.shift_add n 1 y]
      exact shift_one_mem ih

/-- The forward shift makes each word subshift a set on which the additive monoid of
naturals acts. Mathlib supplies both action laws for the ambient full shift but
registers no action instance, so the subshift subtype gets one here. -/
instance shiftAddAction (x : ℕ → A) : AddAction ℕ ↥(wordSubshift x) where
  vadd i y := ⟨FullShift.shift i (y : ℕ → A), shift_mem_wordSubshift y.2 i⟩
  zero_vadd y := by
    apply Subtype.ext
    change FullShift.shift (0 : ℕ) (y : ℕ → A) = (y : ℕ → A)
    simp
  add_vadd i j y := by
    apply Subtype.ext
    change FullShift.shift (i + j) (y : ℕ → A)
      = FullShift.shift i (FullShift.shift j (y : ℕ → A))
    rw [Nat.add_comm i j, FullShift.shift_add]

/-- Under the shift action the orbit of a subshift member has, as a subset of the
ambient sequence space, exactly the forward shift orbit of its underlying word. -/
theorem coe_orbit_eq_range (x : ℕ → A) (y : ↥(wordSubshift x)) :
    (Subtype.val '' AddAction.orbit ℕ y)
      = Set.range fun i : ℕ ↦ FullShift.shift i (y : ℕ → A) := by
  ext z
  constructor
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨⟨FullShift.shift i (y : ℕ → A), shift_mem_wordSubshift y.2 i⟩, ⟨i, rfl⟩, rfl⟩

/-- The golden word subshift is a minimal system for the forward shift action, in
mathlib's sense: every orbit is dense in the subtype. Density of the ambient orbit
closure is already frozen; the content added here is the transfer to the subtype
topology together with the instance registration. -/
instance goldenSubshiftIsMinimal :
    AddAction.IsMinimal ℕ ↥(wordSubshift goldenWord) where
  dense_orbit y := by
    rw [Subtype.dense_iff, coe_orbit_eq_range]
    exact le_of_eq (golden_wordSubshift_minimal y.2).symm

end

#print axioms shift_mem_wordSubshift
#print axioms shiftAddAction
#print axioms coe_orbit_eq_range
#print axioms goldenSubshiftIsMinimal

end D5.S1.Words.Complexity.GoldenSubshiftMinimalAction
