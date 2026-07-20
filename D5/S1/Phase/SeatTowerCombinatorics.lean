/- GID: D5/S1/Phase/SeatTowerCombinatorics
   generality: G
   mirror-B: D5/B/S1/Phase/SeatTowerCombinatorics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact parity and finite-counting skeletons for mirror stationing. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace D5.S1.Phase.SeatTowerCombinatorics

open scoped BigOperators

/-- Reversal in an even-length cycle swaps the parity of an in-range index. -/
theorem reversal_swaps_parity (halfLength index : Nat)
    (hIndex : index < 2 * halfLength) :
    (2 * halfLength - 1 - index) % 2 = 1 - index % 2 := by
  omega

/-- If a rotation has the same parity action as reversal, its offset is odd. -/
theorem matching_rotation_offset_is_odd (halfLength index offset : Nat)
    (hIndex : index < 2 * halfLength)
    (hMatch : (2 * halfLength - 1 - index) % 2 = (index + offset) % 2) :
    offset % 2 = 1 := by
  have hReverse := reversal_swaps_parity halfLength index hIndex
  omega

/-- Even labeled offsets in a cycle of length `2 * halfLength`. -/
def EvenOffset (halfLength : Nat) := {offset : Fin (2 * halfLength) // Even offset.val}

/-- Halving and doubling identify the even offsets with `Fin halfLength`. -/
def evenOffsetEquiv (halfLength : Nat) : Fin halfLength ≃ EvenOffset halfLength where
  toFun index :=
    ⟨⟨2 * index.val, (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 index.isLt⟩,
      ⟨index.val, by
        change 2 * index.val = index.val + index.val
        omega⟩⟩
  invFun offset := ⟨offset.val / 2, by
    rcases offset.property with ⟨value, hValue⟩
    omega⟩
  left_inv index := by
    apply Fin.ext
    simp
  right_inv offset := by
    apply Subtype.ext
    apply Fin.ext
    rcases offset.property with ⟨value, hValue⟩
    dsimp
    omega

instance evenOffsetFintype (halfLength : Nat) : Fintype (EvenOffset halfLength) :=
  Fintype.ofEquiv (Fin halfLength) (evenOffsetEquiv halfLength)

/-- Exactly half of the labeled offsets in an even cycle are even. -/
theorem even_offset_skeleton_count (halfLength : Nat) :
    Fintype.card (EvenOffset halfLength) = halfLength := by
  rw [Fintype.card_congr (evenOffsetEquiv halfLength).symm]
  exact Fintype.card_fin halfLength

/-- Independent exponent allocations have the product of their local capacities. -/
theorem full_exponent_stationing_count (primeCount : Nat)
    (exponent : Fin primeCount -> Nat) :
    Fintype.card ((index : Fin primeCount) -> Fin (exponent index + 1)) =
      ∏ index, (exponent index + 1) := by
  simp

/-- A labeled two-side stationing. -/
abbrev Stationing (count : Nat) := Fin count -> Bool

/-- Pointwise exchange of the two stationing sides. -/
def mirrorStationing {count : Nat} (stationing : Stationing count) : Stationing count :=
  fun index => !stationing index

/-- A mirror-pair representative fixes the distinguished side to `false`. -/
def IsMirrorRepresentative {freeCount : Nat} (stationing : Stationing (freeCount + 1)) : Prop :=
  stationing 0 = false

/-- Select the member of a mirror pair whose distinguished side is `false`. -/
def normalizeMirror {freeCount : Nat} (stationing : Stationing (freeCount + 1)) :
    Stationing (freeCount + 1) :=
  if stationing 0 then mirrorStationing stationing else stationing

/-- Normalization is the unique representative among a stationing and its mirror. -/
theorem mirror_normalization_is_unique {freeCount : Nat}
    (stationing : Stationing (freeCount + 1)) :
    IsMirrorRepresentative (normalizeMirror stationing) ∧
      (normalizeMirror stationing = stationing ∨
        normalizeMirror stationing = mirrorStationing stationing) ∧
      ∀ representative,
        IsMirrorRepresentative representative ->
        (representative = stationing ∨ representative = mirrorStationing stationing) ->
        representative = normalizeMirror stationing := by
  cases hSide : stationing 0 with
  | false =>
      have hNormalize : normalizeMirror stationing = stationing := by
        simp [normalizeMirror, hSide]
      refine ⟨?_, ⟨Or.inl hNormalize, ?_⟩⟩
      · simpa [IsMirrorRepresentative, hNormalize] using hSide
      · intro representative hRepresentative hOrbit
        rw [hNormalize]
        rcases hOrbit with hEqual | hEqual
        · exact hEqual
        · subst representative
          simp [IsMirrorRepresentative, mirrorStationing, hSide] at hRepresentative
  | true =>
      have hNormalize : normalizeMirror stationing = mirrorStationing stationing := by
        simp [normalizeMirror, hSide]
      refine ⟨?_, ⟨Or.inr hNormalize, ?_⟩⟩
      · simp [IsMirrorRepresentative, hNormalize, mirrorStationing, hSide]
      · intro representative hRepresentative hOrbit
        rw [hNormalize]
        rcases hOrbit with hEqual | hEqual
        · subst representative
          simp [IsMirrorRepresentative, hSide] at hRepresentative
        · exact hEqual

/-- A representative is determined freely by all coordinates after the first. -/
def mirrorRepresentativeEquiv (freeCount : Nat) :
    {stationing : Stationing (freeCount + 1) // IsMirrorRepresentative stationing} ≃
      Stationing freeCount where
  toFun stationing index := stationing.val index.succ
  invFun tail := ⟨(fun index => Fin.cases false tail index : Stationing (freeCount + 1)), by
    rfl⟩
  left_inv stationing := by
    apply Subtype.ext
    funext index
    refine Fin.cases ?_ (fun _ => rfl) index
    exact stationing.property.symm
  right_inv tail := by
    funext index
    rfl

instance mirrorRepresentativeFintype (freeCount : Nat) :
    Fintype {stationing : Stationing (freeCount + 1) // IsMirrorRepresentative stationing} :=
  Fintype.ofEquiv (Stationing freeCount) (mirrorRepresentativeEquiv freeCount).symm

/-- Fixing one side leaves exactly `2 ^ freeCount` mirror representatives. -/
theorem mirror_representative_count (freeCount : Nat) :
    Fintype.card
        {stationing : Stationing (freeCount + 1) // IsMirrorRepresentative stationing} =
      2 ^ freeCount := by
  rw [Fintype.card_congr (mirrorRepresentativeEquiv freeCount)]
  simp [Stationing]

end D5.S1.Phase.SeatTowerCombinatorics
