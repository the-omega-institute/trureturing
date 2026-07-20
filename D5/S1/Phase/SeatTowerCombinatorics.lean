/- GID: D5/S1/Phase/SeatTowerCombinatorics
   generality: G
   mirror-B: D5/B/S1/Phase/SeatTowerCombinatorics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact parity and finite-counting skeletons for mirror stationing. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
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

/-- The labeled stations assigned to the `true` side. -/
def occupiedStations {count : Nat} (stationing : Stationing count) : Finset (Fin count) :=
  Finset.univ.filter fun index => stationing index = true

/-- Boolean stationings are equivalent to their finite occupied supports. -/
def stationingSupportEquiv (count : Nat) : Stationing count ≃ Finset (Fin count) where
  toFun := occupiedStations
  invFun support index := decide (index ∈ support)
  left_inv stationing := by
    funext index
    cases hValue : stationing index <;> simp [occupiedStations, hValue]
  right_inv support := by
    ext index
    simp [occupiedStations]

/-- Restricting the support equivalence preserves a prescribed occupancy. -/
def occupiedCountEquiv (count occupiedCount : Nat) :
    {stationing : Stationing count //
        (occupiedStations stationing).card = occupiedCount} ≃
      {support : Finset (Fin count) // support.card = occupiedCount} :=
  (stationingSupportEquiv count).subtypeEquiv fun _ => Iff.rfl

/-- There are two independent side choices at every labeled station. -/
theorem stationing_count (count : Nat) :
    Fintype.card (Stationing count) = 2 ^ count := by
  simp [Stationing]

/-- Mirroring a stationing complements its occupied support. -/
theorem occupied_stations_mirror {count : Nat} (stationing : Stationing count) :
    occupiedStations (mirrorStationing stationing) =
      Finset.univ \ occupiedStations stationing := by
  ext index
  cases hValue : stationing index <;>
    simp [occupiedStations, mirrorStationing, hValue]

/-- The occupied count of a mirror is the complementary count. -/
theorem mirror_occupied_count {count : Nat} (stationing : Stationing count) :
    (occupiedStations (mirrorStationing stationing)).card =
      count - (occupiedStations stationing).card := by
  rw [occupied_stations_mirror, Finset.card_sdiff]
  simp

/-- Pointwise Boolean mirroring has no fixed stationing on a nonempty station set. -/
theorem mirror_stationing_ne_self {count : Nat} (hCount : 0 < count)
    (stationing : Stationing count) :
    mirrorStationing stationing ≠ stationing := by
  intro hFixed
  have hAtZero := congrFun hFixed (⟨0, hCount⟩ : Fin count)
  cases hValue : stationing (⟨0, hCount⟩ : Fin count) <;>
    simp [mirrorStationing, hValue] at hAtZero

/-- Prescribing exactly `occupiedCount` occupied labeled stations gives a binomial layer. -/
theorem occupied_count_stationing_count (count occupiedCount : Nat) :
    Fintype.card
        {stationing : Stationing count //
          (occupiedStations stationing).card = occupiedCount} =
      Nat.choose count occupiedCount := by
  rw [Fintype.card_congr (occupiedCountEquiv count occupiedCount)]
  simp

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
