/- GID: D5/S1/Phase/StationingCounts
   generality: G
   mirror-B: none(waiver:blueprint-moved-to-depth-capacity-bucket)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact support and occupancy counts for labeled Boolean stationings. -/

import D5.S1.Phase.SeatTowerCombinatorics
import Mathlib.Data.Fintype.Powerset

namespace D5.S1.Phase.StationingCounts

open SeatTowerCombinatorics

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

end D5.S1.Phase.StationingCounts
