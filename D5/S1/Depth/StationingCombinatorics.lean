/- GID: D5/S1/Depth/StationingCombinatorics
   generality: G
   mirror-B: D5/B/S1/Depth/StationingCombinatorics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact support and occupancy counts for labeled Boolean stationings. -/

import D5.S1.Phase.StationingCounts

namespace D5.S1.Depth.StationingCombinatorics

open D5.S1.Phase.SeatTowerCombinatorics
open D5.S1.Phase.StationingCounts

/-- There are two independent side choices at every labeled station. -/
theorem stationing_count (count : Nat) :
    Fintype.card (Stationing count) = 2 ^ count :=
  D5.S1.Phase.StationingCounts.stationing_count count

/-- Mirroring a stationing complements its occupied support. -/
theorem occupied_stations_mirror {count : Nat} (stationing : Stationing count) :
    occupiedStations (mirrorStationing stationing) =
      Finset.univ \ occupiedStations stationing :=
  D5.S1.Phase.StationingCounts.occupied_stations_mirror stationing

/-- The occupied count of a mirror is the complementary count. -/
theorem mirror_occupied_count {count : Nat} (stationing : Stationing count) :
    (occupiedStations (mirrorStationing stationing)).card =
      count - (occupiedStations stationing).card :=
  D5.S1.Phase.StationingCounts.mirror_occupied_count stationing

/-- Pointwise Boolean mirroring has no fixed stationing on a nonempty station set. -/
theorem mirror_stationing_ne_self {count : Nat} (hCount : 0 < count)
    (stationing : Stationing count) :
    mirrorStationing stationing ≠ stationing :=
  D5.S1.Phase.StationingCounts.mirror_stationing_ne_self hCount stationing

/-- Prescribing exactly `occupiedCount` occupied labeled stations gives a binomial layer. -/
theorem occupied_count_stationing_count (count occupiedCount : Nat) :
    Fintype.card
        {stationing : Stationing count //
          (occupiedStations stationing).card = occupiedCount} =
      Nat.choose count occupiedCount :=
  D5.S1.Phase.StationingCounts.occupied_count_stationing_count count occupiedCount

end D5.S1.Depth.StationingCombinatorics
