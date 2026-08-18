/- GID: D5/S0/Tower/DBonacciGeneral/ChampionMidBridge
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/ChampionMidBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The indexed middle coordinate is the general one at the Perron root. -/

import D5.S0.Tower.DBonacciSurvivors.FiniteDepth
import D5.S0.Tower.DBonacciGeneral.ChampionLimit

/- Library-search audit trail (2026-08-18):
   * `championMid d = 1 / (beta d ^ 2 - 1)` landed twenty-three minutes before
     `championMidCoordinate beta = 1 / (beta ^ 2 - 1)` generalised it, and the
     indexed one was frozen by then, so the link could not be made in place.
     Issue 2419 records that; this module is the link.
   * `beta d` in the indexed module already delegates to `dbonacciPerronRoot d`,
     which is what the general module's limit statement is phrased over, so the
     two sides meet without any further definition.
   * Nothing new is proved about the limit; it is transported. -/

namespace D5.S0.Tower.DBonacciGeneral.ChampionMidBridge

open Filter Topology
open D5.S0.Tower.DBonacciSurvivors.DBonacciPermanentSurvivors
open D5.S0.Tower.DBonacciSurvivors.FiniteDepth
open D5.S0.Tower.DBonacciGeneral.ChampionLimit
open D5.S0.Tower.DBonacci.PerronRoot

/-- The indexed middle coordinate is the general one evaluated at the base. -/
theorem championMid_eq (d : Nat) : championMid d = championMidCoordinate (beta d) := rfl

/-- And the base is the Perron root, so the two phrasings agree pointwise. -/
theorem championMid_eq_at_perron_root (d : Nat) :
    championMid d = championMidCoordinate (dbonacciPerronRoot d) := rfl

/-- The limit proved for the general form therefore holds for the indexed one. -/
theorem championMid_tendsto_one_third :
    Tendsto (fun d : Nat => championMid d) atTop (nhds (1 / 3)) := by
  simpa [championMid_eq_at_perron_root] using championMidCoordinate_tendsto_one_third

/-- One value under two names, with the limit carried across. -/
theorem the_two_middle_coordinates_are_one :
    (∀ d : Nat, championMid d = championMidCoordinate (dbonacciPerronRoot d)) ∧
      Tendsto (fun d : Nat => championMid d) atTop (nhds (1 / 3)) :=
  ⟨championMid_eq_at_perron_root, championMid_tendsto_one_third⟩

end D5.S0.Tower.DBonacciGeneral.ChampionMidBridge
