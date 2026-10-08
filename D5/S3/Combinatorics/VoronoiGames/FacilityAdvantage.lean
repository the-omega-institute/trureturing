/- GID: D5/S3/Combinatorics/VoronoiGames/FacilityAdvantage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VoronoiGames/FacilityAdvantage
   mirror-E: none(waiver:named-conjecture-refutation)
   anchors: []
   utility: none
   digest: The separated nine-voter family refutes Maharaj's facility advantage conjecture. -/

import D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageAmplification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VoronoiGames.FacilityAdvantage

open FacilityAdvantageDefs FacilityAdvantageAmplification

/-- Maharaj's Conjecture 1 fails at ten responding facilities. -/
theorem result : ¬ FacilityAdvantageDefs.claim := by
  intro hclaim
  have hstar : kStar 10 = 11 := hclaim 10 (by decide)
  have hs : {k : ℕ | 1 ≤ k ∧ ∀ V : Multiset ℝ,
      V.card ≤ 2 * gameValue k 10 V}.Nonempty :=
    Nat.nonempty_of_sInf_eq_succ (k := 10) hstar
  have hmem := Nat.sInf_mem hs
  have hgood := hmem.2 (voters 5)
  change (voters 5).card ≤ 2 * gameValue (kStar 10) 10 (voters 5) at hgood
  rw [hstar] at hgood
  have hbad : 2 * gameValue 11 10 (voters 5) < (voters 5).card :=
    family_bound 5 11 (by decide) (by decide)
  exact (Nat.not_le_of_gt hbad) hgood

end D5.S3.Combinatorics.VoronoiGames.FacilityAdvantage
