/- GID: D5/S3/PrimeGaps/LocalGlobalOccupancySeparation
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exhibit an admissible two-offset pattern whose translated prime occupancy can be both zero and two. -/

import D5.S3.PrimeGaps.DHLAdmissibleDiameterTransfer
import D5.S3.PrimeGaps.PrimeGapAdmissibilityContractBridge

namespace D5.S3.PrimeGaps.LocalGlobalOccupancySeparation

open D5.S3.PrimeGaps.ShortGapOccupancyBridge
open D5.S3.PrimeGaps.PrimeGapAdmissibilityContractBridge
open D5.S3.PrimeGaps.DHLAdmissibleDiameterTransfer

/-- The normalized twin-offset window. -/
def twinOffsets : Finset Nat := {0, 2}

/-- Integer presentation of the same two offsets. -/
def twinOffsetsInt : Finset Int := {0, 2}

/-- The twin-offset pattern passes every local residue obstruction. -/
theorem twinOffsetsInt_direct_admissible : DirectTupleAdmissible twinOffsetsInt := by
  rw [directTupleAdmissible_iff_local_residue]
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  by_cases h2 : p = 2
  · subst p
    norm_num [localResidueCount, localResidueSet, twinOffsetsInt]
  · have hp3 : 3 ≤ p := by
      omega
    calc
      localResidueCount twinOffsetsInt p ≤ twinOffsetsInt.card := by
        unfold localResidueCount localResidueSet
        exact Finset.card_image_le
      _ = 2 := by decide
      _ < p := hp3

/-- The natural twin-offset presentation is likewise admissible. -/
theorem twinOffsets_natural_admissible : NaturalTupleAdmissible twinOffsets := by
  intro p hp
  obtain ⟨a, ha⟩ := twinOffsetsInt_direct_admissible p hp
  refine ⟨a, ?_⟩
  intro h hh
  interval_cases h <;>
    simp [twinOffsets, twinOffsetsInt] at hh ⊢
  · simpa using ha 0 (by simp [twinOffsetsInt])
  · simpa using ha 2 (by simp [twinOffsetsInt])

/-- At translation `n = 3`, both positions are prime. -/
theorem twinOffsets_occupancy_two :
    primeTranslateOccupancy twinOffsets 3 = 2 := by
  decide

/-- At translation `n = 8`, neither position is prime. -/
theorem twinOffsets_occupancy_zero :
    primeTranslateOccupancy twinOffsets 8 = 0 := by
  decide

/-- Local admissibility does not determine pointwise translated prime occupancy. The same
admissible offset geometry realizes both the maximal two-hit state and the zero-hit state at
different translates. Consequently the DHL local-to-global step contains genuinely additional
analytic/distributional information. -/
theorem admissibility_does_not_fix_translate_occupancy :
    NaturalTupleAdmissible twinOffsets ∧
      primeTranslateOccupancy twinOffsets 3 = 2 ∧
      primeTranslateOccupancy twinOffsets 8 = 0 :=
  ⟨twinOffsets_natural_admissible, twinOffsets_occupancy_two, twinOffsets_occupancy_zero⟩

#print axioms twinOffsets
#print axioms twinOffsetsInt
#print axioms twinOffsetsInt_direct_admissible
#print axioms twinOffsets_natural_admissible
#print axioms twinOffsets_occupancy_two
#print axioms twinOffsets_occupancy_zero
#print axioms admissibility_does_not_fix_translate_occupancy

end D5.S3.PrimeGaps.LocalGlobalOccupancySeparation
