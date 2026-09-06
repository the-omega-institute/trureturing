/- GID: D5/S3/PrimeGaps/PrimeGap186TwoAxisAssembly
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Instantiate the generic DHL-versus-diameter decomposition with the certified forty-point window of width 186. -/

import D5.S3.PrimeGaps.DHLAdmissibleDiameterTransfer
import D5.S3.PrimeGaps.PrimeGap186AdmissibilityCertificate

namespace D5.S3.PrimeGaps.PrimeGap186TwoAxisAssembly

open D5.S3.PrimeGaps.DHLAdmissibleDiameterTransfer
open D5.S3.PrimeGaps.PrimeGap186FiniteFrontEnd
open D5.S3.PrimeGaps.PrimeGap186AdmissibilityCertificate

/-- The natural presentation of the explicit tuple satisfies the generic direct admissibility
contract. -/
theorem admissibleTuple186_natural_admissible :
    NaturalTupleAdmissible admissibleTuple186 := by
  intro p hp
  obtain ⟨a, ha⟩ := admissibleTuple186_is_admissible p hp
  refine ⟨a, ?_⟩
  intro h hh
  have hint : Int.ofNat h ∈ admissibleTuple186Int := by
    unfold admissibleTuple186Int
    exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
  simpa using ha (Int.ofNat h) hint

/-- The combinatorial axis of the 186 result is fully closed inside trureturing: forty directly
admissible natural offsets fit in a normalized window of width 186. -/
theorem admissibleWindowWitness_40_186 :
    AdmissibleWindowWitness 40 186 :=
  ⟨admissibleTuple186,
    admissibleTuple186_card,
    admissibleTuple186_natural_admissible,
    admissibleTuple186_le_186⟩

/-- Therefore any independent proof of the generic natural `DHL[40,2]` contract immediately
produces arbitrarily late consecutive prime gaps of width at most 186. This isolates the exact
remaining analytic burden from the now-closed combinatorial diameter layer. -/
theorem dhl40TwoNat_yields_gap186
    (hdhl : DHLTwoNat 40) :
    ArbitrarilyLateConsecutiveGap 186 :=
  dhl_two_and_admissible_window_yield_bounded_gap 40 186 hdhl
    admissibleWindowWitness_40_186

#print axioms admissibleTuple186_natural_admissible
#print axioms admissibleWindowWitness_40_186
#print axioms dhl40TwoNat_yields_gap186

end D5.S3.PrimeGaps.PrimeGap186TwoAxisAssembly
