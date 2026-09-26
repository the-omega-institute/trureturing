/- GID: D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicSeriesRegistration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/MechanicalAtomicSeriesRegistration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One infinite-parameter readout records the floor series, coefficient mass, and threshold expansion. -/

import D5.S1.Words.Mechanical.MechanicalReadoutAtomicSeries
import D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration

open Set Finset
open scoped BigOperators
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalReadoutOrder
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration

abbrev SeriesOutput :=
  (ℝ → ℝ → ℝ → ℝ) × (ℝ → ℝ) × (ℝ → ℝ → ℝ → ℝ)

/-- The three quantities compared by the atomic-series theorem. -/
def floorSeriesReadout (r alpha x : ℝ) : ℝ :=
  ∑' j : ℕ, (1 - r) ^ 2 * r ^ j *
    (⌊x + ((j + 1 : ℕ) : ℝ) * alpha⌋ : ℝ)

def coefficientMassReadout (r : ℝ) : ℝ :=
  ∑' j : ℕ, (1 - r) ^ 2 * r ^ j * ((j + 1 : ℕ) : ℝ)

def thresholdSeriesReadout (r alpha x : ℝ) : ℝ :=
  ∑' j : ℕ, (1 - r) ^ 2 * r ^ j *
    (∑ i ∈ range (j + 1),
      if (((i + 1 : ℕ) : ℝ) - x) / ((j + 1 : ℕ) : ℝ) ≤ alpha then
        (1 : ℝ) else 0)

def seriesReadout : SeriesOutput :=
  (floorSeriesReadout, coefficientMassReadout, thresholdSeriesReadout)

local instance : DecidableEq SeriesOutput := Classical.decEq _

/-- The single CUT slot carries complete real-parameter functions, including
the total mass rather than treating normalization as an external assumption. -/
def seriesArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := {
    toArena := Arena.ofFintype Unit
    signature := mechanicalReadoutSignature SeriesOutput
    Law := fun realization => ∀ (r alpha x : ℝ), 0 ≤ r → r < 1 →
      alpha ∈ Icc (0 : ℝ) 1 → x ∈ Ico (0 : ℝ) 1 →
        geometricReadout r alpha x = (realization.readout () ()).1 r alpha x ∧
        (realization.readout () ()).2.1 r = 1 ∧
        geometricReadout r alpha x = (realization.readout () ()).2.2 r alpha x
  }
  Domain := ℝ

def seriesRealization :=
  @mechanicalReadoutRealization SeriesOutput (Classical.decEq _)
    (fun _ : Unit => seriesReadout)

end D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicSeriesRegistration
