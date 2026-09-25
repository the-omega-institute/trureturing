/- GID: D5/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/MechanicalPhaseAverageRegistration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Phase averaging and volume are compared as functions on admissible real parameters and measurable sets. -/

import D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration

open Set MeasureTheory
open D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
open D5.S3.ConceptDynamics.InformationEscape
open PointwiseRegistrationTemplates

/-- The hypotheses under which the atomic phase average is a volume. -/
structure PhaseAverageInput where
  ratio : ℝ
  ratioPositive : 0 < ratio
  ratioBelowOne : ratio < 1
  target : Set ℝ
  targetMeasurable : MeasurableSet target
  targetInUnit : target ⊆ Set.Icc (0 : ℝ) 1

def phaseAverageIntegral (input : PhaseAverageInput) : ENNReal :=
  ∫⁻ x in Set.Ico (0 : ℝ) 1,
    geometricAtomicMeasure input.ratio x input.target ∂volume

def phaseAverageVolume (input : PhaseAverageInput) : ENNReal :=
  volume input.target

abbrev PhaseAverageOutput := PhaseAverageInput → ENNReal

local instance : DecidableEq PhaseAverageOutput := Classical.decEq _

/-- Two CUT roles compare the complete parameterized average and volume functions. -/
def phaseAverageArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := by
    letI : DecidableEq PhaseAverageOutput := Classical.decEq _
    exact homogeneousPointwiseEqArena (Arena.ofFintype Unit) PhaseAverageOutput
  Domain := Set ℝ

def phaseAverageRealization :=
  @homogeneousPointwiseEqRealization Unit PhaseAverageOutput (Classical.decEq _)
    (fun _ : Unit => phaseAverageIntegral)
    (fun _ : Unit => phaseAverageVolume)

end D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration
