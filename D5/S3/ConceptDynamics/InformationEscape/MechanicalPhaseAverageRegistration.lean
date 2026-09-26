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
import D5.S3.ConceptDynamics.InformationEscape.MechanicalReadoutSources

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration

open Set MeasureTheory
open D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
open D5.S3.ConceptDynamics.InformationEscape
open PointwiseRegistrationTemplates

/-- The hypotheses under which the atomic phase average is a volume. -/
abbrev PhaseAverageInput := MechanicalReadoutSources.PhaseAverageInput

def phaseAverageIntegral (input : PhaseAverageInput) : ENNReal :=
  MechanicalReadoutSources.phaseAverageIntegral input

def phaseAverageVolume (input : PhaseAverageInput) : ENNReal :=
  MechanicalReadoutSources.phaseAverageVolume input

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
    (fun _ : Unit => MechanicalReadoutSources.phaseAverageIntegral)
    (fun _ : Unit => MechanicalReadoutSources.phaseAverageVolume)

end D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration
