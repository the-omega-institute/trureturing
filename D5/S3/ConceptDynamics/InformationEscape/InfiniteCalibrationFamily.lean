/- GID: D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full real calibration existence varies the original real control witness. -/

import D5.S3.Quantum.Information.InfiniteCalibrationControl
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily
open D5.S3.Quantum.Information.InfiniteCalibrationControl
open DependentFamily

def signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (a δ b : ℝ) (_ha : 0 < a) (_ha1 : a < 1)
    (_hδ : 0 < δ) (_hδL : δ < (1-a)/4) (_hδa : δ < (1-a^2)/16)
    (_hb : 0 < b) (_hbδ : b < 1 - a/(1-δ)),
    ∃ k : ℝ, InfiniteScalarControl a δ b (r.readout () ⟨a, δ, b⟩ k)

end D5.S3.ConceptDynamics.InformationEscape.InfiniteCalibrationFamily
