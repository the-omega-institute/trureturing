/- GID: D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/CyclicStackFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded recursive stack laws share their actual process readout. -/

import D5.S1.Words.Patterns.CyclicStackPreimagesCore
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open D5.S1.Words.Patterns.CyclicStackPreimages
open DependentFamily

def signature : Signature where
  Params := List ℕ
  State := fun _ => List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ input stack => process input stack) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

def runArena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ input stack, r.readout () input stack = (run input stack).1 ++ (run input stack).2

def permArena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ (input stack : List ℕ), (r.readout () input stack).Perm (input ++ stack)

end D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
