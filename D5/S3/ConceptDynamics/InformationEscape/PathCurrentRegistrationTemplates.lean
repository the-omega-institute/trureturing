/- GID: D5/S3/ConceptDynamics/InformationEscape/PathCurrentRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/PathCurrentRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A real path-statistic observation family over signed state spaces with a peak. -/

import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Mathlib.Data.Real.Basic

namespace D5.S3.ConceptDynamics.InformationEscape.PathCurrentRegistrationTemplates

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

/-- A finite role observes one real statistic of a path in a signed state space. The parameters
are the state type, the sign function, the peak, two profile values, the normalizer and the
horizon; the state is the whole path. -/
def signedPeakPathSignature : Signature where
  Params := Σ X : Type u, Σ _ : X → ℝ, Σ _ : X, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℕ
  State := fun p => ℕ → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

end D5.S3.ConceptDynamics.InformationEscape.PathCurrentRegistrationTemplates
