/- GID: D5/S3/ConceptDynamics/Information/SharedSourceLocalIntervention
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Information/SharedSourceLocalIntervention
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixing one coordinate leaves a distinct shared-source coordinate fair and unfixed. -/

import D5.S3.ConceptDynamics.Information.SharedSourceObservationDependence

/- Library-search audit trail (2026-08-26):
   * The exact current-tree hit `conceptLaw` is the canonical finite pushforward
     law and is reused directly for the intervened coordinate.
   * `SharedSourceObservationDependence` proves the observational dependence of
     two copies of one fair Boolean source, but has no local-intervention clause.
   * Repository body-shape searches for a fixed coordinate beside a retained
     shared source found no exact theorem or canonical intervention primitive.
   * Pinned Mathlib searches found finite Boolean and probability infrastructure,
     but no theorem stating this shared-source intervention calculation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Information.SharedSourceLocalIntervention

open D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity
open D5.S3.Entropy.Forgetting.CapacityMonotone

/-- If an intervention fixes the coordinate at `p`, a distinct coordinate `q`
continues to copy the fair Boolean source. Its law stays fair, and it disagrees
with the imposed value with probability one half. -/
theorem local_intervention_exposes_shared_source
    {Address : Type*} [DecidableEq Address]
    (p q : Address) (distinct : p ≠ q) :
    ∀ imposed source observed : Bool,
      (if q = p then imposed else source) = source ∧
        conceptLaw (fun _ : Bool => (1 / 2 : Real))
          (fun source : Bool => if q = p then imposed else source) observed = 1 / 2 ∧
        conceptLaw (fun _ : Bool => (1 / 2 : Real))
          (fun source : Bool =>
            decide ((if q = p then imposed else source) ≠ imposed)) true = 1 / 2 := by
  have q_ne_p : q ≠ p := Ne.symm distinct
  intro imposed source observed
  constructor
  · simp [q_ne_p]
  · constructor
    · simp only [q_ne_p, if_false]
      cases observed <;> norm_num [conceptLaw, pushforward]
    · simp only [q_ne_p, if_false]
      cases imposed <;> norm_num [conceptLaw, pushforward]

#print axioms local_intervention_exposes_shared_source

end D5.S3.ConceptDynamics.Information.SharedSourceLocalIntervention
