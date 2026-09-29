/- GID: D5/S3/ConceptDynamics/InformationEscape/DependentFamily
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/DependentFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Source-bound audits use finite roles on arbitrary dependent state and output families. -/

import D5.S3.ConceptDynamics.InformationEscapeHierarchy.StructuralArena

namespace D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe t s r o a

/-- Only roles and anchors are finite. Parameters, states and outputs need not be. -/
structure Signature where
  Params : Type t
  State : Params → Type s
  Role : Type r
  finiteRole : Fintype Role
  nonemptyRole : Nonempty Role
  Output : Role → Params → Type o
  Anchor : Type a
  finiteAnchor : Fintype Anchor

structure Realization (S : Signature.{t,s,r,o,a}) where
  readout : ∀ role p, S.State p → S.Output role p
  anchor : ∀ (_ : S.Anchor) p, S.State p

/-- The common template transports typed mathematical operands without interpreting them. -/
def realize (S : Signature.{t,s,r,o,a})
    (readout : ∀ role p, S.State p → S.Output role p)
    (anchor : ∀ (_ : S.Anchor) p, S.State p) : Realization S := ⟨readout, anchor⟩

structure Arena where
  signature : Signature.{t,s,r,o,a}
  Law : Realization signature → Prop

/-- Interventions vary whole families. No obligation demands variation in every fiber. -/
def Variation (A : Arena.{t,s,r,o,a}) (actual : Realization A.signature) : Prop :=
  A.Law actual ∧ ∃ bad, ¬ A.Law bad

/-- Every role changes the law with all other roles and anchors fixed at actual. -/
def Sensitivity (A : Arena.{t,s,r,o,a}) (actual : Realization A.signature) : Prop :=
  (∀ i, ∃ bad : Realization A.signature,
    (∀ j, j ≠ i → actual.readout j = bad.readout j) ∧
    actual.anchor = bad.anchor ∧ ¬ A.Law bad) ∧
  (∀ i, ∃ bad : Realization A.signature,
    actual.readout = bad.readout ∧
    (∀ j, j ≠ i → actual.anchor j = bad.anchor j) ∧ ¬ A.Law bad)

/-- Hypothetical law variation cannot give a constant actual readout legitimacy. -/
def ObservationalDependence (S : Signature.{t,s,r,o,a}) (actual : Realization S) : Prop :=
  ∀ i, ∃ p x y, actual.readout i p x ≠ actual.readout i p y

/-- Kernel obligations complement the producer's complete raw source reconstruction,
scope/coordinate checks and exact occurrence ties. This record grants no enrollment. -/
structure Registration (A : Arena.{t,s,r,o,a}) (statement : Prop) where
  actual : Realization A.signature
  bridge : statement ↔ A.Law actual
  variation : Variation A actual
  sensitivity : Sensitivity A actual
  dependence : ObservationalDependence A.signature actual

end D5.S3.ConceptDynamics.InformationEscape.DependentFamily
