import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

namespace LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
universe u v w

/-- Law variation ranges over one registered signature, never over bridges. -/
def FiniteLawVariation (A : PrimitiveLawArena.{u, v, w}) : Prop :=
  ∃ r r' : PrimitiveRealization A.signature, A.Law r ∧ ¬ A.Law r'

/-- Exact generated slot support: changing just this readout can change Law.
Anchors are held fixed, so a witness cannot borrow a different primitive. -/
def FiniteSlotSensitivity (A : PrimitiveLawArena.{u, v, w}) : Prop :=
  (∀ i : A.signature.Index, ∃ r r' : PrimitiveRealization A.signature,
    (∀ j, j ≠ i → r.readout j = r'.readout j) ∧
    (∀ j, r.anchor j = r'.anchor j) ∧ (A.Law r ↔ ¬ A.Law r')) ∧
  (∀ i : A.signature.AnchorIndex, ∃ r r' : PrimitiveRealization A.signature,
    (∀ j, r.readout j = r'.readout j) ∧
    (∀ j, j ≠ i → r.anchor j = r'.anchor j) ∧ (A.Law r ↔ ¬ A.Law r'))

end LeanInformationAudit
