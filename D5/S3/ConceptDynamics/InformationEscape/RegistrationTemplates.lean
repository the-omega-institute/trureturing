/- GID: D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/RegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Typed registration constructors generate primitive inventories and realization-dependent laws on explicit canonical arenas. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

/- The canonical arena is an explicit input. No constructor accepts a Law or a
bundle. Changing a readout changes the generated Law's argument, not its syntax.
Search receipt: TheoremUnit's compiler and ADMIT reflection; Mathlib's Bijective
API. These are presentation constructors, not new proofs of bijection facts. -/

def cutSignature (X Y : Type) [DecidableEq Y] : PrimitiveSignature X where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def cutRealization {X Y : Type} [DecidableEq Y] (f : X → Y) :
    PrimitiveRealization (cutSignature X Y) := ⟨fun _ => f, Fin.elim0⟩

/-- Single-consumer helper in the gold set; all readout functions remain abstract. -/
def bijectiveArena (A : Arena) (Y : Type) [DecidableEq Y] : PrimitiveLawArena where
  toArena := A
  signature := cutSignature A.State Y
  Law := fun r => Function.Bijective (r.readout ())

theorem bijectiveLegacy (A : Arena) {Y : Type} [DecidableEq Y] (f : A.State → Y) :
    LegacyPrimitiveRealization (bijectiveArena A Y) (Function.Bijective f)
      (cutRealization f) := ⟨Iff.rfl⟩

def separationSignature (X Y Z : Type) [DecidableEq Y] [DecidableEq Z] :
    PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output | false => Y | true => Z
  outputDecidableEq := by intro i; cases i <;> infer_instance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def separationRealization {X Y Z : Type} [DecidableEq Y] [DecidableEq Z]
    (coarse : X → Y) (fine : X → Z) : PrimitiveRealization (separationSignature X Y Z) where
  readout | false => coarse | true => fine
  anchor := Fin.elim0

/-- Witness separation, exactly the law shared by the two causal golds. -/
def separationArena (A : Arena) (Y Z : Type) [DecidableEq Y] [DecidableEq Z] :
    PrimitiveLawArena where
  toArena := A
  signature := separationSignature A.State Y Z
  Law := fun r => ∃ x y, r.readout false x = r.readout false y ∧
    r.readout true x ≠ r.readout true y

theorem separationLegacy (A : Arena) {Y Z : Type} [DecidableEq Y] [DecidableEq Z]
    (coarse : A.State → Y) (fine : A.State → Z) :
    LegacyPrimitiveRealization (separationArena A Y Z)
      (∃ x y, coarse x = coarse y ∧ fine x ≠ fine y)
      (separationRealization coarse fine) := ⟨Iff.rfl⟩

end D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
