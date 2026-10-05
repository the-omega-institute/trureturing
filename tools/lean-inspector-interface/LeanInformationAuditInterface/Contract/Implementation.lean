import LeanInformationAuditInterface.Contract.Core
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.ConceptDynamics.RegistrationWitnesses

namespace LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape

/-- Typed original arena inputs retain their source spelling. -/
inductive ArenaRef.{u,v,w,t,s,r,o,a,k} : Type (max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)) where
  | law (value : Ref (PrimitiveLawArena.{u,v,w}))
  | finite (value : Ref (Arena.{u}))
  | object (value : Ref (ObjectDomainArena.{u,v,w,k}))
  | witness (value : Ref (CounterexampleRecord.WitnessArena.{k}))
  | source (value : Ref (DependentFamily.Arena.{t,s,r,o,a}))

/-- The exact theorem statement and raw bundle belong to this finite unit. -/
structure BoundTheoremUnit.{u,v} (arena : Arena.{u}) (P : Prop)
    (primitives : D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.{u,v} arena.State) where
  value : Ref (TheoremUnit.{u,v} arena)
  statement : ExactMatch P value.value.Statement
  bundle : ExactMatch primitives value.value.primitives

/-- Original bridges, compiled bundles and theorem units are checked together. -/
inductive Implementation.{u,v,w,t,s,r,o,a,k} (P : Prop) :
    Type (max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)) where
  | legacy (arena : PrimitiveLawArena.{u,v,w})
      (actual : PrimitiveRealization arena.signature)
      (primitives : D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.{u,v} arena.State)
      (bridge : Ref (LegacyPrimitiveRealization arena P actual))
      (compiled : ExactMatch (@PrimitiveRealization.toPrimitiveBundle _ _ arena.stateDecidableEq actual) primitives)
      (unit : BoundTheoremUnit arena.toArena P primitives)
  | forward (arena : PrimitiveLawArena.{u,v,w})
      (actual : PrimitiveRealization arena.signature)
      (primitives : D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.{u,v} arena.State)
      (bridge : Ref (EscapeRecord.EscapePrimitiveRealization arena P actual))
      (compiled : ExactMatch (@PrimitiveRealization.toPrimitiveBundle _ _ arena.stateDecidableEq actual) primitives)
      (unit : BoundTheoremUnit arena.toArena P primitives)
  | witness (arena : CounterexampleRecord.WitnessArena.{k})
      (actual : PrimitiveRealization arena.signature)
      (primitives : D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.{0,0} arena.State)
      (bridge : Ref (CounterexampleRecord.WitnessPrimitiveRealization arena P actual))
      (positive : arena.Law actual)
      (actualCheck : ExactMatch arena.realization.readout actual.readout)
      (statementCheck : ExactMatch (¬ ∀ d, arena.predicate d) P)
      (compiled : ExactMatch (@PrimitiveRealization.toPrimitiveBundle _ _ arena.stateDecidableEq actual) primitives)
      (unit : BoundTheoremUnit arena.toArena P primitives)
  | source (arena : DependentFamily.Arena.{t,s,r,o,a})
      (bridge : Ref (DependentFamily.Registration arena P))

namespace Implementation
universe u v w t s r o a k

/-- Literal evidence retains exact normalized stage indices. -/
def ArenaCorrespondence {P : Prop} (implementation : Implementation.{u,v,w,t,s,r,o,a,k} P)
    (original : ArenaRef.{u,v,w,t,s,r,o,a,k}) : Type (max (u+3) (v+3) (w+3) (t+3) (s+3) (r+3) (o+3) (a+3) (k+3)) :=
  match implementation, original with
  | .legacy arena .., .law raw | .forward arena .., .law raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value)
  | .legacy arena .., .object raw | .forward arena .., .object raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value.toPrimitiveLawArena)
  | .legacy arena .., .witness raw | .forward arena .., .witness raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value.toPrimitiveLawArena)
  | .witness arena .., .witness raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value)
  | .source arena _, .source raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value)
  | _, _ => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} True) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} False)

def ObjectCorrespondence {P : Prop} (implementation : Implementation.{u,v,w,t,s,r,o,a,k} P)
    (original : ArenaRef.{u,v,w,t,s,r,o,a,k}) : Type (max (u+3) (v+3) (w+3) (t+3) (s+3) (r+3) (o+3) (a+3) (k+3)) :=
  match implementation, original with
  | .legacy arena .., .law raw | .forward arena .., .law raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena.toArena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value.toArena)
  | .legacy arena .., .finite raw | .forward arena .., .finite raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena.toArena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value)
  | .legacy arena .., .object raw | .forward arena .., .object raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena.toArena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value.toArena)
  | .legacy arena .., .witness raw | .forward arena .., .witness raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena.toArena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value.toArena)
  | .witness arena .., .witness raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena.toArena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value.toArena)
  | .witness arena .., .finite raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena.toArena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value)
  | .source arena _, .source raw => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} arena) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} raw.value)
  | _, _ => ExactMatch (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} True) (ULift.up.{max (u+2) (v+2) (w+2) (t+2) (s+2) (r+2) (o+2) (a+2) (k+2)} False)

structure Correspondence {P : Prop} (implementation : Implementation.{u,v,w,t,s,r,o,a,k} P)
    (arena objectArena : ArenaRef.{u,v,w,t,s,r,o,a,k}) where
  stage : implementation.ArenaCorrespondence arena
  objectStage : implementation.ObjectCorrespondence objectArena

def Variation {P : Prop} : Implementation.{u,v,w,t,s,r,o,a,k} P → Prop
  | .legacy arena .. | .forward arena .. => LeanInformationAudit.FiniteLawVariation arena
  | .witness arena actual .. => arena.Law actual ∧ ¬ arena.Law arena.constantTrue
  | .source _ _ => True

/-- Separate submissions preserve the positive/negative witness diagnostics. -/
structure WitnessVariationEvidence (arena : CounterexampleRecord.WitnessArena.{k})
    (actual : PrimitiveRealization arena.signature) where
  positive : Obligation (arena.Law actual)
  negative : Obligation (¬ arena.Law arena.constantTrue)

def VariationEvidence {P : Prop} : Implementation.{u,v,w,t,s,r,o,a,k} P → Type
  | .witness arena actual .. => WitnessVariationEvidence arena actual
  | implementation => Obligation implementation.Variation

def Sensitivity {P : Prop} : Implementation.{u,v,w,t,s,r,o,a,k} P → Prop
  | .legacy arena .. | .forward arena .. => LeanInformationAudit.FiniteSlotSensitivity arena
  | .witness arena .. => LeanInformationAudit.FiniteSlotSensitivity arena.toPrimitiveLawArena
  | .source _ _ => True

def BundleNonempty {P : Prop} : Implementation.{u,v,w,t,s,r,o,a,k} P → Prop
  | .legacy _ _ primitives .. | .forward _ _ primitives .. => primitives.Nonempty
  | .witness _ _ primitives .. => primitives.Nonempty
  | .source _ _ => True

/-- Lift only the index carrier; the underlying registered slot stays unchanged. -/
def ReadoutIndex {P : Prop} : Implementation.{u,v,w,t,s,r,o,a,k} P → Type (max v r a)
  | .legacy arena .. | .forward arena .. => ULift.{max v r a} arena.signature.Index
  | .witness arena .. => ULift.{max v r a} arena.signature.Index
  | .source arena _ => ULift.{max v r a} arena.signature.Role

def AnchorIndex {P : Prop} : Implementation.{u,v,w,t,s,r,o,a,k} P → Type (max v r a)
  | .legacy arena .. | .forward arena .. => ULift.{max v r a} arena.signature.AnchorIndex
  | .witness arena .. => ULift.{max v r a} arena.signature.AnchorIndex
  | .source arena _ => ULift.{max v r a} arena.signature.Anchor

def ReadoutSensitivity {P : Prop} : (implementation : Implementation.{u,v,w,t,s,r,o,a,k} P) →
    implementation.ReadoutIndex → Prop
  | .legacy arena .., i | .forward arena .., i =>
    Exists fun r : PrimitiveRealization arena.signature =>
      Exists fun r' : PrimitiveRealization arena.signature =>
      (∀ j, j ≠ i.down → r.readout j = r'.readout j) ∧
      (∀ j, r.anchor j = r'.anchor j) ∧ (arena.Law r ↔ ¬ arena.Law r')
  | .witness arena .., i =>
    Exists fun r : PrimitiveRealization arena.signature =>
      Exists fun r' : PrimitiveRealization arena.signature =>
      (∀ j, j ≠ i.down → r.readout j = r'.readout j) ∧
      (∀ j, r.anchor j = r'.anchor j) ∧ (arena.Law r ↔ ¬ arena.Law r')
  | .source _ _, _ => True

def AnchorSensitivity {P : Prop} : (implementation : Implementation.{u,v,w,t,s,r,o,a,k} P) →
    implementation.AnchorIndex → Prop
  | .legacy arena .., i | .forward arena .., i =>
    Exists fun r : PrimitiveRealization arena.signature =>
      Exists fun r' : PrimitiveRealization arena.signature =>
      (∀ j, r.readout j = r'.readout j) ∧
      (∀ j, j ≠ i.down → r.anchor j = r'.anchor j) ∧ (arena.Law r ↔ ¬ arena.Law r')
  | .witness arena .., i =>
    Exists fun r : PrimitiveRealization arena.signature =>
      Exists fun r' : PrimitiveRealization arena.signature =>
      (∀ j, r.readout j = r'.readout j) ∧
      (∀ j, j ≠ i.down → r.anchor j = r'.anchor j) ∧ (arena.Law r ↔ ¬ arena.Law r')
  | .source _ _, _ => True

/-- Individual slot submissions preserve partial support in the arena's own
finite enumeration. Each evidence constructor proves that exact registered slot. -/
structure PartialSlotEvidence {P : Prop} (implementation : Implementation.{u,v,w,t,s,r,o,a,k} P) where
  readouts : ∀ i, Obligation (implementation.ReadoutSensitivity i)
  anchors : ∀ i, Obligation (implementation.AnchorSensitivity i)

end Implementation
end LeanInformationAudit.Contract
