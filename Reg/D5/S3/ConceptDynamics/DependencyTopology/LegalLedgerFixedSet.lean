import D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet
import D5.S3.ConceptDynamics.DagSemantics.StrictDependencyCoordinate
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The original permitted-proof projection on the full family of actual legal cores. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet

open _root_.D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet
open _root_.D5.S3.ConceptDynamics.DagSemantics.StrictDependencyCoordinate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w x
noncomputable section
attribute [local instance] Classical.propDecidable

structure Source where
  Proposition : Type u
  Proof : Type v
  Axiom : Type w
  Model : Type x
  kernel : KernelData Proposition Proof Axiom Model

abbrev signature : Signature where
  Params := Source.{u,v,w,x}
  State s := LegalLedger s.kernel
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ s := Set s.Proposition
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature.{u,v,w,x}
  Law obs := ∀ (s : Source.{u,v,w,x}) (L : LegalLedger s.kernel) p,
    p ∈ obs.readout () s L → Proved s.kernel p

def actual : Realization signature.{u,v,w,x} := realize signature
  (fun _ _ L => Frozen L) (fun a => nomatch a)

def rejected : Realization signature.{u,v,w,x} := realize signature
  (fun _ _ _ => Set.univ) (fun a => nomatch a)

def emptyCore {P : Type u} {Proof : Type v} {Ax : Type w} {Model : Type x}
    (k : KernelData P Proof Ax Model) : CertifiedNodes k := by
  refine ⟨⟨∅, fun p => (Finset.notMem_empty p.val p.property).elim⟩, ?_, ?_, ?_, ?_⟩
  · intro p; exact (Finset.notMem_empty p.val p.property).elim
  · intro p; exact (Finset.notMem_empty p.val p.property).elim
  · intro p; exact (Finset.notMem_empty p.val p.property).elim
  · apply acyclic_of_strictCoordinate (coordinate := fun _ => (0 : ℕ))
    rintro p q ⟨hq,_⟩
    exact (Finset.notMem_empty q hq).elim

def emptyLedger {P : Type u} {Proof : Type v} {Ax : Type w} {Model : Type x}
    (k : KernelData P Proof Ax Model) : LegalLedger k :=
  ⟨⟨emptyCore k, ∅⟩, by simp⟩

def testKernel (accepted : Bool) : KernelData (ULift.{u} Unit) (ULift.{v} Unit)
    (ULift.{w} Unit) (ULift.{x} Unit) :=
  (fun _ _ => accepted, fun _ => ∅, fun _ => ∅, ∅, id,
    fun _ _ => True, fun _ _ => True)

def singletonCore : CertifiedNodes (testKernel.{u,v,w,x} true) := by
  refine ⟨⟨{⟨()⟩}, fun _ => ⟨()⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro p; rfl
  · intro p a ha; exact (Finset.notMem_empty a ha).elim
  · intro p q hq; exact (Finset.notMem_empty q hq).elim
  · apply acyclic_of_strictCoordinate (coordinate := fun _ => (0 : ℕ))
    rintro p q ⟨_,hq⟩
    exact (Finset.notMem_empty p hq).elim

def singletonLedger : LegalLedger (testKernel.{u,v,w,x} true) :=
  ⟨⟨singletonCore, ∅⟩, by simp⟩

def testSource (accepted : Bool) : Source.{u,v,w,x} :=
  ⟨ULift Unit, ULift Unit, ULift Unit, ULift Unit, testKernel accepted⟩

private theorem rejected_fails : ¬ arena.{u,v,w,x}.Law rejected := by
  intro h
  obtain ⟨π,hπ,_⟩ := h (testSource false) (emptyLedger _) ⟨()⟩ (Set.mem_univ _)
  change false = true at hπ
  cases hπ

private theorem actual_dependence : ObservationalDependence signature actual.{u,v,w,x} := by
  intro i
  refine ⟨testSource true, emptyLedger _, singletonLedger, ?_⟩
  intro he
  have present : (⟨()⟩ : ULift.{u} Unit) ∈ Frozen singletonLedger.{u,v,w,x} :=
    Finset.mem_singleton_self _
  have absent : (⟨()⟩ : ULift.{u} Unit) ∉ Frozen (emptyLedger (testKernel.{u,v,w,x} true)) :=
    Finset.notMem_empty _
  change Frozen (emptyLedger (testKernel.{u,v,w,x} true)) =
    Frozen singletonLedger.{u,v,w,x} at he
  apply absent
  rw [he]
  exact present

def family : Registration arena.{u,v,w,x} (type_of% @frozen_proved.{u,v,w,x}) where
  actual := realize signature actual.readout actual.anchor
  bridge := by
    constructor
    · intro h s L p hp
      exact h L hp
    · intro h P Proof Ax Model k L p hp
      exact h ⟨P,Proof,Ax,Model,k⟩ L p hp
  variation := ⟨fun _ L _ hp => frozen_proved L hp, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := actual_dependence

def registration : Contract.Registration.{
    max (max (u + 1) (v + 1)) (max (w + 1) (x + 1)), 0, 1, 0, 0, 0,
    max (max (u + 1) (v + 1)) (max (w + 1) (x + 1)), max u v, 0, u, 0, 0}
    (@frozen_proved.{u,v,w,x}) (Realization signature.{u,v,w,x}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","domain","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end
end Reg.D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet
