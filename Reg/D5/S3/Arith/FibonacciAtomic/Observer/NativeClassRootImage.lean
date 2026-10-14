import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev fillingSignature : Signature where
  Params := Unit
  State _ := Nat → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def fillingActual : Realization fillingSignature := realize fillingSignature
  (fun _ _ f => evaluateRow f) (fun e => nomatch e)
def fillingBad : Realization fillingSignature := realize fillingSignature
  (fun _ _ _ _ => .of true) (fun e => nomatch e)
abbrev fillingArena : Arena where
  signature := fillingSignature
  Law R := ∀ (C : LiteralRow) (f : Nat → Source),
    Image (R.readout () () f C) ↔ BranchImages C f ∧ im (fun n => rootType (f n)) C

theorem fillingBadLaw : ¬ fillingArena.Law fillingBad := by
  intro h
  have hh := (h (.of (.inl false)) (fun _ => .of false)).mpr
    ⟨by simp [BranchImages,labels],rfl⟩
  obtain ⟨u,hu⟩ := hh
  exact _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates.no_alpha u hu

def fillingFamily : Registration fillingArena (type_of% (@filling_image_iff)) where
  actual := fillingActual
  bridge := Iff.rfl
  variation := ⟨filling_image_iff,fillingBad,fillingBadLaw⟩
  sensitivity := ⟨fun i => ⟨fillingBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,fillingBadLaw⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(),(fun _ => .of true),(fun _ => .of false),?_⟩
    intro h
    have hh := congrFun h (.of (.inr 0))
    change FreeMagma.of true = FreeMagma.of false at hh
    cases (show true = false from by injection hh)

def fillingRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@filling_image_iff)
    (type_of% (realize fillingSignature fillingActual.readout fillingActual.anchor))
    Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.filling_image_iff.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.fillingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fillingArena⟩
  objectArena := .source ⟨fillingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fillingArena ⟨fillingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fillingSignature fillingActual.readout fillingActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg","arg","fn"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev chartSignature : Signature where
  Params := Σ _ : CutSet, Source
  State p := Classes (canonicalRow p.1 p.2) → Option Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Classes (canonicalRow p.1 p.2) → Option Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def chartActual : Realization chartSignature := realize chartSignature
  (fun _ _ θ => θ) (fun e => nomatch e)
def chartBad : Realization chartSignature := realize chartSignature
  (fun _ _ _ _ => some true) (fun e => nomatch e)
abbrev chartArena : Arena where
  signature := chartSignature
  Law R := ∀ (P : CutSet) (hP : CutPrefixFree P) (t₀ : Source)
    (θ : Classes (canonicalRow P t₀) → Option Bool),
    Admissible (canonicalRow P t₀) (R.readout () ⟨P,t₀⟩ θ) ↔ ∃ u : OriginFiber P (canonicalRow P t₀),
      types (canonicalRow P t₀)
        (recover P hP (canonicalRow P t₀) ⟨substitution u.val,u.property⟩).val = θ

private theorem rootRow : canonicalRow {[]} (.of false) = .of (.inr 0) := by
  simp [canonicalRow,literalRow,classOrdinal,orderedHoles,reachedHoles,firstEqIndex,
    _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity.subtree]

private theorem betaRootAdmissible : Admissible (.of (.inr 0)) (fun _ => some false) := by
  classical
  have bound : (Finset.univ : Finset (Classes (.of (.inr 0)))).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro d _ e _
    apply Subtype.ext
    have hd : d.val = 0 := by simpa [labels] using d.property
    have he : e.val = 0 := by simpa [labels] using e.property
    exact hd.trans he.symm
  refine ⟨by simp [im,typeExtend,labels],?_,?_⟩ <;>
    exact (Finset.card_filter_le _ _).trans bound

theorem chartBadLaw : ¬ chartArena.Law chartBad := by
  intro h
  have hp : CutPrefixFree {[]} := by
    intro a ha b hb _
    change a ∈ ({[]} : CutSet) at ha
    change b ∈ ({[]} : CutSet) at hb
    simp only [Finset.mem_singleton] at ha hb
    exact ha.trans hb.symm
  let θ : Classes (canonicalRow {[]} (.of false)) → Option Bool := fun _ => some false
  have ha : Admissible (canonicalRow {[]} (.of false)) θ := by
    change Admissible (canonicalRow {[]} (.of false)) (fun _ => some false)
    rw [rootRow]
    exact betaRootAdmissible
  have hx := (h {[]} hp (.of false) θ).mpr
    ((class_root_chart {[]} hp (.of false) θ).mp ha)
  change Admissible (canonicalRow {[]} (.of false)) (fun _ => some true) at hx
  rw [rootRow] at hx
  simpa [Admissible,im,typeExtend,labels] using hx

theorem chartDependence : ObservationalDependence chartSignature chartActual := by
  intro i
  refine ⟨⟨{[]},.of false⟩,(fun _ => some false),(fun _ => some true),?_⟩
  change (fun _ : Classes (canonicalRow {[]} (.of false)) => some false) ≠
    (fun _ => some true)
  have hn : 0 ∈ labels (canonicalRow {[]} (.of false)) := by rw [rootRow]; simp [labels]
  intro eq
  have h := congrFun eq (⟨0,hn⟩ : Classes (canonicalRow {[]} (.of false)))
  cases (show false = true from Option.some.inj h)

def chartFamily : Registration chartArena (type_of% (@class_root_chart)) where
  actual := chartActual
  bridge := Iff.rfl
  variation := ⟨class_root_chart,chartBad,chartBadLaw⟩
  sensitivity := ⟨fun i => ⟨chartBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,chartBadLaw⟩,fun i => nomatch i⟩
  dependence := chartDependence

def chartRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@class_root_chart)
    (type_of% (realize chartSignature chartActual.readout chartActual.anchor))
    (LiteralRow → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.class_root_chart.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.chartFamily
  realizationSource := none
  generated := false
  arena := .source ⟨chartArena⟩
  objectArena := .source ⟨chartArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chartArena ⟨chartFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize chartSignature chartActual.readout chartActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","arg"],
      stateBinder := 3,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms fillingRegistration
#print axioms chartRegistration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage

noncomputable section

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.FullRootSuppliers
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev leafSignature : Signature where
  Params := LiteralRow
  State p := Nat → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def leafActual : Realization leafSignature := realize leafSignature
  (fun _ C f => evaluateRow f C) (fun e => nomatch e)
def leafBad : Realization leafSignature := realize leafSignature
  (fun _ _ _ => .of false) (fun e => nomatch e)
abbrev leafArena : Arena where
  signature := leafSignature
  Law R := ∀ (C : LiteralRow) (f : Nat → Source) (b : Bool), R.readout () C f = .of b ↔ lit (fun n => rootType (f n)) b C

private theorem leafBadLaw : ¬ leafArena.Law leafBad := by
  intro h
  have eq := (h (.of (.inl true)) (fun _ => .of true) true).mpr rfl
  change FreeMagma.of false = FreeMagma.of true at eq
  cases eq

private theorem leafDependence : ObservationalDependence leafSignature leafActual := by
  intro i
  refine ⟨.of (.inr 0),(fun _ => .of true),(fun _ => .of false),?_⟩
  intro eq
  change FreeMagma.of true = FreeMagma.of false at eq
  cases eq

def leafFamily : Registration leafArena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.evaluate_leaf)) where
  actual := leafActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.evaluate_leaf,leafBad,leafBadLaw⟩
  sensitivity := ⟨fun i => ⟨leafBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,leafBadLaw⟩,fun i => nomatch i⟩
  dependence := leafDependence

def leafRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.evaluate_leaf)
    (type_of% (realize leafSignature leafActual.readout leafActual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.evaluate_leaf.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.FullRootSuppliers.leafFamily
  realizationSource := none
  generated := false
  arena := .source ⟨leafArena⟩
  objectArena := .source ⟨leafArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source leafArena ⟨leafFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize leafSignature leafActual.readout leafActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms leafRegistration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.FullRootSuppliers

noncomputable section

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.FullRootSuppliers
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCutFibers
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev extensionSignature : Signature where
  Params := LiteralRow
  State p := Classes p → Option Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat → Option Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def extensionActual : Realization extensionSignature := realize extensionSignature
  (fun _ C θ => typeExtend C θ) (fun e => nomatch e)
def extensionBad : Realization extensionSignature := realize extensionSignature
  (fun _ _ _ _ => some false) (fun e => nomatch e)
abbrev extensionArena : Arena where
  signature := extensionSignature
  Law R := ∀ (C : LiteralRow) (v : Classes C → Source), (fun n => rootType (extend C v n)) = R.readout () C (types C v)

private theorem extensionBadLaw : ¬ extensionArena.Law extensionBad := by
  intro h
  have eq := congrFun (h (.of (.inl true)) (fun d => False.elim (by simpa [labels] using d.property))) 0
  change some true = some false at eq
  cases eq

private theorem extensionDependence : ObservationalDependence extensionSignature extensionActual := by
  intro i
  refine ⟨.of (.inr 0),(fun _ => some true),(fun _ => some false),?_⟩
  intro eq
  have h := congrFun eq 0
  simp [extensionActual,realize,typeExtend,labels] at h

def extensionFamily : Registration extensionArena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.root_extend)) where
  actual := extensionActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.root_extend,extensionBad,extensionBadLaw⟩
  sensitivity := ⟨fun i => ⟨extensionBad,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,extensionBadLaw⟩,fun i => nomatch i⟩
  dependence := extensionDependence

def extensionRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.root_extend)
    (type_of% (realize extensionSignature extensionActual.readout extensionActual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.root_extend.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.FullRootSuppliers.extensionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨extensionArena⟩
  objectArena := .source ⟨extensionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source extensionArena ⟨extensionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize extensionSignature extensionActual.readout extensionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms extensionRegistration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage.FullRootSuppliers
