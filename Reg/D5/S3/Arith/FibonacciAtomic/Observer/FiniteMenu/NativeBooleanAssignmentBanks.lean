import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic
open D5.S3.Arith.FibonacciAtomic.Observer
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage (rootType)
open D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks

abbrev signature : Signature where
  Params := Nat
  State n := Fin n → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ b => bank b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .of false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Lemma61 (fun n b => R.readout () n b)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have root := ((h.1 0).2.2 (fun i => Fin.elim0 i)).1.2.2.2.2.2.1
  change rootType (.of false) = none at root
  cases root

private theorem bank_dependence : ObservationalDependence signature actual := by
  intro _
  let off : Fin 1 → Bool := fun _ => false
  let on : Fin 1 → Bool := fun _ => true
  have all := native_boolean_assignment_banks.1 1
  have lengths := all.1.2.2.2.2.2.1 0
  have empty := (all.2.2 off).1
  have full := (all.2.2 on).1
  have left := empty.2.1 (variableWord 1 0) lengths.1
  have right := full.2.1 (variableWord 1 0) lengths.1
  rw [empty.2.2.1 0] at left
  rw [full.2.2.1 0] at right
  refine ⟨1,off,on,?_⟩
  intro h
  change bank off = bank on at h
  have sub := congrArg (subtree (variableWord 1 0)) h
  rw [left,right] at sub
  cases sub

noncomputable def family : Registration arena (type_of% (@native_boolean_assignment_banks)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_boolean_assignment_banks,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun i => nomatch i⟩
  dependence := bank_dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_boolean_assignment_banks) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks.native_boolean_assignment_banks.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => bank b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg","body","body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

namespace Height

abbrev signature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => B d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .of false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : Nat, ActualImageAddressCertificate.height (R.readout () () d) = d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h 1
  change 0 = 1 at h1
  omega

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨(),0,1,by decide⟩

def family : Registration arena (type_of% (@B_height)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨B_height,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@B_height) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks.B_height.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks.Height.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => B d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Height

namespace Preimage

abbrev signature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => NativeClassRootPadding.pad d (.of true)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .of true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : Nat, GenealogicalFiberTransport.substitution (R.readout () () d) = B d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h 1
  change FreeMagma.of false = FreeMagma.mul (.of false) (.of false) at h1
  cases h1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨(),0,1,by decide⟩

def family : Registration arena (type_of% (@pad_preimage)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pad_preimage,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pad_preimage) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks.pad_preimage.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks.Preimage.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => NativeClassRootPadding.pad d (.of true)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Preimage

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks
