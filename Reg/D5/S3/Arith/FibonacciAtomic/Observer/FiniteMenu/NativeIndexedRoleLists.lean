import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeIndexedRoleLists
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeIndexedRoleLists
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeIndexedRoleLists

/-- One output retains all nodes, six roles and four types for a record family. -/
abbrev signature : Signature where
  Params := Unit
  State _ := List Constraint
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Address → Fin 6 → Kind → List Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ R => lists R) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Specification (fun Q => R.readout () () Q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have eq := h.hash [] 0 .A
  change ([] : List Source) = [.of true] at eq
  cases eq

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(),[],[⟨0,0,[],.absent⟩],?_⟩
  intro h
  have eq := congrArg (fun f => f (some []) 0 .A) h
  change ([.of true] : List Source) = [] at eq
  cases eq

def family : Registration arena (type_of% (@native_indexed_role_lists)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_indexed_role_lists,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_indexed_role_lists) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeIndexedRoleLists.native_indexed_role_lists.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeIndexedRoleLists.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ R => lists R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeIndexedRoleLists
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeIndexedRoleLists
