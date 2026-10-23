import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.Kernel
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (readout)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
open D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.Kernel
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.Kernel

abbrev signature : Signature where
  Params := Menu
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ S u => code S u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (S : Menu) (u v : Source),
    R.readout () S u = R.readout () S v ↔
      ∀ q ∈ S, ∀ k : Nat,
        readout q (substitution^[k] u) = readout q (substitution^[k] v)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h [[]] (.of true) (.of false)).mp rfl [] (by simp) 0
  cases he

def family : Registration arena (type_of% (@original_menu_kernel)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_menu_kernel, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro _
    exact ⟨[[]], .of true, .of false,
      original_code_context_separation [[]] [] [] (by simp)⟩

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_menu_kernel) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.Kernel.original_menu_kernel.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.Kernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ S u => code S u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.Kernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.Kernel
