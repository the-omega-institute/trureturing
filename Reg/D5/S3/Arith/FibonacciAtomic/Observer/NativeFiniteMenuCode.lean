import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode

abbrev rankSignature : Signature where
  Params := Menu
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def rankActual : Realization rankSignature :=
  realize rankSignature (fun _ S u => code S u) (fun e => nomatch e)

def rankBad : Realization rankSignature :=
  realize rankSignature (fun _ S _ => code S (.of false)) (fun e => nomatch e)

abbrev contextArena : Arena where
  signature := rankSignature
  Law R := ∀ (S : Menu) (a r : Address), a ++ r ∈ S →
    R.readout () S (spine a (.of true)) ≠ code S (spine a (.of false))

private theorem context_bad : ¬ contextArena.Law rankBad := by
  intro h
  exact h [[]] [] [] (by simp) rfl

def contextProof : Registration contextArena (type_of% (@original_code_context_separation)) where
  actual := rankActual
  bridge := Iff.rfl
  variation := ⟨original_code_context_separation, rankBad, context_bad⟩
  sensitivity := ⟨fun i => ⟨rankBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, context_bad⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨[[]], .of true, .of false,
      original_code_context_separation [[]] [] [] (by simp)⟩

noncomputable def original_code_context_separation_registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode.original_code_context_separation)
    (Realization rankSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode.original_code_context_separation.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode.contextProof
  realizationSource := none
  generated := false
  arena := .source ⟨contextArena⟩
  objectArena := .source ⟨contextArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source contextArena ⟨contextProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature (fun _ S u => code S u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms contextProof
#print axioms original_code_context_separation_registration

abbrev grammarArena : Arena where
  signature := rankSignature
  Law R := ∀ S : Menu,
    (S = [] → N S = 1 ∧ ∀ u, code S u = 0) ∧
    (S ≠ [] →
      N S = N (child false S) * N (child true S) + 1 + (if eta S then 1 else 0) ∧
      (∀ x y, code S (.mul x y) = code (child false S) x * N (child true S) + code (child true S) y) ∧
      code S (.of true) = N (child false S) * N (child true S) ∧
      code S (.of false) = if eta S then N (child false S) * N (child true S) + 1 else
        code (child false S) (.of true) * N (child true S) + code (child true S) (.of true)) ∧
    0 < N S ∧ (∀ u, R.readout () S u < N S)

def rangeBad : Realization rankSignature :=
  realize rankSignature (fun _ S _ => N S) (fun e => nomatch e)

private theorem grammar_bad : ¬ grammarArena.Law rangeBad := by
  intro h
  have no := (h []).2.2.2 (.of true)
  exact Nat.lt_irrefl (N []) no

def grammarProof : Registration grammarArena (type_of% (@original_code_grammar)) where
  actual := rankActual
  bridge := Iff.rfl
  variation := ⟨original_code_grammar, rangeBad, grammar_bad⟩
  sensitivity := ⟨fun i => ⟨rangeBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, grammar_bad⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨[[]], .of true, .of false,
      original_code_context_separation [[]] [] [] (by simp)⟩

abbrev childSignature : Signature where
  Params := Bool
  State _ := Menu
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Menu
  Anchor := Empty
  finiteAnchor := inferInstance

def childActual : Realization childSignature :=
  realize childSignature (fun _ b S => child b S) (fun e => nomatch e)

def childBad : Realization childSignature :=
  realize childSignature (fun _ _ _ => []) (fun e => nomatch e)

abbrev childArena : Arena where
  signature := childSignature
  Law R := ∀ (b : Bool) (S : Menu) (r : Address), r ∈ R.readout () b S ↔ b :: r ∈ S

private theorem child_bad : ¬ childArena.Law childBad := by
  intro h
  have no := (h false [[false]] []).mpr (by simp)
  exact List.not_mem_nil no

def childProof : Registration childArena (type_of% (@mem_child)) where
  actual := childActual
  bridge := Iff.rfl
  variation := ⟨mem_child, childBad, child_bad⟩
  sensitivity := ⟨fun i => ⟨childBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, child_bad⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨false, [[false]], [], ?_⟩
    change [[]] ≠ []
    simp

noncomputable def original_code_grammar_registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_code_grammar) (Realization rankSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode.original_code_grammar.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode.grammarProof
  realizationSource := none
  generated := false
  arena := .source ⟨grammarArena⟩
  objectArena := .source ⟨grammarArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source grammarArena ⟨grammarProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature (fun _ S u => code S u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","arg","arg","arg","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms grammarProof
#print axioms original_code_grammar_registration

noncomputable def mem_child_registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mem_child) (Realization childSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode.mem_child.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode.childProof
  realizationSource := none
  generated := false
  arena := .source ⟨childArena⟩
  objectArena := .source ⟨childArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source childArena ⟨childProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize childSignature (fun _ b S => child b S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
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

#print axioms childProof
#print axioms mem_child_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
