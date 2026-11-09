import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair (Call run)
open _root_.D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum (comb)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

@[reducible] def prepSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Call
  Anchor := Empty
  finiteAnchor := inferInstance

def prepActual : Realization prepSignature :=
  realize prepSignature (fun _ _ k => preparation k) (fun e => nomatch e)

def prepBad (i : Fin 2) : Realization prepSignature :=
  realize prepSignature (fun j _ k => if j = i then [] else preparation k)
    (fun e => nomatch e)

@[reducible] def prepArena : Arena where
  signature := prepSignature
  Law R := ∀ k : ℕ,
    run (.of true) (R.readout 0 () k) = some (comb k (fun _ => C) M) ∧
    (R.readout 1 () k).length = 3 * k + 4

private theorem prep_bad (i : Fin 2) : ¬ prepArena.Law (prepBad i) := by
  intro h
  fin_cases i
  · have hh := (h 0).1
    change some (FreeMagma.of true : Source) = some M at hh
    exact (by decide : some (FreeMagma.of true : Source) ≠ some M) hh
  · have hh := (h 0).2
    change 0 = 3 * 0 + 4 at hh
    omega

def prepFamilyRegistration : Registration prepArena (type_of% prepares) := {
  actual := prepActual
  bridge := Iff.rfl
  variation := ⟨prepares, prepBad 0, prep_bad 0⟩
  sensitivity := ⟨fun i => ⟨prepBad i,
    by intro j hj; funext p k; simp [prepActual, prepBad, realize, hj], rfl, prep_bad i⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change preparation 0 ≠ preparation 1
    decide }

def preparationRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prepares) (type_of% (realize prepSignature prepActual.readout prepActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion.prepares "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion.prepFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨prepArena⟩
  objectArena := .source ⟨prepArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prepArena ⟨prepFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize prepSignature prepActual.readout prepActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "arg", "fn", "arg", "arg"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

@[reducible] def insertionSignature : Signature where
  Params := (k : ℕ) × (Fin k → Bool)
  State p := List (Fin p.1)
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Call
  Anchor := Empty
  finiteAnchor := inferInstance

def insertionActual : Realization insertionSignature :=
  realize insertionSignature (fun _ p order => order.flatMap (insertion p.2))
    (fun e => nomatch e)

def insertionBad (i : Fin 2) : Realization insertionSignature :=
  realize insertionSignature (fun j p order =>
    if j = i then [] else order.flatMap (insertion p.2)) (fun e => nomatch e)

@[reducible] def insertionArena : Arena where
  signature := insertionSignature
  Law R := ∀ (k : ℕ) (x : Fin k → Bool) (order : List (Fin k)), order.Nodup →
    run (.of true) (preparation k ++ R.readout 0 ⟨k, x⟩ order) =
      some (endpoint k x order) ∧
    (preparation k ++ R.readout 1 ⟨k, x⟩ order).length =
      3 * k + 4 + 2 * order.length

private theorem insertion_bad (i : Fin 2) : ¬ insertionArena.Law (insertionBad i) := by
  intro h
  have hh := h 1 (fun _ => false) [0] (by simp)
  fin_cases i
  · have hn :
        run (.of true) (preparation 1 ++ []) ≠ some (endpoint 1 (fun _ => false) [0]) := by
      decide
    exact hn hh.1
  · have he := hh.2
    change 7 = 3 * 1 + 4 + 2 * 1 at he
    omega

def insertionFamilyRegistration : Registration insertionArena (type_of% prepared_insertion) := {
  actual := insertionActual
  bridge := Iff.rfl
  variation := ⟨prepared_insertion, insertionBad 0, insertion_bad 0⟩
  sensitivity := ⟨fun i => ⟨insertionBad i,
    by intro j hj; funext p order; simp [insertionActual, insertionBad, realize, hj],
    rfl, insertion_bad i⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨1, fun _ => false⟩, [], [0], ?_⟩
    change ([] : List Call) ≠ [0].flatMap (insertion (fun _ : Fin 1 => false))
    decide }

def insertionRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prepared_insertion)
    (type_of% (realize insertionSignature insertionActual.readout insertionActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion.prepared_insertion "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion.insertionFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨insertionArena⟩
  objectArena := .source ⟨insertionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source insertionArena ⟨insertionFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize insertionSignature insertionActual.readout insertionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativePreparedInsertion
