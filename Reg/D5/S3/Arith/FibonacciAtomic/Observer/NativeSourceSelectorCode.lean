import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
open D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Nat.Partrec (Code)

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode

abbrev tickSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Part Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def tickActual : Realization tickSignature :=
  realize tickSignature (fun _ _ n => Code.eval tickCode n) (fun e => nomatch e)

def tickBad : Realization tickSignature :=
  realize tickSignature (fun _ _ _ => Part.none) (fun e => nomatch e)

abbrev tickArena : Arena where
  signature := tickSignature
  Law R := ∀ n : Nat, R.readout () () n = Part.some (Encodable.encode (numericTick n))

private theorem numeric_one : numericTick 1 = Sum.inl (originalStop 0) := by
  have h : (1 : Nat) = Encodable.encode (Sum.inr (0,[]) : NumericControl) := rfl
  rw [h]
  simp only [numericTick,Encodable.encodek,Option.getD_some]
  rfl

private theorem numeric_five : numericTick 5 = Sum.inl (originalStop 1) := by
  have h : (5 : Nat) = Encodable.encode (Sum.inr (1,[]) : NumericControl) := rfl
  rw [h]
  simp only [numericTick,Encodable.encodek,Option.getD_some]
  rfl

private theorem tick_bad : ¬ tickArena.Law tickBad := by
  intro h
  have hn := h 1
  simp [tickBad,realize,numeric_one] at hn

def tickProof : Registration tickArena (type_of% (@tick_code_correct)) where
  actual := tickActual
  bridge := Iff.rfl
  variation := ⟨tick_code_correct,tickBad,tick_bad⟩
  sensitivity := ⟨fun i => ⟨tickBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,tick_bad⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(),1,5,?_⟩
    change Code.eval tickCode 1 ≠ Code.eval tickCode 5
    rw [tick_code_correct,tick_code_correct]
    simp [numeric_one,numeric_five,originalStop,Encodable.encodeSum]

noncomputable def tick_code_correct_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode.tick_code_correct)
      (Realization tickSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode.tick_code_correct
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode.tickProof
  realizationSource := none
  generated := false
  arena := .source ⟨tickArena⟩
  objectArena := .source ⟨tickArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tickArena ⟨tickProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tickSignature tickActual.readout tickActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private theorem workspace_one : selectWorkspace 1 = Part.some (originalStop 0) := by
  apply Part.eq_some_iff.mpr
  exact PFun.fix_stop (by rw [numeric_one]; exact Part.mem_some _)

private theorem workspace_five : selectWorkspace 5 = Part.some (originalStop 1) := by
  apply Part.eq_some_iff.mpr
  exact PFun.fix_stop (by rw [numeric_five]; exact Part.mem_some _)

def workspaceActual : Realization tickSignature :=
  realize tickSignature (fun _ _ n => Code.eval workspaceCode n) (fun e => nomatch e)

abbrev workspaceArena : Arena where
  signature := tickSignature
  Law R := ∀ (hTick : ∀ n : Nat, Code.eval tickCode n =
      Part.some (Encodable.encode (numericTick n))) (n : Nat),
    R.readout () () n = (selectWorkspace n).map Encodable.encode

private theorem workspace_bad : ¬ workspaceArena.Law tickBad := by
  intro h
  have hn := h tick_code_correct 1
  simp [tickBad,realize,workspace_one] at hn

def workspaceProof : Registration workspaceArena (type_of% (@workspace_code_correct_of_tick)) where
  actual := workspaceActual
  bridge := Iff.rfl
  variation := ⟨workspace_code_correct_of_tick,tickBad,workspace_bad⟩
  sensitivity := ⟨fun i => ⟨tickBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,workspace_bad⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(),1,5,?_⟩
    change Code.eval workspaceCode 1 ≠ Code.eval workspaceCode 5
    rw [workspace_code_correct_of_tick tick_code_correct,
      workspace_code_correct_of_tick tick_code_correct,workspace_one,workspace_five]
    simp [originalStop,Encodable.encodeSum]

abbrev selectorSignature : Signature where
  Params := Unit
  State _ := OriginalState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Part Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def selectorActual : Realization selectorSignature :=
  realize selectorSignature (fun _ _ s => Code.eval selectorCode (Encodable.encode s))
    (fun e => nomatch e)

def selectorBad : Realization selectorSignature :=
  realize selectorSignature (fun _ _ _ => Part.none) (fun e => nomatch e)

abbrev selectorArena : Arena where
  signature := selectorSignature
  Law R := ∀ s : OriginalState, R.readout () () s = (sourceService.select s).map Encodable.encode

private theorem selector_bad : ¬ selectorArena.Law selectorBad := by
  intro h
  have hn := h (0,1,0,[])
  simp [selectorBad,realize,sourceService,workspace_one] at hn

def selectorProof : Registration selectorArena (type_of% (@selector_code_correct)) where
  actual := selectorActual
  bridge := Iff.rfl
  variation := ⟨selector_code_correct,selectorBad,selector_bad⟩
  sensitivity := ⟨fun i => ⟨selectorBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,selector_bad⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(),(0,1,0,[]),(0,5,0,[]),?_⟩
    change Code.eval selectorCode (Encodable.encode ((0,1,0,[]) : OriginalState)) ≠
      Code.eval selectorCode (Encodable.encode ((0,5,0,[]) : OriginalState))
    rw [selector_code_correct,selector_code_correct]
    change (selectWorkspace 1).map Encodable.encode ≠ (selectWorkspace 5).map Encodable.encode
    rw [workspace_one,workspace_five]
    simp [originalStop,Encodable.encodeSum]

noncomputable def workspace_code_correct_of_tick_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode.workspace_code_correct_of_tick)
      (Realization tickSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode.workspace_code_correct_of_tick
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode.workspaceProof
  realizationSource := none
  generated := false
  arena := .source ⟨workspaceArena⟩
  objectArena := .source ⟨workspaceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source workspaceArena ⟨workspaceProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tickSignature workspaceActual.readout workspaceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","body","fn","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def selector_code_correct_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode.selector_code_correct)
      (Realization selectorSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode.selector_code_correct
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode.selectorProof
  realizationSource := none
  generated := false
  arena := .source ⟨selectorArena⟩
  objectArena := .source ⟨selectorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source selectorArena ⟨selectorProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize selectorSignature selectorActual.readout selectorActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode
