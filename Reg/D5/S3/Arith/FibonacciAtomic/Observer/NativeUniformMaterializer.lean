import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformMaterializer
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformMaterializer

open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.Observer
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State _ := CommonCode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option AnalysisCode
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ w => materializeAnalysis w) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Computable (R.readout () ()) ∧ ∀ C Q H N,
    R.readout () () (codeCommon C Q H N) = some (nativeAnalysisCode C Q H)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have no := h.2 (FreeMagma.of (.inl false)) ∅ [] 0
  cases no

def proof : Registration arena (type_of% (@uniform_native_materializer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_native_materializer,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(),codeCommon (FreeMagma.of (.inl false)) ∅ [] 0,
      codeCommon (FreeMagma.of (.inl false)) {[false]} [] 0,?_⟩
    change materializeAnalysis (codeCommon (FreeMagma.of (.inl false)) ∅ [] 0) ≠
      materializeAnalysis (codeCommon (FreeMagma.of (.inl false)) {[false]} [] 0)
    rw [uniform_native_materializer.2,uniform_native_materializer.2]
    intro eq
    have hd := congrArg (fun s : AnalysisCode => s.1) (Option.some.inj eq)
    simp [nativeAnalysisCode,NativeHistoryCells.requiredDepth,ActualCutPartitionRecovery.cutDepth] at hd

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis.uniform_native_materializer)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformMaterializer.uniform_native_materializer
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformMaterializer.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => materializeAnalysis w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformMaterializer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformMaterializer
