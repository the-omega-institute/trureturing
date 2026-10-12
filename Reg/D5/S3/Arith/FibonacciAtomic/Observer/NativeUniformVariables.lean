import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformVariables
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformVariables

open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.Observer
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformPatterns
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformVariables
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ActualCutPartitionRecovery (LiteralRow CutSet)
open NativeDepthPatterns (Pattern History)
open NativeHistoryCells (Patterns Variables)
open NativeWholeRowService (classList variableList presentation)
open NativeTermUnification (finName)

abbrev tableSignature : Signature where
  Params := Unit
  State := fun _ => List Nat × List PatternWord
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Option (List VariableKey)
  Anchor := Empty
  finiteAnchor := inferInstance

def tableActual : Realization tableSignature := realize tableSignature
  (fun _ _ => fun p => variableKeys p.1 p.2) (fun e => nomatch e)

def tableRejected : Realization tableSignature := realize tableSignature
  (fun _ _ _ => none) (fun e => nomatch e)

abbrev tableArena : Arena where
  signature := tableSignature
  Law R := Primrec₂ (fun names ws => R.readout () () (names,ws)) ∧ ∀ C d (η : Patterns C d), R.readout () () ((classList C).map Subtype.val,familyWord η) = some ((variableList η).map variableKey)

private theorem table_rejected : ¬ tableArena.Law tableRejected := by
  intro h
  have bad := h.2 (FreeMagma.of (.inl false)) 0 (fun _ => ())
  cases bad

def tableEvidence : Registration tableArena (tableArena.Law tableActual) where
  actual := tableActual
  bridge := Iff.rfl
  variation := ⟨uniform_variable_table,tableRejected,table_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨tableRejected,?_,rfl,table_rejected⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(),([],[]),([7],[[some (.inr 0)]]),?_⟩
    change variableKeys [] [] ≠ variableKeys [7] [[some (.inr 0)]]
    decide

abbrev materializerSignature : Signature where
  Params := Unit
  State := fun _ => CommonCode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Option VariableCellCode
  Anchor := Empty
  finiteAnchor := inferInstance

def materializerActual : Realization materializerSignature := realize materializerSignature
  (fun _ _ => fun w => materializeVariableCells w) (fun e => nomatch e)

def materializerRejected : Realization materializerSignature := realize materializerSignature
  (fun _ _ _ => none) (fun e => nomatch e)

abbrev materializerArena : Arena where
  signature := materializerSignature
  Law R := Primrec (R.readout () ()) ∧ ∀ C Q H N,
    R.readout () () (codeCommon C Q H N) =
      some (NativeHistoryCells.requiredDepth Q H,(classList C).map Subtype.val,
        (NativeWholeRowService.allPatterns C (NativeHistoryCells.requiredDepth Q H)).map
          (fun η => (familyWord η,(variableList η).map variableKey))) ∧
      ∀ (η : Patterns C (NativeHistoryCells.requiredDepth Q H)) (x : Variables η),
        (presentation η).code x = finName
          (((variableList η).map variableKey).idxOf (variableKey x))

private theorem materializer_rejected : ¬ materializerArena.Law materializerRejected := by
  intro h
  have bad := (h.2 (FreeMagma.of (.inl false)) ∅ [] 0).1
  cases bad

def materializerEvidence : Registration materializerArena (materializerArena.Law materializerActual) where
  actual := materializerActual
  bridge := Iff.rfl
  variation := ⟨uniform_variable_materializer,materializerRejected,materializer_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨materializerRejected,?_,rfl,materializer_rejected⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(),codeCommon (FreeMagma.of (.inl false)) ∅ [] 0,
      codeCommon (FreeMagma.of (.inl false)) {[false]} [] 0,?_⟩
    dsimp only [materializerActual, realize]
    change materializeVariableCells (codeCommon (FreeMagma.of (.inl false)) ∅ [] 0) ≠
      materializeVariableCells (codeCommon (FreeMagma.of (.inl false)) {[false]} [] 0)
    rw [(uniform_variable_materializer.2 _ _ _ _).1,
      (uniform_variable_materializer.2 _ _ _ _).1]
    intro h
    have hd := congrArg (fun s : VariableCellCode => s.1) (Option.some.inj h)
    simp [NativeHistoryCells.requiredDepth, ActualCutPartitionRecovery.cutDepth] at hd

/- The typed whole-family proofs preserve each complete infinite input claim.
   Contract source-selection coordinates and raw occurrence ties remain
   unregistered; these proof records claim no declared_validated status. -/

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformVariables
