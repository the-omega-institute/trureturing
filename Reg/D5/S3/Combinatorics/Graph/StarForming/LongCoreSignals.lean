import D5.S3.Combinatorics.Graph.StarForming.LongCoreSignals
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.StarForming
open _root_.D5.S3.Combinatorics.Graph.StarForming.LongCoreSignals

namespace Reg.D5.S3.Combinatorics.Graph.StarForming.LongCoreSignals

abbrev signature : Signature where
  Params := Type
  State p := Finset (p × Fin 62)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (p : Type), Finset (p × Fin 62) → ℕ :=
  fun _ _ S => S.card

def noAnchor : ∀ (_ : Empty) (p : Type), Finset (p × Fin 62) := fun e => nomatch e

def bad : Realization signature := realize signature (fun _ _ S => S.card+1) noAnchor

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {I : Type} [f : Fintype I] [e : DecidableEq I],
    r.readout () I (selection (I := I))=34*Fintype.card I ∧
    (LongCoreRings.coreSet (selection (I := I))).card=10*Fintype.card I ∧
    (∀ i : I, ∀ j : Fin 3,
      (ClosedModule.blockSlice (LongCoreRings.slice (selection (I := I)) i) j).card=8)

abbrev SourceClaim : Prop := ∀ {I : Type} [Fintype I] [DecidableEq I],
    (selection (I := I)).card=34*Fintype.card I ∧
    (LongCoreRings.coreSet (selection (I := I))).card=10*Fintype.card I ∧
    (∀ i : I, ∀ j : Fin 3,
      (ClosedModule.blockSlice (LongCoreRings.slice (selection (I := I)) i) j).card=8)

private theorem bad_law : ¬arena.Law bad := by
  intro h
  have hh := (h (I := Fin 0)).1
  change (selection (I := Fin 0)).card+1=34*Fintype.card (Fin 0) at hh
  simp at hh

def family : Registration arena SourceClaim where
  actual := realize signature observation noAnchor
  bridge := Iff.rfl
  variation := ⟨@counts,bad,bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let p : Type := Fin 1
    refine ⟨p,∅,{(0,0)},?_⟩
    change (∅ : Finset (Fin 1 × Fin 62)).card≠({(0,0)} : Finset (Fin 1 × Fin 62)).card
    simp

noncomputable def countsRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Graph.StarForming.LongCoreSignals.counts)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.StarForming.LongCoreSignals.counts.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.StarForming.LongCoreSignals.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation noAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.StarForming.LongCoreSignals
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.StarForming.LongCoreSignals
