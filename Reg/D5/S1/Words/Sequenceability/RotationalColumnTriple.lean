import D5.S1.Words.Sequenceability.RotationalColumnTriple
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact dependent-family audit of the universal directed column supplier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.Sequenceability.RotationalColumnTriple

open _root_.D5.S1.Words.Sequenceability.RotationalColumnTriple
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State p := ZMod (p-1) → ZMod p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod (p-1) → ZMod p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ), p.Prime → 7 ≤ p →
    ∃ d : ZMod (p-1) → ZMod p,
      Set.BijOn (R.readout () p d) Set.univ {x | x ≠ 0} ∧
      Set.BijOn (fun i => R.readout () p d (i+1)-R.readout () p d i)
        Set.univ {x | x ≠ 0} ∧
      R.readout () p d 1 = R.readout () p d 0 + R.readout () p d 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨d,hv,_,_⟩ := h 7 (by decide) (by decide)
  exact hv.1 (x := (0 : ZMod 6)) (Set.mem_univ _) rfl

def family : Registration arena (type_of% (@exists_rotational_column_triple)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_rotational_column_triple,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨7,(fun _ => 0),(fun _ => 1),?_⟩
    intro he
    have hv := congrFun he 0
    change (0 : ZMod 7) = 1 at hv
    exact (by decide : (0 : ZMod 7) ≠ 1) hv

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@exists_rotational_column_triple)
    (Realization signature) (ℕ → Type) Unit where
  unitName := .str
    `D5.S1.Words.Sequenceability.RotationalColumnTriple.exists_rotational_column_triple
    "__information_unit"
  realizationName := `Reg.D5.S1.Words.Sequenceability.RotationalColumnTriple.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun p : ℕ => ZMod (p-1) → ZMod p)
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.RotationalColumnTriple
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","arg","body","fn","arg","fn","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Sequenceability.RotationalColumnTriple
