import D5.S1.Words.Sequenceability.BipartiteGracefulExtension
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit of the complete two-block attachment statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.Sequenceability.BipartiteGracefulExtension

open _root_.D5.S1.Words.Sequenceability.BipartiteGracefulExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _s : ℕ, Σ _L : ℕ, Bool
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p q => lengths (q.map (blockMap p.1 p.2.1 p.2.2) ++
      [attachment p.1 p.2.1 p.2.2])) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s L : ℕ), 2 ≤ s → ∀ flip : Bool,
    ∃ q : List ℕ, Auxiliary s q ∧
      (R.readout () ⟨s,L,flip⟩ q).Perm (List.range' s (2*s+2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q,_,he⟩ := h 2 0 (by decide) false
  have hh := he.length_eq
  change 0 = (List.range' 2 6).length at hh
  simp at hh

def family : Registration arena (type_of% (@exists_two_block_attachment)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_two_block_attachment, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2,0,false⟩,[0],[1],?_⟩
    cases i
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@exists_two_block_attachment)
    (Realization signature) Unit Unit where
  unitName := .str
    `D5.S1.Words.Sequenceability.BipartiteGracefulExtension.exists_two_block_attachment
    "__information_unit"
  realizationName := `Reg.D5.S1.Words.Sequenceability.BipartiteGracefulExtension.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.BipartiteGracefulExtension
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body","body","body","body","arg","body","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg","fn","arg","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Sequenceability.BipartiteGracefulExtension
