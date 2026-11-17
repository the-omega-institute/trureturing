import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4
import Reg.Support.DependentFamily

/-! A source cardinality observation retains the complete quantified assertion. -/

namespace Reg.D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4

open _root_.D5.S3.FiniteGroups
open _root_.D5.S3.FiniteGroups.SubgroupConjugacyRatio
open _root_.D5.S3.FiniteGroups.Heisenberg
open _root_.D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := FiniteGroup
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ H => Nat.card H.Carrier) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : ℕ, p.Prime → ∃ G H : FiniteGroup,
    Nat.card G.Carrier = p ^ 6 ∧ R.readout () () H = p ^ 6 ∧
      Nonempty (commutingGraph G.Carrier ≃g commutingGraph H.Carrier) ∧
      ¬ Isoclinic G.Carrier H.Carrier

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨G,H,hh⟩ := h 2 (by norm_num)
  have hzero := hh.2.1
  norm_num [rejected, realize] at hzero

private def trivialGroup : FiniteGroup where
  Carrier := Unit
  group := inferInstance
  finite := inferInstance

def family : Registration arena ExactEvent where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
    let two : FiniteGroup := ⟨Multiplicative (ZMod 2), inferInstance, inferInstance⟩
    refine ⟨(),trivialGroup,two,?_⟩
    change Nat.card Unit ≠ Nat.card (Multiplicative (ZMod 2))
    norm_num [Nat.card_eq_fintype_card]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) (Type 1) Unit where
  unitName := `D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4.result.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ H => Nat.card H.Carrier) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4
    definition := some {
      owner := `D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4
      name := `D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4.ExactEvent
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body","body","arg","body","arg","body","arg","fn","arg","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4
