import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4
import Reg.Support.DependentFamily

/-! The complete existential witness predicate is the source observation. -/

namespace Reg.D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4

open _root_.D5.S3.FiniteGroups
open _root_.D5.S3.FiniteGroups.SubgroupConjugacyRatio
open _root_.D5.S3.FiniteGroups.Heisenberg
open _root_.D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℕ × FiniteGroup
  State _ := FiniteGroup
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p H => Nat.card p.2.Carrier = p.1 ^ 6 ∧ Nat.card H.Carrier = p.1 ^ 6 ∧
    Nonempty (commutingGraph p.2.Carrier ≃g commutingGraph H.Carrier) ∧
    ¬ Isoclinic p.2.Carrier H.Carrier) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : ℕ, p.Prime → ∃ G H : FiniteGroup, R.readout () (p,G) H

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨G,H,hh⟩ := h 2 (by norm_num)
  exact hh

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
    obtain ⟨G,H,hgood⟩ := result 2 (by norm_num)
    refine ⟨(2,G),H,trivialGroup,?_⟩
    change (_ ∧ _ ∧ _ ∧ _) ≠ (_ ∧ _ ∧ _ ∧ _)
    intro he
    have hb := he.mp hgood
    have hc := hb.2.1
    norm_num [trivialGroup] at hc

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
    (fun _ p H => Nat.card p.2.Carrier = p.1 ^ 6 ∧ Nat.card H.Carrier = p.1 ^ 6 ∧
      Nonempty (commutingGraph p.2.Carrier ≃g commutingGraph H.Carrier) ∧
      ¬ Isoclinic p.2.Carrier H.Carrier) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some FiniteGroup
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4
    definition := some {
      owner := `D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4
      name := `D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4.ExactEvent
      path := #[] }
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","arg","body","arg","body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4
