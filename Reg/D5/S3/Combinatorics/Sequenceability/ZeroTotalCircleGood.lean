import D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood
universe u
abbrev signature : Signature where
  Params := Type u
  State X := List X × List X × List X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ s => (∃ p q, s.2.2 = p ++ s.1 ++ q) ∨
    (∃ p q, s.2.2 = p ++ s.2.1 ++ q)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} {a b c : List X}, (a ++ b).IsRotated c →
    R.readout () X (a,b,c)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (X := ULift.{u} Unit) (a := []) (b := []) (c := []) ⟨0,rfl⟩
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨ULift.{u} Unit, ([],[],[]), ([⟨()⟩],[⟨()⟩],[]), ?_⟩
  intro he
  have ht : actual.readout i (ULift.{u} Unit) ([],[],[]) := Or.inl ⟨[],[],rfl⟩
  rw [he] at ht
  rcases ht with ⟨p,q,hpq⟩ | ⟨p,q,hpq⟩
  all_goals
    have hh := congrArg List.length hpq
    simp at hh

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood.rotated_two_runs)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood.rotated_two_runs,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

-- Four slots attempted; exact raw source selection and escape binding are unfinished.
-- No declared_validated status is asserted by this source.
def audit : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood.rotated_two_runs)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood.rotated_two_runs.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ s => (∃ p q, s.2.2 = p ++ s.1 ++ q) ∨
      (∃ p q, s.2.2 = p ++ s.2.1 ++ q)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood
