import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Sequenceability.PairedQuantitativeOrdering

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Sequenceability.PairedQuantitativeOrdering

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.PairedQuantitativeOrdering
open _root_.D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
open _root_.D5.S3.Combinatorics.CircularWords.DisjointBlockContraction

noncomputable section

/-- Rank varies over the complete natural domain; the observed count is a natural number. -/
abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ r => (goodOrders r).card) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ {r : ℕ}, 12 ≤ r →
    ((2*r).factorial : ℚ)*lowerFraction r ≤ (R.readout () () r : ℚ) ∧
      0 < lowerFraction r ∧ 0 < (goodOrders r).card

abbrev sourceScope := type_of% (@quantitative_good_orders)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := quantitative_good_orders

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h (r := 12) (by decide)).1
  have hp := (quantitative_good_orders (r := 12) (by decide)).2.1
  have hh : (0:ℚ) < (24).factorial*lowerFraction 12 := mul_pos (by positivity) hp
  change ((24).factorial : ℚ)*lowerFraction 12 ≤ 0 at hb
  linarith

private theorem zero_rank_card : (goodOrders 0).card=1 := by
  have ha : alphabet 0=∅ := Finset.card_eq_zero.mp (by simp [alphabet_card])
  have hg : Good ([] : List (V 0)) := by
    intro i j hij hj hp
    simp only [List.length_nil] at hj
    omega
  simp [goodOrders,ha,orders,Finset.filter_singleton,hg]

private theorem count_dependence : (goodOrders 0).card ≠ (goodOrders 12).card := by
  rw [zero_rank_card]
  have hb := (quantitative_good_orders (r := 12) (by decide)).1
  norm_num [lowerFraction] at hb
  intro he
  rw [←he] at hb
  norm_num at hb

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(),0,12,count_dependence⟩

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@quantitative_good_orders) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PairedQuantitativeOrdering.quantitative_good_orders.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PairedQuantitativeOrdering.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ _ r => (goodOrders r).card) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.PairedQuantitativeOrdering
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Sequenceability.PairedQuantitativeOrdering
