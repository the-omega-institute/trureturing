import Reg.Support.DependentFamily
import D5.S0.Computability.OriginalClauseClassification

set_option autoImplicit false
namespace Reg.D5.S0.Computability.OriginalClauseClassification
open _root_.Complexity
open _root_.PredictiveThermodynamic.OriginalClasses
open _root_.D5.S3.ConceptDynamics.InformationEscape

/-- This source reconstruction retains the original NP-completeness antecedent.
It supplies no family registration or proof of that antecedent. -/
abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Language
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun (role : Bool) (_ : Unit) (A : Language) =>
      if role then DPComplete A else CoNPComplete A)
    (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (_hS : NPComplete S),
    R.readout false () U ∧ R.readout true () Q

abbrev sourceScope := type_of% (@lemma63)
theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := lemma63

/-- A negative instance of this complete conditional law entails the antecedent;
it cannot be obtained merely by erasing the conclusion. -/
theorem failure_requires_original_premise (R : DependentFamily.Realization signature)
    (h : ¬ arena.Law R) : NPComplete S := by
  classical
  by_contra hn
  exact h (fun hs => (hn hs).elim)

theorem variation_requires_original_premise
    (h : DependentFamily.Variation arena actual) : NPComplete S := by
  obtain ⟨_,bad,hbad⟩ := h
  exact failure_requires_original_premise bad hbad

end Reg.D5.S0.Computability.OriginalClauseClassification
