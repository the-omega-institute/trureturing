import D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound observations of total native words. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility

open _root_.D5.S0.History.Spacetime.ArchiveCarrier
open _root_.D5.S3.ConceptDynamics.Spacetime
open _root_.D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ComplementCharge TotalCopyNormalization RegionFilterQExpressibility
open scoped BigOperators

noncomputable section

@[reducible] def signature : Signature where
  Params := Word
  State _ := B
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ w X => (contextDenote nativeSignature w X).map (fun Y => q Y.val))
  (fun e => nomatch e)

def timeSum (X : B) : Int :=
  ∑ e ∈ X.val.2.val, (X.val.1.archive.attributes e).time

def rejected : Realization signature := realize signature
  (fun _ _ X => some (timeSum X)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ w : Word,
    (∀ X : B, ∃ Y, contextDenote nativeSignature w X = some Y) →
    ∃ c : Int, ∀ (p : Fin 3 → Int) (t t' : Int), t < c → t' < c →
      ∃ X Y : B, SelectedVariant X Y p t t' ∧
        F.readout 0 w X = F.readout 1 w Y

private theorem positive : arena.Law actual := total_word_saturation

private theorem selected_times (X Y : B) (p : Fin 3 → Int) (t t' : Int)
    (pair : SelectedVariant X Y p t t') : timeSum X = t ∧ timeSum Y = t' := by
  obtain ⟨h, selected, _, _, ht, ht'⟩ := pair
  have selected' : Y.val.2.val = {h.eventEquiv h.exceptional} := by
    rw [← h.selection_image, selected, Finset.map_singleton]
    rfl
  constructor
  · unfold timeSum
    rw [selected, Finset.sum_singleton]
    exact ht
  · unfold timeSum
    rw [selected', Finset.sum_singleton]
    exact ht'

private theorem negative : ¬ arena.Law rejected := by
  intro law
  obtain ⟨c, hc⟩ := law [] (fun X => ⟨X, rfl⟩)
  obtain ⟨X, Y, pair, same⟩ := hc (fun _ => 0) (c - 1) (c - 2) (by omega) (by omega)
  have values := Option.some.inj same
  obtain ⟨hx, hy⟩ := selected_times X Y _ _ _ pair
  change timeSum X = timeSum Y at values
  omega

private theorem selected_charges (X Y : B) (p : Fin 3 → Int) (t t' : Int)
    (pair : SelectedVariant X Y p t t') : q X.val = 1 ∧ q Y.val = 1 := by
  obtain ⟨h, selected, _, positive, _, _⟩ := pair
  have selected' : Y.val.2.val = {h.eventEquiv h.exceptional} := by
    rw [← h.selection_image, selected, Finset.map_singleton]
    rfl
  have positive' := h.positive_eq.trans positive
  constructor
  · change (∑ e ∈ X.val.2.val, contribution X.val.1 e) = 1
    rw [selected, Finset.sum_singleton]
    simp only [contribution, positive, ite_true]
  · change (∑ e ∈ Y.val.2.val, contribution Y.val.1 e) = 1
    rw [selected', Finset.sum_singleton]
    simp only [contribution, positive', ite_true]

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j w X => if j = i then (actual.readout j w X).map (fun q => q + 1)
    else actual.readout j w X) (fun e => nomatch e)

private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  obtain ⟨c, hc⟩ := law [] (fun X => ⟨X, rfl⟩)
  obtain ⟨X, Y, pair, same⟩ := hc (fun _ => 0) (c - 1) (c - 2) (by omega) (by omega)
  have same' : (if (0 : Fin 2) = i then some (q X.val + 1) else some (q X.val)) =
      (if (1 : Fin 2) = i then some (q Y.val + 1) else some (q Y.val)) := same
  obtain ⟨hx, hy⟩ := selected_charges X Y _ _ _ pair
  rw [hx, hy] at same'
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> norm_num at same'

def evidence : Registration arena (type_of% (@total_word_saturation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext w X
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨[], ComplementFibers.balancedSection 3 0,
      ComplementFibers.balancedSection 3 1, ?_⟩
    change some (q (ComplementFibers.balancedSection 3 0).val) ≠
      some (q (ComplementFibers.balancedSection 3 1).val)
    have h0 : q (ComplementFibers.balancedSection 3 0).val = 0 :=
      ComplementFibers.balancedSection_readout 3 0
    have h1 : q (ComplementFibers.balancedSection 3 1).val = 1 :=
      ComplementFibers.balancedSection_readout 3 1
    rw [h0, h1]
    decide

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility.total_word_saturation)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility.total_word_saturation,
  realizationName := `Reg.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility.evidence,
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "body", "body", "body",
        "body", "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "body", "body", "body", "body", "body",
        "body", "arg", "body", "arg", "body", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility
