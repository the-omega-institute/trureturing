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
open Classical

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

namespace TailConstruction

@[reducible] def signature : Signature where
  Params := Σ _ : Region, Σ _ : Int, Int
  State _ := B
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i p X => Fin.cases (q (tailConstruction p.1 p.2.2 X).val)
    (fun _ => regionReadout p.1 X) i) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ (R : Region) (c k : Int), TailAt R c → k ≤ c - 1 → ∀ X : B,
    F.readout 0 ⟨R,c,k⟩ X = F.readout 1 ⟨R,c,k⟩ X

private theorem positive : arena.Law actual := tail_construction_q

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p X => if j = i then actual.readout j p X + 1
    else actual.readout j p X) (fun e => nomatch e)

private theorem emptyTail : TailAt (∅ : Region) 0 := by
  intro p t t' ht ht'
  simp

private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  have h := law ∅ 0 (-1) emptyTail (by omega) unitBalanced
  have hp := positive ∅ 0 (-1) emptyTail (by omega) unitBalanced
  change (if (0 : Fin 2) = i then q (tailConstruction ∅ (-1) unitBalanced).val + 1
    else q (tailConstruction ∅ (-1) unitBalanced).val) =
    (if (1 : Fin 2) = i then regionReadout ∅ unitBalanced + 1
    else regionReadout ∅ unitBalanced) at h
  change q (tailConstruction ∅ (-1) unitBalanced).val = regionReadout ∅ unitBalanced at hp
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> norm_num at h <;> omega

private theorem univTail : TailAt (Set.univ : Region) 0 := by
  intro p t t' ht ht'
  simp

private theorem univ_readout (X : B) : regionReadout Set.univ X = q X.val := by
  simp [regionReadout, q, readout, charge]

def evidence : Registration arena (type_of% (@tail_construction_q)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p X
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    refine ⟨⟨Set.univ,0,-1⟩, ComplementFibers.balancedSection 3 0,
      ComplementFibers.balancedSection 3 1, ?_⟩
    have h0 := tail_construction_q Set.univ 0 (-1) univTail (by omega)
      (ComplementFibers.balancedSection 3 0)
    have h1 := tail_construction_q Set.univ 0 (-1) univTail (by omega)
      (ComplementFibers.balancedSection 3 1)
    have hq0 : q (ComplementFibers.balancedSection 3 0).val = 0 :=
      ComplementFibers.balancedSection_readout 3 0
    have hq1 : q (ComplementFibers.balancedSection 3 1).val = 1 :=
      ComplementFibers.balancedSection_readout 3 1
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;>
      simp only [actual, realize, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] <;>
      simp only [h0, h1, univ_readout, hq0, hq1] <;> decide

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility.tail_construction_q)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility.tail_construction_q
  realizationName := `Reg.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility.TailConstruction.evidence
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
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration
end TailConstruction

namespace Classification

@[reducible] def signature : Signature where
  Params := Unit
  State _ := Region
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i _ R => Fin.cases (decide (QExpressible R)) (fun _ => decide (Tail R)) i)
  (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ R : Region, F.readout 0 () R = true ↔ F.readout 1 () R = true

private theorem positive : arena.Law actual := by
  intro R
  change decide (QExpressible R) = true ↔ decide (Tail R) = true
  simpa only [decide_eq_true_eq] using q_expressible_iff_tail R

private theorem empty_tail : Tail (∅ : Region) := ⟨0, by
  intro p t t' ht ht'
  simp⟩

private def alternating : Region := {z | z.1 % 2 = 0}

private theorem alternating_not_tail : ¬ Tail alternating := by
  rintro ⟨c,hc⟩
  have h := hc (fun _ => 0) (2 * (min c 0 - 1)) (2 * (min c 0 - 1) - 1)
    (by omega) (by omega)
  change (2 * (min c 0 - 1)) % 2 = 0 ↔ (2 * (min c 0 - 1) - 1) % 2 = 0 at h
  omega

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p R => if j = i then !(actual.readout j p R) else actual.readout j p R)
  (fun e => nomatch e)

private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  have h := law ∅
  have he := (q_expressible_iff_tail ∅).mpr empty_tail
  change ((if (0 : Fin 2) = i then !(decide (QExpressible ∅))
    else decide (QExpressible ∅)) = true ↔
    (if (1 : Fin 2) = i then !(decide (Tail ∅)) else decide (Tail ∅)) = true) at h
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;>
    simp [he, empty_tail] at h

def evidence : Registration arena (type_of% (@q_expressible_iff_tail)) where
  actual := actual
  bridge := by
    change (∀ R : Region, QExpressible R ↔ Tail R) ↔
      ∀ R : Region, decide (QExpressible R) = true ↔ decide (Tail R) = true
    simp only [decide_eq_true_eq]
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p R
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    refine ⟨(), ∅, alternating, ?_⟩
    have he := (q_expressible_iff_tail ∅).mpr empty_tail
    have hn : ¬ QExpressible alternating := fun h =>
      alternating_not_tail ((q_expressible_iff_tail alternating).mp h)
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · change decide (QExpressible ∅) ≠ decide (QExpressible alternating)
      simp [he, hn]
    · change decide (Tail ∅) ≠ decide (Tail alternating)
      simp [empty_tail, alternating_not_tail]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility.q_expressible_iff_tail)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility.q_expressible_iff_tail
  realizationName := `Reg.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility.Classification.evidence
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
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }, {
      path := #["body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration
end Classification

end
end Reg.D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility
