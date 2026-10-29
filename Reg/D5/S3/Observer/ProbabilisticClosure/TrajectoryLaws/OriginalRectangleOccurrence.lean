import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence

/-! A dependent-family audit attempt for the complete occurrence theorem telescope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory LeanInformationAudit
open scoped BigOperators Classical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureScreening
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleMessages
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence
universe u

@[reducible] def signature : Signature where
  Params := ℕ
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set (ℕ → Bool)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ b w => success w b) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => ∅) Empty.elim

@[reducible] def arena : Arena where
  signature := signature
  Law V := ∀ {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Presentation H) (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (_hc : HasOriginalCylinders J θ) (w : List Bool) (R : Rectangle (product θ w))
    (r : H) (_hr : r ∈ R.rows) (a : ∀ h, LabelledRoute θ h r)
    (_ha : ∀ h, (a h).length ≤ Fintype.card H),
    let ε := selectedEpsilon θ w r a
    let b := w.length + Fintype.card H
    0 < ε ∧ ε ≤ 1 ∧
    (∀ (t : ℤ) (h : H), 0 < θ.initial h →
      ENNReal.ofReal ε ≤ futureLaw J t h (V.readout () b w)) ∧
    (∀ (t : ℤ) (h : H) (A : Set (ℕ → H × Bool)), MeasurableSet A →
      ENNReal.ofReal ε * J ((state t ⁻¹' {h}) ∩ (past t ⁻¹' A)) ≤
        J ((state t ⁻¹' {h}) ∩ (past t ⁻¹' A) ∩ (future t ⁻¹' V.readout () b w)))

private def toyRectangle : Rectangle (product MarkedPredictiveQuotient.toy.{u} []) where
  rows := Finset.univ
  cols := Finset.univ
  rows_nonempty := Finset.univ_nonempty
  cols_nonempty := Finset.univ_nonempty
  positive i _ j _ := by
    have he : i = j := Subsingleton.elim _ _
    simp [product, Matrix.one_apply, he]
  zero i j h := (h ⟨Finset.mem_univ i, Finset.mem_univ j⟩).elim

private def toyRoute (h : MarkedPredictiveQuotient.Toy.{u}) :
    LabelledRoute MarkedPredictiveQuotient.toy h ⟨()⟩ where
  length := 0
  states _ := ⟨()⟩
  labels i := nomatch i
  first := Subsingleton.elim _ _
  last := rfl
  positive i := nomatch i

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let θ := MarkedPredictiveQuotient.toy.{u}
  obtain ⟨J,hc,_⟩ := original_law θ
  obtain ⟨hε,_,hlower,_⟩ := h θ (J : Measure _) hc [] toyRectangle ⟨()⟩
    (Finset.mem_univ _) toyRoute (fun _ => Nat.zero_le _)
  have he := hlower 0 ⟨()⟩ (by norm_num [θ, MarkedPredictiveQuotient.toy])
  have hz : ENNReal.ofReal (selectedEpsilon θ [] ⟨()⟩ toyRoute) = 0 := by
    exact le_antisymm (by simpa [rejected,realize] using he) zero_le
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr hε)) hz

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨0,[],[true],?_⟩
  intro he
  have hh : (fun _ : ℕ => false) ∈ actual.readout () 0 [] := by
    simp [actual,realize,success]
  rw [he] at hh
  simpa [actual,realize,success] using hh

def family : Registration arena.{u} (type_of% (@original_rectangle_occurrence.{u})) where
  actual := realize signature (fun _ b w => success w b) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@original_rectangle_occurrence.{u},rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

def audit : Contract.Registration
    (@original_rectangle_occurrence.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ b w => success w b) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (List Bool)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence
