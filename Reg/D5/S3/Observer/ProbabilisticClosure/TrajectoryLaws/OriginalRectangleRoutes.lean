import Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleRoutes

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
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleRoutes
open Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleRoutes
universe u

@[reducible] def arena : Arena where
  signature := signature
  Law V := ∀ {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : Presentation H) (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (_hc : HasOriginalCylinders J θ)
    (_hirr : ∀ i j : H, ∃ n : ℕ, 0 < ((θ.matrix false+θ.matrix true)^n) i j)
    (w : List Bool) (R : Rectangle (product θ w)) (r : H) (_hr : r ∈ R.rows),
    ∃ a : ∀ h, LabelledRoute θ h r,
      (a r).length = 0 ∧ (∀ h, (a h).length ≤ Fintype.card H) ∧
      (∀ h, w.head? = some false → (a h).length < Fintype.card H) ∧
      (∀ h, h ≠ r → w.head? = some true →
        (List.ofFn (a h).labels).getLast? = some false) ∧
      (let ε := selectedEpsilon θ w r a
       let b := w.length + Fintype.card H
       0 < ε ∧ ε ≤ 1 ∧
       (∀ (t : ℤ) (h : H), 0 < θ.initial h →
         ENNReal.ofReal ε ≤ futureLaw J t h (V.readout () b w)) ∧
       (∀ (t : ℤ) (h : H) (A : Set (ℕ → H × Bool)), MeasurableSet A →
         ENNReal.ofReal ε * J ((state t ⁻¹' {h}) ∩ (past t ⁻¹' A)) ≤
           J ((state t ⁻¹' {h}) ∩ (past t ⁻¹' A) ∩ (future t ⁻¹' V.readout () b w))))

private def toyRectangle : Rectangle (product MarkedPredictiveQuotient.toy.{u} []) where
  rows := Finset.univ
  cols := Finset.univ
  rows_nonempty := Finset.univ_nonempty
  cols_nonempty := Finset.univ_nonempty
  positive i _ j _ := by
    have he : i = j := Subsingleton.elim _ _
    simp [product, Matrix.one_apply, he]
  zero i j h := (h ⟨Finset.mem_univ i, Finset.mem_univ j⟩).elim

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let θ := MarkedPredictiveQuotient.toy.{u}
  obtain ⟨J,hc,_⟩ := original_law θ
  have hirr (i j : MarkedPredictiveQuotient.Toy.{u}) :
      ∃ n : ℕ, 0 < ((θ.matrix false+θ.matrix true)^n) i j := by
    exact ⟨1,by simp [θ, MarkedPredictiveQuotient.toy]⟩
  obtain ⟨a,_,_,_,_,hp⟩ := h θ (J : Measure _) hc hirr [] toyRectangle ⟨()⟩ (Finset.mem_univ _)
  obtain ⟨hε,_,hlower,_⟩ := hp
  have he := hlower 0 ⟨()⟩ (by norm_num [θ, MarkedPredictiveQuotient.toy])
  have hz : ENNReal.ofReal (selectedEpsilon θ [] ⟨()⟩ a) = 0 := by
    exact le_antisymm (by simpa [rejected,realize] using he) zero_le
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr hε)) hz

def family : Registration arena.{u} (type_of% (@irreducible_rectangle_occurrence.{u})) where
  actual := realize signature (fun _ b w => success w b) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@irreducible_rectangle_occurrence.{u},rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := OriginalRectangleOccurrence.family.dependence

def audit : Contract.Registration
    (@irreducible_rectangle_occurrence.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleRoutes.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleRoutes.family
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

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleRoutes
