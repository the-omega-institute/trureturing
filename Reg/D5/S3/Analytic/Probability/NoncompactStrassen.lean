import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport
import D5.S3.Analytic.Probability.NoncompactStrassen

/-! Source-bound escape audit for scalar integrable martingale transport. -/

open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit

noncomputable section
namespace Reg.D5.S3.Analytic.Probability.NoncompactStrassen

namespace strassen_iff
abbrev arena : Arena where
  signature := ScalarMeasure
  Law r := source_law% Econlib.Probability.NoncompactStrassen.strassen_iff
    replacing (@ProbabilityMeasure.toMeasure ℝ inferInstance)
    with (r.readout () ())

theorem source_bridge :
    (type_of% @Econlib.Probability.NoncompactStrassen.strassen_iff) ↔ arena.Law scalarMeasureActual := Iff.rfl

theorem actual_law : arena.Law scalarMeasureActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.NoncompactStrassen.strassen_iff
/-- The transplanted law fails when both supplied marginals are the zero measure. -/
def rejected : Realization ScalarMeasure :=
  realize ScalarMeasure (fun _ _ _ => 0) (fun e => nomatch e)

private def pointMass (x : ℝ) : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : Integrable (fun x : ℝ => x) (0 : Measure ℝ) := by simp
  have hiff := h (pointMass 0) (pointMass 0) hzero hzero
  obtain ⟨π, hfst, _, _⟩ := hiff.mp ⟨rfl, fun _ _ _ _ => le_rfl⟩
  have hp : π.toMeasure.map Prod.fst = (0 : Measure ℝ) := hfst
  have huniv := congrArg (fun μ : Measure ℝ => μ Set.univ) hp
  rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ, measure_univ] at huniv
  simp at huniv

theorem dependence : ObservationalDependence ScalarMeasure scalarMeasureActual := by
  intro i
  refine ⟨(), pointMass 0, pointMass 1, ?_⟩
  intro heq
  have hsingle := congrArg (fun μ : Measure ℝ => μ ({0} : Set ℝ)) heq
  change Measure.dirac (0 : ℝ) {0} = Measure.dirac (1 : ℝ) {0} at hsingle
  rw [Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)] at hsingle
  norm_num at hsingle

def source_registration : Registration arena
    (type_of% @Econlib.Probability.NoncompactStrassen.strassen_iff) where
  actual := scalarMeasureActual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@Econlib.Probability.NoncompactStrassen.strassen_iff) (Realization ScalarMeasure) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.NoncompactStrassen.strassen_iff.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.NoncompactStrassen.strassen_iff.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ScalarMeasure (fun _ _ μ => μ.toMeasure) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.NoncompactStrassen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "domain", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end strassen_iff

end Reg.D5.S3.Analytic.Probability.NoncompactStrassen
end
