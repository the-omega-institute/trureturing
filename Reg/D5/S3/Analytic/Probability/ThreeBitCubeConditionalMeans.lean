import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import D5.S3.Analytic.Probability.ThreeBitCubeConditionalMeans
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Analytic.Probability.ThreeBitCubeConditionalMeans

open _root_.D5.S3.Analytic.Probability.ThreeBitCubeConditionalMeans
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

open scoped Classical

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def strict : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : PMF Cube) (h : Cube → ℝ)
    (_ : ∀ (T : Finset (Fin 3)) (a b : T → Fin 2), a ≤ b →
      0 < fiberMass p T a → 0 < fiberMass p T b → fiberMean p h T b ≤ fiberMean p h T a)
    (U : Set Cube) (_ : IsUpperSet U),
    r.readout () () (∑ x ∈ U.toFinset,
      (p x).toReal * (h x - ∑ y, (p y).toReal * h y)) 0

private theorem strict_fails : ¬ arena.Law strict := by
  intro h
  have hz (T : Finset (Fin 3)) (a : T → Fin 2) :
      fiberMean (PMF.pure (fun _ => 0)) (fun _ => 0) T a = 0 := by simp [fiberMean]
  have hfalse := h (PMF.pure (fun _ => 0)) (fun _ => 0)
    (fun T a b _ _ _ => by rw [hz, hz]) Set.univ isUpperSet_univ
  simpa [strict, realize] using hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hfalse : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le_of_gt zero_lt_one) hfalse

def source_registration :
    Registration arena (type_of% centered_sum_nonpos_of_antitone_fiber_means) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨centered_sum_nonpos_of_antitone_fiber_means, strict, strict_fails⟩
  sensitivity := ⟨fun i => ⟨strict,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, strict_fails⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      centered_sum_nonpos_of_antitone_fiber_means (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.ThreeBitCubeConditionalMeans.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.ThreeBitCubeConditionalMeans.source_registration
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
    (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.ThreeBitCubeConditionalMeans
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Analytic.Probability.ThreeBitCubeConditionalMeans
