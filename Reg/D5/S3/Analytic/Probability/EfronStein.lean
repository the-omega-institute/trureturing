import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.EfronStein
import Reg.Support.DependentFamily

/-! The full Efron–Stein telescope is observed through real comparison. -/

namespace Reg.D5.S3.Analytic.Probability.EfronStein
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe u v
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ lower upper => lower ≤ upper) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ lower upper => lower < upper) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {Ω : ι → Type v}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {F : (∀ i, Ω i) → ℝ} (_hF : Measurable F) {M : ℝ} (_hM : ∀ x, |F x| ≤ M),
    r.readout () () (Var[F; Measure.pi μ])
      ((1 / 2) * ∑ i, ∫ x, ∫ y, (F (Function.update x i y) - F x) ^ 2 ∂(μ i)
        ∂(Measure.pi μ))

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  have hbad := h (ι := ULift.{u} (Fin 0)) (Ω := fun _ => ULift.{v} Unit)
    (fun _ => Measure.dirac (ULift.up ())) (F := fun _ => (0 : ℝ)) measurable_const
    (M := 0) (fun _ => by simp)
  simpa [rejected, realize, variance_eq_integral measurable_const.aemeasurable] using hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hfalse : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le_of_gt zero_lt_one) hfalse

def source_registration :
    Registration arena.{u,v} (type_of% @Homogenization.efronStein_pi.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Homogenization.efronStein_pi.{u,v}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@Homogenization.efronStein_pi.{u,v}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.EfronStein.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.EfronStein.source_registration
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
    (fun _ _ lower upper => lower ≤ upper) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.EfronStein
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Analytic.Probability.EfronStein
