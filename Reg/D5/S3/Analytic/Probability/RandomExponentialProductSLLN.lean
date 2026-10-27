import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.RandomExponentialProductSLLN
import Reg.Support.DependentFamily

/-! Source-bound audit of the positive tolerance in the random-product strong law. -/

namespace Reg.D5.S3.Analytic.Probability.RandomExponentialProductSLLN

open _root_.D5.S3.Analytic.Probability.RandomExponentialProductSLLN
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe strict real comparison at the lower endpoint of the tolerance condition. -/
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
  realize signature (fun _ _ lower upper => lower < upper) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

/-- Preserve all spaces, probability hypotheses, and uniform strong convergence. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ (𝕜 e α : Type) [RCLike 𝕜] [NormedAddCommGroup e] [NormedSpace 𝕜 e]
      [CompleteSpace e] [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ],
      letI := NormedAlgebra.restrictScalars ℝ 𝕜 (e →L[𝕜] e)
      letI : MeasurableSpace (e →L[𝕜] e) := borel (e →L[𝕜] e)
      ∀ (a : ℕ → α → e →L[𝕜] e),
        (∀ i, AEStronglyMeasurable (a i) μ) →
        Pairwise (fun i j => IndepFun (a i) (a j) μ) →
        (∀ i, IdentDistrib (a i) (a 0) μ μ) →
        ∀ (m : ℝ), (∀ i, ∀ᵐ ω ∂μ, ‖a i ω‖ ≤ m) →
        ∀ (x : e) (t : ℝ), 0 ≤ t → ∀ᵐ ω ∂μ,
          ∀ ε : ℝ, R.readout () () 0 ε →
            ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) t,
              ‖(randomProduct a n s ω -
                NormedSpace.exp (((s : ℝ) : 𝕜) • ∫ z, a 0 z ∂μ)) x‖ < ε

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := @h ℝ ℝ Unit inferInstance inferInstance inferInstance inferInstance
    inferInstance (Measure.dirac ()) inferInstance (fun _ _ => 0)
    (fun _ => aestronglyMeasurable_const)
    (fun _ _ _ => indepFun_const_left 0 _)
    (fun _ => IdentDistrib.refl aemeasurable_const) 0 (by simp)
    0 0 (by norm_num)
  obtain ⟨ω, hω⟩ := hbad.exists
  obtain ⟨n, hn⟩ := (hω 0 True.intro).exists
  exact (not_lt_of_ge (norm_nonneg _)) (hn 0 (by simp))

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hlt : (0 : ℝ) < 1 := zero_lt_one
  change (fun upper : ℝ => 0 < upper) = (fun upper : ℝ => 1 < upper) at h
  have hfalse : (1 : ℝ) < 1 := (congrFun h 1).mp hlt
  exact (lt_irrefl 1) hfalse

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.Probability.RandomExponentialProductSLLN.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Probability.RandomExponentialProductSLLN.unit
  realizationName :=
    `Reg.D5.S3.Analytic.Probability.RandomExponentialProductSLLN.source_registration
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
    (fun _ _ lower upper => lower < upper) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.RandomExponentialProductSLLN
    definition := some {
      owner := `D5.S3.Analytic.Probability.RandomExponentialProductSLLN
      name := `D5.S3.Analytic.Probability.RandomExponentialProductSLLN.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "domain", "fn", "fn"]
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
end Reg.D5.S3.Analytic.Probability.RandomExponentialProductSLLN
