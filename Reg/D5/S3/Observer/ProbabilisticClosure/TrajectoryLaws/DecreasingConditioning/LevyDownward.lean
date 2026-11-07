import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.LevyDownward
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
noncomputable section
universe u
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.LevyDownward
open MeasureTheory Filter LeanInformationAudit
open scoped Topology ENNReal ProbabilityTheory
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Parameters where
  Ω : Type u
  ambient : MeasurableSpace Ω
  μ : @Measure Ω ambient
  𝔽 : ℕ → MeasurableSpace Ω
  f : Ω → ℝ

abbrev signature : Signature where
  Params := Parameters
  State p := p.Ω
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p => by
    letI := p.ambient
    exact fun ω n => p.μ[p.f | p.𝔽 n] ω) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le0 : 𝔽 0 ≤ (inferInstance : MeasurableSpace Ω)) (f : Ω → ℝ),
    (∀ᵐ ω ∂μ, Tendsto
      (R.readout () (@Parameters.mk Ω m0 μ 𝔽 f) ω) atTop
      (𝓝 (μ[f | ⨅ n, 𝔽 n] ω))) ∧
      Tendsto (fun n => eLpNorm (μ[f | 𝔽 n] - μ[f | ⨅ n, 𝔽 n]) 1 μ)
        atTop (𝓝 0)

private theorem actual_law : arena.Law actual :=
  @tendsto_ae_and_eLpNorm_condExp_iInf.{u}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  let μ : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  let 𝔽 : ℕ → MeasurableSpace (ULift.{u} Unit) := fun _ => ⊤
  have hanti : Antitone 𝔽 := fun _ _ _ => le_rfl
  have ht := h hanti (by exact le_rfl) (fun _ => 0)
  simpa [rejected, realize, condExp_zero, 𝔽, μ] using ht.1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  letI : MeasurableSpace (ULift.{u} Bool) := ⊤
  let μ : Measure (ULift.{u} Bool) := Measure.dirac (ULift.up false)
  let f : ULift.{u} Bool → ℝ := fun x => if x.down then 1 else 0
  let 𝔽 : ℕ → MeasurableSpace (ULift.{u} Bool) := fun _ => ⊤
  let p : Parameters := ⟨ULift.{u} Bool, ⊤, μ, 𝔽, f⟩
  refine ⟨p, ULift.up false, ULift.up true, ?_⟩
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hfi : Integrable f μ := by
    apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    exact Eventually.of_forall fun x => by dsimp [f]; split <;> norm_num
  have he : μ[f | ⊤] = f := condExp_of_stronglyMeasurable le_rfl hf hfi
  intro hc
  have hh := congrArg (fun a : ℕ → ℝ => a 0) hc
  change μ[f | ⊤] (ULift.up false) = μ[f | ⊤] (ULift.up true) at hh
  rw [he] at hh
  norm_num [f] at hh

def familyRegistration : Registration arena
    (type_of% (@tendsto_ae_and_eLpNorm_condExp_iInf.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@tendsto_ae_and_eLpNorm_condExp_iInf.{u})
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.LevyDownward.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.LevyDownward.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => by
    letI := p.ambient
    exact fun ω n => p.μ[p.f | p.𝔽 n] ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.LevyDownward
    definition := none
    coordinates := #[0,1,2,4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "body"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.LevyDownward
