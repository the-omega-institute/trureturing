import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.JointDominatedConvergence
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
noncomputable section
universe u
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.JointDominatedConvergence
open MeasureTheory Filter LeanInformationAudit
open scoped Topology
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.JointDominatedConvergence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Parameters where
  Ω : Type u
  ambient : MeasurableSpace Ω
  μ : @Measure Ω ambient
  ℱ : ℕ → MeasurableSpace Ω
  y : ℕ → Ω → ℝ
  yLim : Ω → ℝ
  g : Ω → ℝ

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.Ω
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℕ × ℕ) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p => by
    letI := p.ambient
    exact fun ω k => p.μ[p.y k.1 | p.ℱ k.2] ω) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hℱ : Antitone ℱ)
    (h_le : ∀ j, ℱ j ≤ m0)
    (y : ℕ → Ω → ℝ) (yLim g : Ω → ℝ)
    (_hy : ∀ n, Measurable (y n)) (_hyLim : Measurable yLim)
    (_hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => y n ω) atTop (𝓝 (yLim ω)))
    (_hg : Integrable g μ) (_hbound : ∀ n, ∀ᵐ ω ∂μ, |y n ω| ≤ g ω),
    (∀ᵐ ω ∂μ, Tendsto
      (R.readout () (@Parameters.mk Ω m0 μ ℱ y yLim g) ω)
      atTop (𝓝 (μ[yLim | ⨅ j, ℱ j] ω))) ∧
    Tendsto (fun k : ℕ × ℕ => ∫ ω,
      |μ[y k.1 | ℱ k.2] ω - μ[yLim | ⨅ j, ℱ j] ω| ∂μ)
      atTop (𝓝 0)

private theorem actual_law : arena.{u}.Law actual :=
  @tendsto_condExp_of_dominated_convergence.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  let μ : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  let ℱ : ℕ → MeasurableSpace (ULift.{u} Unit) := fun _ => ⊤
  have hanti : Antitone ℱ := fun _ _ _ => le_rfl
  have ht := h (μ := μ) ℱ hanti (fun _ => le_rfl)
    (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => measurable_const) measurable_const
    (Eventually.of_forall fun _ => tendsto_const_nhds)
    (integrable_zero _ _ _) (fun _ => Eventually.of_forall fun _ => by simp)
  have ht' : Tendsto (1 : (ℕ × ℕ) → ℝ) atTop (𝓝 0) := by
    simpa [rejected, realize, condExp_zero, ℱ, μ] using ht.1
  have hc : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht'
  norm_num at hc

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  letI : MeasurableSpace (ULift.{u} Bool) := ⊤
  let μ : Measure (ULift.{u} Bool) := Measure.dirac (ULift.up false)
  let f : ULift.{u} Bool → ℝ := fun x => if x.down then 1 else 0
  let ℱ : ℕ → MeasurableSpace (ULift.{u} Bool) := fun _ => ⊤
  let p : Parameters.{u} := ⟨ULift.{u} Bool, ⊤, μ, ℱ, (fun _ => f), f, (fun _ => 1)⟩
  refine ⟨p, ULift.up false, ULift.up true, ?_⟩
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hfi : Integrable f μ := by
    apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    exact Eventually.of_forall fun x => by dsimp [f]; split <;> norm_num
  have he : μ[f | ⊤] = f := condExp_of_stronglyMeasurable le_rfl hf hfi
  intro hc
  have hh := congrArg (fun a : (ℕ × ℕ) → ℝ => a (0, 0)) hc
  change μ[f | ⊤] (ULift.up false) = μ[f | ⊤] (ULift.up true) at hh
  rw [he] at hh
  norm_num [f] at hh

def familyRegistration : Registration arena.{u} (type_of% (@tendsto_condExp_of_dominated_convergence.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@tendsto_condExp_of_dominated_convergence.{u})
      (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.JointDominatedConvergence.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.JointDominatedConvergence.familyRegistration
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
    exact fun ω k => p.μ[p.y k.1 | p.ℱ k.2] ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.JointDominatedConvergence
    definition := none
    coordinates := #[0,1,2,4,7,8,9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "fn", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.JointDominatedConvergence
