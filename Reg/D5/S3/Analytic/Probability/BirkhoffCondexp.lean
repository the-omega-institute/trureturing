import D5.S3.Analytic.Probability.BirkhoffCondexp
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Analytic.Probability.BirkhoffCondexp

open MeasureTheory MeasurableSpace Filter LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Probability.BirkhoffCondexp

structure Parameters where
  α : Type u
  ambient : MeasurableSpace α
  μ : @Measure α ambient
  T : α → α
  g : α → ℝ

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x n ↦ birkhoffAverage ℝ p.T p.g n x) (fun e ↦ nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ ↦ 1) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [m : MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {T : α → α} {g : α → ℝ}, MeasurePreserving T μ μ → Integrable g μ →
    (∀ᵐ x ∂μ, Tendsto (R.readout () (@Parameters.mk α m μ T g) x)
      atTop (𝓝 (μ[g|invariants T] x))) ∧
    Tendsto (fun n ↦ ∫ x, |R.readout () (@Parameters.mk α m μ T g) x n -
      μ[g|invariants T] x| ∂μ) atTop (𝓝 0)

private theorem actual_law : arena.{u}.Law actual := @birkhoff_conditional_expectation.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  let μ : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  have ht := h μ (T := id) (g := fun _ ↦ 0) (measurePreserving_id μ) (integrable_zero _ _ _)
  simpa [rejected, realize, condExp_zero, μ] using ht.1

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  letI : MeasurableSpace (ULift.{u} Bool) := ⊤
  let μ : Measure (ULift.{u} Bool) := Measure.dirac (ULift.up false)
  let g : ULift.{u} Bool → ℝ := fun x ↦ if x.down then 1 else 0
  let p : Parameters.{u} := ⟨ULift.{u} Bool, ⊤, μ, id, g⟩
  refine ⟨p, ULift.up false, ULift.up true, ?_⟩
  intro hc
  have hh := congrArg (fun a : ℕ → ℝ ↦ a 1) hc
  change birkhoffAverage ℝ id g 1 (ULift.up false) =
    birkhoffAverage ℝ id g 1 (ULift.up true) at hh
  norm_num [birkhoffAverage_one_apply, g] at hh

def familyRegistration : Registration arena.{u}
    (type_of% (@birkhoff_conditional_expectation.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i ↦ ⟨rejected,
    fun j h ↦ (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e ↦ nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@birkhoff_conditional_expectation.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Probability.BirkhoffCondexp.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.BirkhoffCondexp.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p x n ↦ birkhoffAverage ℝ p.T p.g n x) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Probability.BirkhoffCondexp
