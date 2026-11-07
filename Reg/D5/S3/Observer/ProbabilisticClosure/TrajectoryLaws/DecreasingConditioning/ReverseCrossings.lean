import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.ReverseCrossings
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
noncomputable section
universe u
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.ReverseCrossings
open MeasureTheory Filter LeanInformationAudit
open scoped ENNReal
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Parameters where
  Ω : Type u
  ambient : MeasurableSpace Ω
  μ : @Measure Ω ambient
  𝔽 : ℕ → MeasurableSpace Ω
  f : Ω → ℝ
  a b : ℝ

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
  realize signature (fun _ _ _ n => if Even n then (-1 : ℝ) else 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) (a b : ℝ) (hab : a < b),
    ∃ C : ENNReal, C < ⊤ ∧
      ∫⁻ ω, upcrossings (↑a) (↑b)
        (R.readout () (@Parameters.mk Ω m0 μ 𝔽 f a b)) ω ∂μ ≤ C

private theorem actual_law : arena.Law actual :=
  @exists_lintegral_upcrossings_condExp_le.{u}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  let μ : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  let 𝔽 : ℕ → MeasurableSpace (ULift.{u} Unit) := fun _ => ⊤
  have hanti : Antitone 𝔽 := fun _ _ _ => le_rfl
  let bad : ℕ → ℝ := fun n => if Even n then (-1 : ℝ) else 1
  have hlow : ∃ᶠ n in atTop, bad n < (-1 / 2 : ℝ) := by
    exact frequently_even.mono fun n hn => by simp [bad, hn]
  have hupp : ∃ᶠ n in atTop, (1 / 2 : ℝ) < bad n := by
    exact frequently_odd.mono fun n hn => by simp [bad, hn]
  have htop : upcrossings (-1 / 2 : ℝ) (1 / 2 : ℝ) bad (ULift.up ()) = ⊤ :=
    upcrossings_eq_top_of_frequently_lt (by norm_num) hlow hupp
  obtain ⟨C, hC, hbound⟩ := h hanti (fun _ => le_rfl) (fun _ => 0)
    (integrable_zero _ _ _) (-1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num)
  have htop_le : (⊤ : ENNReal) ≤ C := by
    simpa [rejected, realize, bad, μ, htop] using hbound
  exact (not_lt_of_ge htop_le) hC

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  letI : MeasurableSpace (ULift.{u} Bool) := ⊤
  let μ : Measure (ULift.{u} Bool) := Measure.dirac (ULift.up false)
  let f : ULift.{u} Bool → ℝ := fun x => if x.down then 1 else 0
  let 𝔽 : ℕ → MeasurableSpace (ULift.{u} Bool) := fun _ => ⊤
  let p : Parameters := ⟨ULift.{u} Bool, ⊤, μ, 𝔽, f, 0, 1⟩
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
    (type_of% (@exists_lintegral_upcrossings_condExp_le.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@exists_lintegral_upcrossings_condExp_le.{u})
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.ReverseCrossings.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.ReverseCrossings.familyRegistration
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
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.ReverseCrossings
    definition := none
    coordinates := #[0,1,2,4,7,8,9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "body"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.ReverseCrossings
