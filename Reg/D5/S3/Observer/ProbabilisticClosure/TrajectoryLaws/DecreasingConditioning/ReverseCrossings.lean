import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.ReverseCrossings
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Order.Filter.AtTopBot.ModEq
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
noncomputable section
universe u
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.ReverseCrossings
open MeasureTheory Filter LeanInformationAudit
open scoped ENNReal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Parameters where
  Ω : Type u
  ambient : MeasurableSpace Ω
  μ : @Measure Ω ambient
  𝔽 : ℕ → MeasurableSpace Ω
  f : Ω → ℝ
  a : ℝ
  b : ℝ
  n : ℕ

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.Ω
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p => by
    letI := p.ambient
    exact p.μ[p.f | p.𝔽 p.n]) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => if Even p.n then (-1 : ℝ) else 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {𝔽 : ℕ → MeasurableSpace Ω} [IsFiniteMeasure μ]
    (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) (a b : ℝ) (hab : a < b),
    ∃ C : ENNReal, C < ⊤ ∧
      ∫⁻ ω, upcrossings (↑a) (↑b)
        (fun n ω => R.readout () (@Parameters.mk Ω m0 μ 𝔽 f a b n) ω) ω ∂μ ≤ C

private theorem actual_law : arena.{u}.Law actual :=
  @exists_lintegral_upcrossings_condExp_le.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  let μ : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  let 𝔽 : ℕ → MeasurableSpace (ULift.{u} Unit) := fun _ => ⊤
  have hanti : Antitone 𝔽 := fun _ _ _ => le_rfl
  let bad : ℕ → ULift.{u} Unit → ℝ := fun n _ => if Even n then (-1 : ℝ) else 1
  have hlow : ∃ᶠ n in atTop, bad n (ULift.up ()) < (-1 / 2 : ℝ) := by
    exact Nat.frequently_even.mono fun n hn => by norm_num [bad, hn]
  have hupp : ∃ᶠ n in atTop, (1 / 2 : ℝ) < bad n (ULift.up ()) := by
    exact Nat.frequently_odd.mono fun n hn => by norm_num [bad, Nat.not_even_iff_odd.mpr hn]
  have htop : upcrossings (-1 / 2 : ℝ) (1 / 2 : ℝ) bad (ULift.up ()) = ⊤ :=
    upcrossings_eq_top_of_frequently_lt (by norm_num) hlow hupp
  obtain ⟨C, hC, hbound⟩ := h (μ := μ) hanti (fun _ => le_rfl) (fun _ => 0)
    (integrable_zero _ _ _) (-1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num)
  change (∫⁻ ω, upcrossings (-1 / 2 : ℝ) (1 / 2 : ℝ) bad ω ∂μ) ≤ C at hbound
  have htop_le : upcrossings (-1 / 2 : ℝ) (1 / 2 : ℝ) bad (ULift.up ()) ≤ C := by
    simpa [μ] using hbound
  rw [htop] at htop_le
  exact (not_lt_of_ge htop_le) hC

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  letI : MeasurableSpace (ULift.{u} Bool) := ⊤
  let μ : Measure (ULift.{u} Bool) := Measure.dirac (ULift.up false)
  let f : ULift.{u} Bool → ℝ := fun x => if x.down then 1 else 0
  let 𝔽 : ℕ → MeasurableSpace (ULift.{u} Bool) := fun _ => ⊤
  let p : Parameters.{u} := ⟨ULift.{u} Bool, ⊤, μ, 𝔽, f, 0, 1, 0⟩
  refine ⟨p, ULift.up false, ULift.up true, ?_⟩
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hfi : Integrable f μ := by
    apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    exact Eventually.of_forall fun x => by dsimp [f]; split <;> norm_num
  have he : μ[f | ⊤] = f := condExp_of_stronglyMeasurable le_rfl hf hfi
  intro hc
  change μ[f | ⊤] (ULift.up false) = μ[f | ⊤] (ULift.up true) at hc
  rw [he] at hc
  norm_num [f] at hc

def familyRegistration : Registration arena.{u}
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
      (Realization signature.{u}) Unit Unit where
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
    exact p.μ[p.f | p.𝔽 p.n]) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.ReverseCrossings
    definition := none
    coordinates := #[0,1,2,3,7,9,10,14]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg",
        "arg", "body", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning.ReverseCrossings
