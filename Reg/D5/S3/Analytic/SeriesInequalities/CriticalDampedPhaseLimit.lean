import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit
open _root_.D5.S3.Analytic.SeriesInequalities.FiniteSourceCriticalTail
open _root_.D5.S3.Analytic.SeriesInequalities.FiniteSourceClosure
open LeanInformationAudit Filter Topology
open scoped ENNReal

noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => WeightedArray ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (A ρ : ℝ) (_hA : 0 < A) (_hρ : 0 < ρ) (_hρ1 : ρ < 1)
    (_hcrit : A * ρ = (1 - ρ) ^ 2) (ζ : ℂ) (_hζ : ‖ζ‖ = 1)
    (τ θ : ℕ → ℝ) (κ : ℝ) (_hτ : ∀ j, 0 < τ j)
    (_hτlim : Tendsto τ atTop (𝓝 0))
    (_hratio : Tendsto (fun j => θ j / τ j) atTop (𝓝 κ)),
    ∃ (U : WeightedArray ℂ) (V : ℕ → WeightedArray ℂ),
      (∀ n k, U (n, k) = (ρ ^ (n + k)) •
        extension (fun i => -(A : ℂ) * ζ ^ (i + 1)) n k) ∧
      (∀ j n k, V j (n, k) = (ρ ^ (n + k)) •
        extension (fun i => Complex.exp ((-τ j : ℝ) + (θ j : ℂ) * Complex.I) ^ (i + 1) *
          (-(A : ℂ) * ζ ^ (i + 1))) n k) ∧
      (∀ j, R.readout () () (U - V j) =
        phaseReadout (A / (1 + ρ)) (A / (1 + ρ) * ρ) ρ (τ j) (θ j)) ∧
      Tendsto θ atTop (𝓝 0) ∧
      Tendsto (fun j => ‖U - V j‖) atTop (𝓝 (A / (1 + ρ) * envelope κ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let τ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hτ : ∀ j, 0 < τ j := by intro j; dsimp [τ]; positivity
  have hτlim : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : Tendsto (fun j => (0 : ℝ) / τ j) atTop (𝓝 0) := by
    simpa only [zero_div] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  obtain ⟨U, V, _, _, hbad, _⟩ := h (1/2) (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 1 (by simp) τ (fun _ => 0) 0 hτ hτlim hratio
  obtain ⟨U', V', _, _, hgood, _⟩ := critical_damped_phase_limit
    (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    1 (by simp) τ (fun _ => 0) 0 hτ hτlim hratio
  have hbad0 := hbad 0
  change -1 = phaseReadout _ _ _ _ _ at hbad0
  have hgood0 := hgood 0
  have hp := norm_nonneg (U' - V' 0)
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, lp.single (E := fun _ : ℕ × ℕ => ℂ) ∞ (0, 0) 1, ?_⟩
  change ‖(0 : WeightedArray ℂ)‖ ≠ ‖lp.single (E := fun _ : ℕ × ℕ => ℂ) ∞ (0, 0) 1‖
  rw [norm_zero, lp.norm_single (by simp), norm_one]
  norm_num

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨critical_damped_phase_limit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit.critical_damped_phase_limit)
    (type_of% (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit.norm_information_unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
#print axioms registration_1

namespace GradedAudit
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Sigma fun _ : ℕ → ℂ => Sigma fun _ : ℂ => ℕ) (fun _ => ℕ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ p k =>
    extension p.1 p.2.2 k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (a : ℕ → ℂ) (z : ℂ) (n k : ℕ),
    extension (fun i => z ^ (i + 1) * a i) n k =
      z ^ (n + k + 1) * R.readout () ⟨a, ⟨z, n⟩⟩ k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => 1) 1 0 0
  norm_num [rejected, realize, extension] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨⟨(fun _ => 1), ⟨1, 0⟩⟩, 0, 1,
    by simp [actual, realize, extension]⟩
def family : Registration arena (type_of% (@extension_graded)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨extension_graded, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@extension_graded) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit.GradedAudit.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit.GradedAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k =>
    extension p.1 p.2.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end GradedAudit

namespace AmplitudeAudit
open _root_.D5.S3.Analytic.SeriesInequalities.NegativeBoundaryEnvelope
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℕ → ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ A => amplitude A) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ n => -(n : ℝ)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (A : ℝ) (_hA : 0 ≤ A) (_hpos : ∀ k, 0 ≤ amplitude A k),
    Monotone (R.readout () () A)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz (k : ℕ) : amplitude 0 k = 0 := by
    induction k with
    | zero => simp [amplitude]
    | succ k ih => simp [amplitude, ih]
  have hh := h 0 le_rfl (fun k => by rw [hz]) (show (0 : ℕ) ≤ 1 by omega)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize, amplitude] at hh
def family : Registration arena (type_of% (@amplitude_mono)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨amplitude_mono, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@amplitude_mono) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit.AmplitudeAudit.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit.AmplitudeAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => amplitude A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AmplitudeAudit

namespace PhaseNormAudit
def arena : Arena where
  signature := CriticalDampedPhaseLimit.signature
  Law R := ∀ (A ρ : ℝ) (_hA : 0 < A) (_hρ : 0 < ρ) (_hρ1 : ρ < 1)
    (_hcrit : A * ρ = (1 - ρ) ^ 2) (ζ w : ℂ) (_hζ : ‖ζ‖ = 1)
    (U V : WeightedArray ℂ)
    (_hU : ∀ n k, U (n, k) = (ρ ^ (n + k)) •
      extension (fun i => -(A : ℂ) * ζ ^ (i + 1)) n k)
    (_hV : ∀ n k, V (n, k) = (ρ ^ (n + k)) •
      extension (fun i => w ^ (i + 1) * (-(A : ℂ) * ζ ^ (i + 1))) n k),
    R.readout () () (U - V) = sSup (Set.range fun k : ℕ =>
      (A / (1 + ρ) + (A / (1 + ρ) * ρ) * ρ ^ (2 * k)) * ‖1 - w ^ (k + 1)‖)
private theorem rejected_law : ¬ arena.Law CriticalDampedPhaseLimit.rejected := by
  intro h
  obtain ⟨U, _, hU⟩ := (critical_recursive_image_closure (K := ℂ) (1/2) (1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
    (fun _ => -((1/2 : ℝ) : ℂ)) (fun _ => by norm_num)
  have hU' : ∀ n k, U (n, k) = ((1/2 : ℝ) ^ (n + k)) •
      extension (fun i => -((1/2 : ℝ) : ℂ) * (1 : ℂ) ^ (i + 1)) n k := by simpa using hU
  have hV' : ∀ n k, U (n, k) = ((1/2 : ℝ) ^ (n + k)) •
      extension (fun i => (1 : ℂ) ^ (i + 1) * (-((1/2 : ℝ) : ℂ) * (1 : ℂ) ^ (i + 1))) n k := by
    simpa using hU
  have hh := h (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 1 1 (by simp) U U hU' hV'
  norm_num [CriticalDampedPhaseLimit.rejected, realize] at hh
def family : Registration arena (type_of% (@phase_array_norm)) where
  actual := CriticalDampedPhaseLimit.actual
  bridge := Iff.rfl
  variation := ⟨phase_array_norm, CriticalDampedPhaseLimit.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law
    CriticalDampedPhaseLimit.actual CriticalDampedPhaseLimit.rejected rejected_law
  dependence := actual_dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@phase_array_norm) (Realization CriticalDampedPhaseLimit.signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit.PhaseNormAudit.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit.PhaseNormAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize CriticalDampedPhaseLimit.signature (fun _ _ x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PhaseNormAudit
end Reg.D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit
