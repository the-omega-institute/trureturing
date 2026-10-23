import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.PositiveWindowObservationBound
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift

open LeanInformationAudit MeasureTheory Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Linear.PositiveWindowObservationBound
open _root_.D5.S3.Observer.Linear.HilbertMomentCoercivity
open Reg.Support.RealScalarLift
open scoped BigOperators
noncomputable section
universe u v w
namespace Reg.D5.S3.Observer.Linear.PositiveWindowObservationBound

abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ N t => t ^ (2 * N + 1)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def theoremLaw (R : Realization signature) : Prop :=
  ∀ {𝕜 : Type u} {V : Type v} {W : Type w} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V] [Nontrivial V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    (B : V →L[𝕜] V) (C : V →L[𝕜] W) (N : ℕ) (μ : ℝ)
    (_hμ : 0 < μ) (_hfloor : μ ≤ derivativeFloor B C N) (T : ℝ) (_hT : 0 < T),
    0 < remainderScale B C N ∧ 0 < windowCutoff B C N μ ∧
    windowCoefficient N μ * R.readout () N (min T (windowCutoff B C N μ)) ≤
      observationFloor B C T ∧
    0 < windowCoefficient N μ * min T (windowCutoff B C N μ) ^ (2 * N + 1)

def arena : Arena where
  signature := signature
  Law := theoremLaw.{u,v,w}

private theorem line_derivative_floor :
    1 ≤ derivativeFloor (0 : ULift.{v} ℝ →L[ULift.{u} ℝ] ULift.{v} ℝ)
      lineMap.{u,v,w} 0 := by
  apply le_csInf
  · obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty_rclike (ULift.{u} ℝ)
      (E := ULift.{v} ℝ) (r := 1) (by norm_num)
    exact ⟨_, x, by simpa using hx, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    change ‖y‖ = 1 at hy
    simp [Fin.sum_univ_succ, hy]

private theorem line_observation_floor (T : ℝ) :
    observationFloor (0 : ULift.{v} ℝ →L[ULift.{u} ℝ] ULift.{v} ℝ)
      lineMap.{u,v,w} T = T := by
  have he (x : ULift.{v} ℝ) (hx : ‖x‖ = 1) :
      trajectoryEnergy (0 : ULift.{v} ℝ →L[ULift.{u} ℝ] ULift.{v} ℝ)
        lineMap.{u,v,w} T x = T := by
    simp [trajectoryEnergy, hx]
  have hs : (trajectoryEnergy
      (0 : ULift.{v} ℝ →L[ULift.{u} ℝ] ULift.{v} ℝ) lineMap.{u,v,w} T ''
      {x : ULift.{v} ℝ | ‖x‖ = 1}) = {T} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact he x hx
    · intro hz
      obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty_rclike (ULift.{u} ℝ)
        (E := ULift.{v} ℝ) (r := 1) (by norm_num)
      refine ⟨x, by simpa using hx, ?_⟩
      exact (he x (by simpa using hx)).trans hz.symm
  unfold observationFloor
  rw [hs, csInf_singleton]

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  have hlam : 0 < hilbertEigenvalue 0 :=
    (hilbert_polynomial_coercivity 0 (fun _ : Fin 1 => (0 : ℝ))).1
  have ha : 0 < windowCoefficient 0 1 := by
    unfold windowCoefficient
    positivity
  have hh := h (𝕜 := ULift.{u} ℝ) (V := ULift.{v} ℝ) (W := ULift.{w} ℝ)
    0 lineMap 0 1 zero_lt_one line_derivative_floor (windowCoefficient 0 1 / 2)
    (by positivity)
  have hlo := hh.2.2.1
  change windowCoefficient 0 1 * 1 ≤ _ at hlo
  rw [line_observation_floor] at hlo
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @positive_window_observation_bound.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive_window_observation_bound, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@positive_window_observation_bound.{u,v,w})
    (type_of% (realize signature (fun _ N t => t ^ (2 * N + 1)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.PositiveWindowObservationBound.positive_window_observation_bound.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.PositiveWindowObservationBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N t => t ^ (2 * N + 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.PositiveWindowObservationBound
    definition := none
    coordinates := #[12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Observer.Linear.PositiveWindowObservationBound
