import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift

open LeanInformationAudit MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery
open _root_.D5.S3.Observer.Linear.PositiveWindowObservationBound
open Reg.Support.RealScalarLift
open scoped InnerProductSpace ENNReal NNReal
noncomputable section
universe u v w
namespace Reg.D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ δ a => ENNReal.ofReal (δ / Real.sqrt a)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ δ a => ENNReal.ofReal (2 * δ / Real.sqrt a)) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨1, 1, 4, ?_⟩
  change ENNReal.ofReal (1 / Real.sqrt 1) ≠ ENNReal.ofReal (1 / Real.sqrt 4)
  have hs : Real.sqrt 4 = 2 := by norm_num
  rw [Real.sqrt_one, hs]
  have hh : ENNReal.ofReal (1 / 2 : ℝ) < ENNReal.ofReal (1 / 1 : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  exact ne_of_gt hh

private theorem line_modulus :
    squaredLowerModulus lineMap.{u,v,w} = 1 := by
  have hs : ((fun x : ULift.{v} ℝ => ‖lineMap.{u,v,w} x‖ ^ 2) ''
      {x : ULift.{v} ℝ | ‖x‖ = 1}) = {1} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ‖x‖ = 1 at hx
      simp [hx]
    · intro hz
      obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty_rclike (ULift.{u} ℝ)
        (E := ULift.{v} ℝ) (r := 1) (by norm_num)
      refine ⟨x, by simpa using hx, ?_⟩
      have hxn : ‖x‖ = 1 := by simpa using hx
      simpa [hxn] using hz.symm
  unfold squaredLowerModulus
  rw [hs, csInf_singleton]

private theorem line_observation_floor :
    observationFloor (0 : ULift.{v} ℝ →L[ULift.{u} ℝ] ULift.{v} ℝ)
      lineMap.{u,v,w} 1 = 1 := by
  have he (x : ULift.{v} ℝ) (hx : ‖x‖ = 1) :
      trajectoryEnergy (0 : ULift.{v} ℝ →L[ULift.{u} ℝ] ULift.{v} ℝ)
        lineMap.{u,v,w} 1 x = 1 := by
    simp [trajectoryEnergy, hx]
  have hs : (trajectoryEnergy
      (0 : ULift.{v} ℝ →L[ULift.{u} ℝ] ULift.{v} ℝ) lineMap.{u,v,w} 1 ''
      {x : ULift.{v} ℝ | ‖x‖ = 1}) = {1} := by
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

namespace Hilbert

def theoremLaw (S : Realization signature) : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} {F : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [Nontrivial E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
  ∀ (A : E →L[𝕜] F)
    (_ha : 0 < squaredLowerModulus A),
    ∃ R : F →L[𝕜] E,
      (∀ x, R (A x) = x) ∧
      (∀ y x, inner 𝕜 (A x) (y - A (R y)) = 0) ∧
      (∀ y, ‖R y‖ ≤ ‖y‖ / Real.sqrt (squaredLowerModulus A)) ∧
      ∀ δ : ℝ, 0 ≤ δ →
        reconstructionRisk A δ R = ENNReal.ofReal (δ / Real.sqrt (squaredLowerModulus A)) ∧
        (⨅ Q : F → E, reconstructionRisk A δ Q) =
          S.readout () δ (squaredLowerModulus A)

def arena : Arena where
  signature := signature
  Law := theoremLaw.{u,v,w}

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  have ha : 0 < squaredLowerModulus lineMap.{u,v,w} := by rw [line_modulus]; norm_num
  obtain ⟨R, _, _, _, hr⟩ := h (𝕜 := ULift.{u} ℝ) (E := ULift.{v} ℝ)
    (F := ULift.{w} ℝ) lineMap ha
  obtain ⟨hR, hmin⟩ := hr 1 zero_le_one
  have hle := iInf_le (fun Q : ULift.{w} ℝ → ULift.{v} ℝ =>
    reconstructionRisk lineMap 1 Q) (R : ULift.{w} ℝ → ULift.{v} ℝ)
  rw [hmin, hR] at hle
  norm_num [rejected, realize, line_modulus] at hle

def family : Registration arena (type_of% @sharp_hilbert_noise_recovery.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_hilbert_noise_recovery, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sharp_hilbert_noise_recovery.{u,v,w})
    (type_of% (realize signature (fun _ δ a => ENNReal.ofReal (δ / Real.sqrt a))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery.sharp_hilbert_noise_recovery.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery.Hilbert.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ δ a => ENNReal.ofReal (δ / Real.sqrt a))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery
    definition := none
    coordinates := #[14]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "arg", "arg", "arg",
        "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Hilbert

namespace Trajectory

abbrev signatureT : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signatureT :=
  realize signatureT (fun _ _ radius => ENNReal.ofReal radius) (fun e => nomatch e)
def rejected : Realization signatureT :=
  realize signatureT (fun _ _ radius => ENNReal.ofReal (2 * radius)) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signatureT actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def theoremLaw (S : Realization signatureT) : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} {F : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [Nontrivial E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
  ∀ (B : E →L[𝕜] E) (C : E →L[𝕜] F)
    (T : ℝ) (_hT : 0 < T) (_ha : 0 < observationFloor B C T),
    ∃ A : E →L[𝕜] Lp F 2 (volume.restrict (Ioc 0 T)),
    ∃ R : Lp F 2 (volume.restrict (Ioc 0 T)) →L[𝕜] E,
      (∀ x, (fun t => A x t) =ᵐ[volume.restrict (Ioc 0 T)]
        fun t => C ((NormedSpace.exp ((t : 𝕜) • B)) x)) ∧
      (∀ x, ‖A x‖ ^ 2 = trajectoryEnergy B C T x) ∧
      squaredLowerModulus A = observationFloor B C T ∧
      (∀ x, R (A x) = x) ∧
      (∀ y x, inner 𝕜 (A x) (y - A (R y)) = 0) ∧
      (∀ y, ‖R y‖ ≤ ‖y‖ / Real.sqrt (observationFloor B C T)) ∧
      ∀ δ : ℝ, 0 ≤ δ →
        reconstructionRisk A δ R = ENNReal.ofReal (δ / Real.sqrt (observationFloor B C T)) ∧
        (⨅ Q : Lp F 2 (volume.restrict (Ioc 0 T)) → E, reconstructionRisk A δ Q) =
          S.readout () () (δ / Real.sqrt (observationFloor B C T))

def arena : Arena where
  signature := signatureT
  Law := theoremLaw.{u,v,w}

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  have ha : 0 < observationFloor
      (0 : ULift.{v} ℝ →L[ULift.{u} ℝ] ULift.{v} ℝ) lineMap.{u,v,w} 1 := by
    rw [line_observation_floor]; norm_num
  obtain ⟨A, R, _, _, _, _, _, _, hr⟩ := h (𝕜 := ULift.{u} ℝ) (E := ULift.{v} ℝ)
    (F := ULift.{w} ℝ) 0 lineMap 1 zero_lt_one ha
  obtain ⟨hR, hmin⟩ := hr 1 zero_le_one
  have hle := iInf_le (fun Q : Lp (ULift.{w} ℝ) 2 (volume.restrict (Ioc (0 : ℝ) 1)) →
    ULift.{v} ℝ => reconstructionRisk A 1 Q)
    (R : Lp (ULift.{w} ℝ) 2 (volume.restrict (Ioc (0 : ℝ) 1)) → ULift.{v} ℝ)
  rw [hmin, hR] at hle
  norm_num [rejected, realize, line_observation_floor] at hle

def family : Registration arena (type_of% @sharp_trajectory_noise_recovery.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_trajectory_noise_recovery, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sharp_trajectory_noise_recovery.{u,v,w})
    (type_of% (realize signatureT (fun _ _ radius => ENNReal.ofReal radius)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery.sharp_trajectory_noise_recovery.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery.Trajectory.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signatureT (fun _ _ radius => ENNReal.ofReal radius)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body",
        "arg", "body", "arg", "arg", "arg", "arg",
        "arg", "arg", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Trajectory

end Reg.D5.S3.Observer.Linear.SharpTrajectoryNoiseRecovery
