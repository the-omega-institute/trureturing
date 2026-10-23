import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.ExactTaylorObservationRemainder
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift

open LeanInformationAudit MeasureTheory Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Linear.ExactTaylorObservationRemainder
open Reg.Support.RealScalarLift
open scoped BigOperators
noncomputable section
universe u v w
namespace Reg.D5.S3.Observer.Linear.ExactTaylorObservationRemainder

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

namespace Tail

def actual : Realization signature :=
  realize signature (fun _ _ t => Real.exp t) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def theoremLaw (R : Realization signature) : Prop := ∀ {𝕜 : Type u} {A : Type v}
    [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    [CompleteSpace A] [NormOneClass A]
    (z : A) (r : ℝ) (n : ℕ) (_hr : 0 ≤ r) (_hz : ‖z‖ ≤ r),
    ‖NormedSpace.exp z - ∑ k ∈ range n, ((k.factorial : 𝕜)⁻¹) • z ^ k‖ ≤
      r ^ n / (n.factorial : ℝ) * R.readout () () r

def arena : Arena where
  signature := signature
  Law := theoremLaw.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  letI : Algebra (ULift.{u} ℝ) (ULift.{v} ℝ) := ULift.algebra' ℝ (ULift.{v} ℝ)
  letI : NormedAlgebra (ULift.{u} ℝ) (ULift.{v} ℝ) := {
    norm_smul_le := by
      intro r x
      change ‖r.down * x.down‖ ≤ ‖r.down‖ * ‖x.down‖
      exact (norm_mul _ _).le }
  have hh := h (𝕜 := ULift.{u} ℝ) (A := ULift.{v} ℝ)
    0 1 0 zero_le_one (by simp)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  exact ne_of_lt (Real.exp_lt_exp.mpr zero_lt_one)

def family : Registration arena (type_of% @exp_tail_le.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exp_tail_le, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exp_tail_le.{u,v})
    (type_of% (realize signature (fun _ _ t => Real.exp t) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.ExactTaylorObservationRemainder.exp_tail_le.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ExactTaylorObservationRemainder.Tail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Real.exp t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ExactTaylorObservationRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Tail

namespace Pointwise

def actual : Realization signature :=
  realize signature (fun _ _ t => Real.exp t) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def theoremLaw (R : Realization signature) : Prop := ∀ {𝕜 : Type u} {V : Type v} {W : Type w}
    [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (B : V →L[𝕜] V) (C : V →L[𝕜] W) (N : ℕ) (t : ℝ) (_ht : 0 ≤ t) (x : V),
    ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x‖ ≤
      ‖C‖ * R.readout () () (max 1 ‖B‖ * t) * (max 1 ‖B‖ * t) ^ (N + 1) /
        ((N + 1).factorial : ℝ) * ‖x‖

def arena : Arena where
  signature := signature
  Law := theoremLaw.{u,v,w}

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  have hh := h (𝕜 := ULift.{u} ℝ) (V := ULift.{v} ℝ) (W := ULift.{w} ℝ)
    0 lineMap 0 1 zero_le_one 1
  norm_num [rejected, realize, observationTaylor] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  exact ne_of_lt (Real.exp_lt_exp.mpr zero_lt_one)

def family : Registration arena (type_of% @norm_observation_taylor_remainder.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨norm_observation_taylor_remainder, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@norm_observation_taylor_remainder.{u,v,w})
    (type_of% (realize signature (fun _ _ t => Real.exp t) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.ExactTaylorObservationRemainder.norm_observation_taylor_remainder.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ExactTaylorObservationRemainder.Pointwise.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Real.exp t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ExactTaylorObservationRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Pointwise

namespace Energy

def actual : Realization signature :=
  realize signature (fun _ _ t => t ^ 2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def theoremLaw (R : Realization signature) : Prop := ∀ {𝕜 : Type u} {V : Type v} {W : Type w}
    [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (B : V →L[𝕜] V) (C : V →L[𝕜] W) (N : ℕ) (T : ℝ) (_hT : 0 ≤ T) (x : V),
    (∫ t in (0 : ℝ)..T, R.readout () ()
      ‖C ((NormedSpace.exp ((t : 𝕜) • B)) x) - observationTaylor B C N t x‖) ≤
      (‖C‖ * Real.exp (max 1 ‖B‖ * T) * max 1 ‖B‖ ^ (N + 1) /
        ((N + 1).factorial : ℝ)) ^ 2 *
        (T ^ (2 * N + 3) / (2 * N + 3 : ℕ)) * ‖x‖ ^ 2

def arena : Arena where
  signature := signature
  Law := theoremLaw.{u,v,w}

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  have hh := h (𝕜 := ULift.{u} ℝ) (V := ULift.{v} ℝ) (W := ULift.{w} ℝ)
    0 0 0 1 zero_le_one 0
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @observation_taylor_energy_remainder.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨observation_taylor_energy_remainder, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@observation_taylor_energy_remainder.{u,v,w})
    (type_of% (realize signature (fun _ _ t => t ^ 2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.ExactTaylorObservationRemainder.observation_taylor_energy_remainder.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.ExactTaylorObservationRemainder.Energy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => t ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.ExactTaylorObservationRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Energy
end Reg.D5.S3.Observer.Linear.ExactTaylorObservationRemainder
