import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.DerivativeLayerExactPivot
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift

/-! The scalar Schur coefficient readout in the two exact minimum laws. -/

open LeanInformationAudit MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Linear.DerivativeLayerExactPivot
open Reg.Support.RealScalarLift
open scoped Interval InnerProductSpace
noncomputable section
universe u v

namespace Reg.D5.S3.Observer.Linear.DerivativeLayerExactPivot

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => schurFactor k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, schurFactor, Nat.choose]

namespace Filtered

def theoremLaw (R : Realization signature) : Prop :=
  ∀ {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {X : ℕ → Type v} [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
    (D : ∀ i, X i →ₗ[ℝ] W) (k : ℕ) (v : W)
    (_hv : ∀ i : ℕ, i < k → v ∈ LinearMap.range (D i)),
    IsLeast
      (Set.range (fun a : ∀ i : Fin k, X (i : ℕ) =>
        ∫ s : ℝ in 0..1, ‖s ^ k • v - lowerProfile k (fun i => D (i : ℕ) (a i)) s‖ ^ 2))
      (R.readout () () k * ‖v‖ ^ 2)

def arena : Arena where
  signature := signature
  Law := theoremLaw.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let state : ULift.{u} ℝ := ULift.up 1
  let D : ∀ i : ℕ, ULift.{v} ℝ →ₗ[ℝ] ULift.{u} ℝ := fun _ => 0
  have hrange : ∀ i : ℕ, i < 0 → state ∈ LinearMap.range (D i) := by simp
  have heq := (filtered_polynomial_pivot_isLeast D 0 state hrange).unique
    (h D 0 state hrange)
  have hnorm : ‖state‖ ≠ 0 := norm_ne_zero_iff.mpr (by
    intro hz
    have := congrArg ULift.down hz
    simp [state] at this)
  apply hnorm
  simpa [schurFactor, rejected, realize] using heq

def family : Registration arena (type_of% @filtered_polynomial_pivot_isLeast.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨filtered_polynomial_pivot_isLeast, rejected, rejected_law⟩
  sensitivity := by
    exact ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl,
      rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@filtered_polynomial_pivot_isLeast.{u,v})
    (type_of% (realize signature (fun _ _ k => schurFactor k) (fun e => nomatch e))) Unit Unit := {
  unitName :=
    `D5.S3.Observer.Linear.DerivativeLayerExactPivot.filtered_polynomial_pivot_isLeast.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.DerivativeLayerExactPivot.Filtered.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => schurFactor k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.DerivativeLayerExactPivot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Filtered

namespace Derivative

def theoremLaw (R : Realization signature) : Prop :=
  ∀ {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V) (C : V →ₗ[ℝ] W) (k : ℕ) (x : derivativeLayer B C k),
    IsLeast
      (Set.range (fun a : ∀ i : Fin k, derivativeLayer B C (i : ℕ) =>
        ∫ s : ℝ in 0..1, ‖s ^ k • derivativeLayerOutput B C k x -
          lowerProfile k (fun i => derivativeLayerOutput B C (i : ℕ) (a i)) s‖ ^ 2))
      (R.readout () () k * ‖derivativeLayerOutput B C k x‖ ^ 2)

def arena : Arena where
  signature := signature
  Law := theoremLaw.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let e : ULift.{v} ℝ ≃ₗ[ℝ] ULift.{u} ℝ :=
    ULift.moduleEquiv.trans ULift.moduleEquiv.symm
  let B : ULift.{v} ℝ →ₗ[ℝ] ULift.{v} ℝ := 0
  have hone : derivativeKernel B e.toLinearMap 1 = ⊥ := by
    apply le_antisymm _ bot_le
    intro y hy
    have hz := (Submodule.mem_iInf _).mp hy (0 : Fin 1)
    have hz' : e y = 0 := by
      simpa [LinearMap.mem_ker] using hz
    exact (Submodule.mem_bot ℝ).mpr (e.injective (by simpa only [map_zero] using hz'))
  let state : derivativeLayer B e.toLinearMap 0 :=
    ⟨ULift.up 1, by
      rw [derivativeLayer, show 0 + 1 = 1 by rfl, hone, Submodule.bot_orthogonal_eq_top]
      simp [derivativeKernel]⟩
  have hstate : (state : ULift.{v} ℝ) ≠ 0 := by
    intro hz
    have := congrArg ULift.down hz
    simp [state] at this
  have houtput : derivativeLayerOutput B e.toLinearMap 0 state ≠ 0 := by
    simpa [derivativeLayerOutput] using
      (show e (state : ULift.{v} ℝ) ≠ 0 from fun hz =>
        hstate (e.injective (by simpa only [map_zero] using hz)))
  have heq := (derivative_layer_pivot_isLeast B e.toLinearMap 0 state).unique
    (h B e.toLinearMap 0 state)
  have hnorm := norm_ne_zero_iff.mpr houtput
  apply hnorm
  simpa [schurFactor, rejected, realize] using heq

def family : Registration arena (type_of% @derivative_layer_pivot_isLeast.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨derivative_layer_pivot_isLeast, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@derivative_layer_pivot_isLeast.{u,v})
    (type_of% (realize signature (fun _ _ k => schurFactor k) (fun e => nomatch e))) Unit Unit := {
  unitName :=
    `D5.S3.Observer.Linear.DerivativeLayerExactPivot.derivative_layer_pivot_isLeast.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.DerivativeLayerExactPivot.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => schurFactor k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.DerivativeLayerExactPivot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Derivative

end Reg.D5.S3.Observer.Linear.DerivativeLayerExactPivot
