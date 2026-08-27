/- GID: D5/S3/Quantum/Dynamics/AnalyticFlowGeneration
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/AnalyticFlowGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite-dimensional Hamiltonian flow spans its nested commutator closure. -/

/- Library-search audit trail (2026-08-27):
   * Exact family hit `hamiltonianPropagator` constructs the source matrix exponential flow and
     is imported rather than redeclared.
   * Pinned Mathlib hits `LinearMap.mulLeft`, `LinearMap.mulRight`,
     `hasDerivAt_exp_smul_const`, `HasDerivAt.tendsto_slope_zero`, and
     `ODE_solution_unique_univ` are applied directly.
   * Repository and pinned-Mathlib searches found no theorem identifying the full real-time
     conjugation-orbit span with the nested commutator-power span. -/

import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.ODE.ExistUnique

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Dynamics.AnalyticFlowGeneration

open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

private theorem flow_span_eq_power_orbit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V]
    (K : Module.End ℂ V) (flow : ℝ → V → V)
    (flow_zero : ∀ x, flow 0 x = x)
    (flow_deriv : ∀ x t,
      HasDerivAt (fun s : ℝ => flow s x) (Complex.I • K (flow t x)) t)
    (W : Submodule ℂ V) :
    Submodule.span ℂ {x | ∃ (t : ℝ) (w : V), w ∈ W ∧ x = flow t w} =
      ⨆ n : ℕ, W.map (K ^ n) := by
  let orbit : Set V := {x | ∃ (t : ℝ) (w : V), w ∈ W ∧ x = flow t w}
  let U : Submodule ℂ V := Submodule.span ℂ orbit
  let C : Submodule ℂ V := ⨆ n : ℕ, W.map (K ^ n)
  change U = C
  have hW_U : W ≤ U := by
    intro w hw
    apply Submodule.subset_span
    exact ⟨0, w, hw, (flow_zero w).symm⟩
  have hOrbit_U : ∀ t w, w ∈ W → flow t w ∈ U := by
    intro t w hw
    apply Submodule.subset_span
    exact ⟨t, w, hw, rfl⟩
  have hU_closed : IsClosed (U : Set V) := U.closed_of_finiteDimensional
  have hK_orbit : ∀ t w, w ∈ W → K (flow t w) ∈ U := by
    intro t w hw
    have hDerivative : Complex.I • K (flow t w) ∈ U := by
      apply hU_closed.mem_of_tendsto (flow_deriv w t).tendsto_slope_zero
      filter_upwards with s
      rw [← IsScalarTower.algebraMap_smul ℂ s⁻¹]
      exact U.smul_mem ((algebraMap ℝ ℂ) s⁻¹)
        (U.sub_mem (hOrbit_U (t + s) w hw) (hOrbit_U t w hw))
    have hScaled := U.smul_mem (-Complex.I) hDerivative
    simpa [smul_smul] using hScaled
  have hU_invariant : ∀ x ∈ U, K x ∈ U := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => K x ∈ U) ?_ ?_ ?_ ?_ hx
    · intro x hxOrbit
      rcases hxOrbit with ⟨t, w, hw, rfl⟩
      exact hK_orbit t w hw
    · simpa only [map_zero] using U.zero_mem
    · intro x y _ _ hxK hyK
      simpa using U.add_mem hxK hyK
    · intro a x _ hxK
      simpa using U.smul_mem a hxK
  have hC_le_U : C ≤ U := by
    change (⨆ n : ℕ, W.map (K ^ n)) ≤ U
    refine iSup_le fun n => ?_
    rintro _ ⟨w, hw, rfl⟩
    induction n with
    | zero => simpa [Module.End.one_eq_id] using hW_U hw
    | succ n ih =>
        simpa [pow_succ'] using hU_invariant ((K ^ n) w) ih
  have hW_C : W ≤ C := by
    intro w hw
    exact Submodule.mem_iSup_of_mem 0 <| by
      simpa [Module.End.one_eq_id] using
        (show w ∈ W.map (K ^ 0) from ⟨w, hw, rfl⟩)
  have hC_invariant : ∀ x ∈ C, K x ∈ C := by
    have hMap : C.map K ≤ C := by
      change (⨆ n : ℕ, W.map (K ^ n)).map K ≤
        ⨆ n : ℕ, W.map (K ^ n)
      rw [Submodule.map_iSup]
      refine iSup_le fun n => ?_
      calc
        (W.map (K ^ n)).map K = W.map (K ^ (n + 1)) := by
          rw [← Submodule.map_comp]
          congr 1
          ext x
          simp [pow_succ']
        _ ≤ ⨆ m : ℕ, W.map (K ^ m) :=
          le_iSup (fun m : ℕ => W.map (K ^ m)) (n + 1)
    intro x hx
    exact hMap ⟨x, hx, rfl⟩
  have hOrbit_C : ∀ t w, w ∈ W → flow t w ∈ C := by
    intro t w hw
    let KCL : V →L[ℂ] V := LinearMap.toContinuousLinearMap K
    let generator : V →L[ℂ] V := Complex.I • KCL
    let comparisonFlow : ℝ → V := fun s => exp (s • generator) w
    let ambientGenerator : V →L[ℝ] V :=
      generator.restrictScalars ℝ
    have hComparisonDeriv : ∀ s,
        HasDerivAt comparisonFlow (ambientGenerator (comparisonFlow s)) s := by
      intro s
      have hExp := hasDerivAt_exp_smul_const' generator s
      have hApplied :=
        ((ContinuousLinearMap.apply ℂ V w).restrictScalars ℝ).hasFDerivAt
          |>.comp_hasDerivAt s hExp
      change HasDerivAt (fun u : ℝ => exp (u • generator) w)
        ((generator * exp (s • generator)) w) s at hApplied
      simpa [comparisonFlow, ambientGenerator, generator, KCL, mul_apply] using hApplied
    have hActualDeriv : ∀ s,
        HasDerivAt (fun r : ℝ => flow r w)
          (ambientGenerator (flow s w)) s := by
      intro s
      simpa [ambientGenerator, generator, KCL] using flow_deriv w s
    have hLipschitz : ∀ _s : ℝ,
        LipschitzOnWith ‖ambientGenerator‖₊ (fun x : V => ambientGenerator x)
          (Set.univ : Set V) := by
      intro s
      exact ambientGenerator.lipschitz.lipschitzOnWith
    have hInitial : flow 0 w = comparisonFlow 0 := by
      simp [flow_zero, comparisonFlow]
    have hEqual : (fun s : ℝ => flow s w) = comparisonFlow := by
      apply ODE_solution_unique_univ (K := ‖ambientGenerator‖₊)
        (v := fun _ x => ambientGenerator x) (s := fun _ => Set.univ)
        (t₀ := 0)
      · exact hLipschitz
      · intro s
        exact ⟨hActualDeriv s, Set.mem_univ _⟩
      · intro s
        exact ⟨hComparisonDeriv s, Set.mem_univ _⟩
      · exact hInitial
    have hGeneratorInvariant : ∀ x ∈ C, generator x ∈ C := by
      intro x hx
      simpa [generator, KCL] using C.smul_mem Complex.I (hC_invariant x hx)
    have hComparisonMem : comparisonFlow t ∈ C := by
      have hScaledInvariant : ∀ x ∈ C, (t • generator) x ∈ C := by
        intro x hx
        rw [_root_.smul_apply,
          ← IsScalarTower.algebraMap_smul ℂ t]
        exact C.smul_mem ((algebraMap ℝ ℂ) t) (hGeneratorInvariant x hx)
      have hPower : ∀ m : ℕ, ((t • generator) ^ m) w ∈ C := by
        intro m
        induction m with
        | zero => simpa using hW_C hw
        | succ m ih => simpa [pow_succ'] using hScaledInvariant _ ih
      have hSeries : HasSum
          (fun m : ℕ => ((Nat.factorial m : ℝ)⁻¹) • (t • generator) ^ m)
          (exp (t • generator)) :=
        exp_series_hasSum_exp' (𝕂 := ℝ) (t • generator)
      have hApplied :=
        ((ContinuousLinearMap.apply ℂ V w).restrictScalars ℝ).hasSum hSeries
      change
        ((ContinuousLinearMap.apply ℂ V w).restrictScalars ℝ
          (exp (t • generator))) ∈ C
      rw [← hApplied.tsum_eq]
      apply tsum_mem C.closed_of_finiteDimensional
      intro m
      rw [← IsScalarTower.algebraMap_smul ℂ ((Nat.factorial m : ℝ)⁻¹)]
      exact C.smul_mem ((algebraMap ℝ ℂ) ((Nat.factorial m : ℝ)⁻¹)) (hPower m)
    rw [congrFun hEqual t]
    exact hComparisonMem
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro x ⟨t, w, hw, rfl⟩
    exact hOrbit_C t w hw
  · exact hC_le_U

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance (priority := 2000) : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAddCommGroup

local instance (priority := 2000) : NormedSpace ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedSpace

local instance (priority := 2000) : NormedRing (Matrix n n ℂ) :=
  Matrix.instL2OpNormedRing

local instance (priority := 2000) : NormedAlgebra ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAlgebra

private theorem hasDerivAt_heisenbergFlow (H E : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        hamiltonianPropagator H (-s) * E * hamiltonianPropagator H s)
      (Complex.I •
        (H * (hamiltonianPropagator H (-t) * E * hamiltonianPropagator H t) -
          (hamiltonianPropagator H (-t) * E * hamiltonianPropagator H t) * H)) t := by
  let G := hamiltonianGenerator H
  have hPositive : HasDerivAt (hamiltonianPropagator H)
      (hamiltonianPropagator H t * G) t := by
    exact hasDerivAt_exp_smul_const G t
  have hNegative : HasDerivAt (fun s : ℝ => hamiltonianPropagator H (-s))
      (-(hamiltonianPropagator H (-t) * G)) t := by
    have hExp : HasDerivAt (fun s : ℝ => exp (s • G))
        (exp ((-t) • G) * G) (-t) := hasDerivAt_exp_smul_const G (-t)
    have hNeg : HasDerivAt (fun s : ℝ => -s) (-1) t := hasDerivAt_neg t
    have hComp := hExp.scomp t hNeg
    change HasDerivAt
      (fun s : ℝ => exp ((-s) • G))
      ((-1 : ℝ) • (exp ((-t) • G) * G)) t at hComp
    simpa [hamiltonianPropagator, G] using hComp
  have hRaw := (hNegative.mul_const E).mul hPositive
  apply hRaw.congr_deriv
  have hCommute : H * hamiltonianPropagator H (-t) =
      hamiltonianPropagator H (-t) * H := by
    apply (Commute.exp_right _).eq
    exact ((Commute.refl H).smul_right (-Complex.I)).smul_right (-t)
  calc
    -(hamiltonianPropagator H (-t) * G) * E * hamiltonianPropagator H t +
        hamiltonianPropagator H (-t) * E * (hamiltonianPropagator H t * G) =
      Complex.I •
        ((hamiltonianPropagator H (-t) * H) * E * hamiltonianPropagator H t -
          (hamiltonianPropagator H (-t) * E * hamiltonianPropagator H t) * H) := by
      dsimp [G, hamiltonianGenerator]
      simp only [neg_mul, mul_smul_comm, smul_mul_assoc,
        smul_add, Matrix.mul_assoc, sub_eq_add_neg]
      simp only [neg_smul, smul_neg, neg_neg]
    _ = Complex.I •
        ((H * hamiltonianPropagator H (-t)) * E * hamiltonianPropagator H t -
          (hamiltonianPropagator H (-t) * E * hamiltonianPropagator H t) * H) := by
      rw [hCommute]
    _ = Complex.I •
        (H * (hamiltonianPropagator H (-t) * E * hamiltonianPropagator H t) -
          (hamiltonianPropagator H (-t) * E * hamiltonianPropagator H t) * H) := by
      simp only [Matrix.mul_assoc]

/-- In finite dimension, the complex span of every Hamiltonian conjugate of the initial
observable subspace is exactly the complex span generated by all nested commutators. -/
theorem analytic_flow_generates_commutator_closure
    (H : Matrix n n ℂ) (initial : Submodule ℂ (Matrix n n ℂ)) :
    Submodule.span ℂ
        {A | ∃ (t : ℝ) (E : Matrix n n ℂ), E ∈ initial ∧
          A = hamiltonianPropagator H (-t) * E * hamiltonianPropagator H t} =
      ⨆ k : ℕ,
        initial.map
          ((LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H) ^ k) := by
  let commutator : Module.End ℂ (Matrix n n ℂ) :=
    LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H
  let flow : ℝ → Matrix n n ℂ → Matrix n n ℂ := fun t E =>
    hamiltonianPropagator H (-t) * E * hamiltonianPropagator H t
  change Submodule.span ℂ
      {A | ∃ (t : ℝ) (E : Matrix n n ℂ), E ∈ initial ∧ A = flow t E} =
    ⨆ k : ℕ, initial.map (commutator ^ k)
  apply flow_span_eq_power_orbit commutator flow
  · intro E
    simp [flow, hamiltonianPropagator]
  · intro E t
    simpa [flow, commutator] using hasDerivAt_heisenbergFlow H E t

#print axioms analytic_flow_generates_commutator_closure

end D5.S3.Quantum.Dynamics.AnalyticFlowGeneration
