/- GID: D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.claim; result=D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.result; claim=D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.claim
   digest: A block Hadamard measurement gives time-dependent two-classical dephasing without MUBs. -/

import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
import D5.S3.Observer.Existence.EmpiricalReflexiveSeparation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation

open scoped BigOperators ComplexOrder Kronecker Matrix
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
open D5.S3.Quantum.PureState.PureStateHandshake

noncomputable section

/-- The dephasing Hamiltonian on system times bath. -/
def hamiltonian {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ :=
  ∑ j, basisProjector j ⊗ₖ Hs j

/-- The time-independent joint propagator. -/
def propagator {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ) (t : ℝ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • hamiltonian Hs)

/-- The rank-one projector onto a column of a unitary measurement matrix. -/
def measurementProjector {d : ℕ} (V : Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  rankOneDensity (fun i => V.val i x)

/-- A sharp measurement acting trivially on the bath. -/
def luders {d m : ℕ} (V : Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d)
    (X : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ :=
  (measurementProjector V x ⊗ₖ 1) * X * (measurementProjector V x ⊗ₖ 1)

/-- The literal one-time joint-system trace formula. -/
def prob1 {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (σ : Matrix (Fin m) (Fin m) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix.unitaryGroup (Fin d) ℂ) (t₀ : ℝ) (y : Fin d) (t₁ : ℝ) : ℂ :=
  Matrix.trace (luders V y (unitaryEvolution (propagator Hs (t₁ - t₀)) (ρ ⊗ₖ σ)))

/-- The literal two-time joint-system trace formula. -/
def prob2 {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (σ : Matrix (Fin m) (Fin m) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix.unitaryGroup (Fin d) ℂ) (t₀ : ℝ)
    (y : Fin d) (t₂ : ℝ) (x : Fin d) (t₁ : ℝ) : ℂ :=
  Matrix.trace (luders V y (unitaryEvolution (propagator Hs (t₂ - t₁))
    (luders V x (unitaryEvolution (propagator Hs (t₁ - t₀)) (ρ ⊗ₖ σ)))))

/-- All consistency conditions through two measurements, including normalization. -/
def twoClassical {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (σ : Matrix (Fin m) (Fin m) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix.unitaryGroup (Fin d) ℂ) (t₀ : ℝ) : Prop :=
  ∀ t₁ t₂ : ℝ, t₀ ≤ t₁ → t₁ ≤ t₂ →
    (∑ x, prob1 Hs σ ρ V t₀ x t₁) = 1 ∧
    (∀ y, (∑ x, prob2 Hs σ ρ V t₀ y t₂ x t₁) = prob1 Hs σ ρ V t₀ y t₂) ∧
    (∀ x, (∑ y, prob2 Hs σ ρ V t₀ y t₂ x t₁) = prob1 Hs σ ρ V t₀ x t₁)

/-- Two ordered time pairs give different statistics for the same outcomes. -/
def timeDependent {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (σ : Matrix (Fin m) (Fin m) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix.unitaryGroup (Fin d) ℂ) (t₀ : ℝ) : Prop :=
  ∃ t₁ t₂ t₁' t₂' : ℝ, t₀ ≤ t₁ ∧ t₁ ≤ t₂ ∧ t₀ ≤ t₁' ∧ t₁' ≤ t₂' ∧
    ∃ x y, prob2 Hs σ ρ V t₀ y t₂ x t₁ ≠ prob2 Hs σ ρ V t₀ y t₂' x t₁'

/-- The measurement and dephasing PVMs fail to commute. -/
def notFullyCompatible {d : ℕ} (V : Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  ∃ x j, measurementProjector V x * basisProjector j ≠
    basisProjector j * measurementProjector V x

/-- Necessity of an unbiased measurement for genuinely time-dependent two-classical dephasing. -/
def claim : Prop :=
  ∀ (d m : ℕ) (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (σ : Matrix (Fin m) (Fin m) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix.unitaryGroup (Fin d) ℂ) (t₀ : ℝ),
    (∀ j, (Hs j).IsHermitian) → σ.PosSemidef → Matrix.trace σ = 1 →
    ρ.PosSemidef → Matrix.trace ρ = 1 →
    (∀ i j, i ≠ j → ρ i j = 0) → ρ ≠ (1 / (d : ℂ)) • 1 →
    notFullyCompatible V → twoClassical Hs σ ρ V t₀ → timeDependent Hs σ ρ V t₀ →
    ∀ j x, Complex.normSq (V.val j x) = 1 / (d : ℝ)

private def bathZ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1]
private def blocks : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![0, bathZ, 2 • bathZ]
private def bathState : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • 1
private def systemState : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1/2, 1/3, 1/6]
private def amplitude : ℂ := (Real.sqrt 2 : ℂ) / 2
private def measurementRaw : Matrix (Fin 3) (Fin 3) ℂ :=
  !![amplitude, amplitude, 0; amplitude, -amplitude, 0; 0, 0, 1]

private theorem measurement_unitary : measurementRaw ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  sorry

private def measurement : Matrix.unitaryGroup (Fin 3) ℂ :=
  ⟨measurementRaw, measurement_unitary⟩

private theorem states_valid :
    bathState.PosSemidef ∧ Matrix.trace bathState = 1 ∧
    systemState.PosSemidef ∧ Matrix.trace systemState = 1 ∧
    (∀ i j, i ≠ j → systemState i j = 0) ∧ systemState ≠ (1 / (3 : ℂ)) • 1 := by
  sorry

private theorem blocks_hermitian : ∀ j, (blocks j).IsHermitian := by
  sorry

private def energies (k : Fin 3 × Fin 2) : ℂ := (k.1 : ℂ) * ![1, -1] k.2

private theorem hamiltonian_diagonal : hamiltonian blocks = Matrix.diagonal energies := by
  sorry

private theorem propagator_diagonal (t : ℝ) :
    propagator blocks t = Matrix.diagonal (fun k => Complex.exp (-(t : ℂ) * Complex.I * energies k)) := by
  sorry

private theorem initial_stationary (t : ℝ) :
    unitaryEvolution (propagator blocks t) (systemState ⊗ₖ bathState) =
      systemState ⊗ₖ bathState := by
  sorry

private theorem one_time (t : ℝ) (y : Fin 3) :
    prob1 blocks bathState systemState measurement 0 y t = ![(5/12 : ℂ), 5/12, 1/6] y := by
  sorry

private def jointLaw (u : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let a := 5 * (2 + Complex.exp (Complex.I * (u : ℂ)) +
    Complex.exp (-(Complex.I * (u : ℂ)))) / 48
  let b := 5 * (2 - Complex.exp (Complex.I * (u : ℂ)) -
    Complex.exp (-(Complex.I * (u : ℂ)))) / 48
  !![a, b, 0; b, a, 0; 0, 0, 1/6]

private theorem two_time (t₁ t₂ : ℝ) (x y : Fin 3) :
    prob2 blocks bathState systemState measurement 0 y t₂ x t₁ = jointLaw (t₂ - t₁) y x := by
  sorry

private theorem consistency : twoClassical blocks bathState systemState measurement 0 := by
  sorry

private theorem dependence : timeDependent blocks bathState systemState measurement 0 := by
  sorry

private theorem incompatible : notFullyCompatible measurement := by
  sorry

private theorem biased : Complex.normSq (measurement.val 2 0) ≠ 1 / (3 : ℝ) := by
  sorry

/-- The block measurement refutes the proposed necessity of mutual unbiasedness. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨hσ, htσ, hρ, htρ, hd, hn⟩ := states_valid
  exact biased (h 3 2 blocks bathState systemState measurement 0 blocks_hermitian
    hσ htσ hρ htρ hd hn incompatible consistency dependence 2 0)

end
end D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation
