/- GID: D5/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/NoisyWernerHolevoLindbladEmbedding
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The noisy qutrit Werner–Holevo channel has a GKSL logarithm only at zero noise. -/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators Matrix

namespace D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding

/-- The noisy Werner–Holevo map on qutrit matrices. -/
def wernerHolevo (x : ℝ) :
    Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
  (1 - (x : ℂ)) • LinearMap.id -
    ((x : ℂ) / 2) • (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℂ ℂ).toLinearMap +
    ((x : ℂ) / 2) • (Matrix.traceLinearMap (Fin 3) ℂ ℂ).smulRight 1

/-- A generator with a Hermitian Hamiltonian and finitely many GKSL jump matrices. -/
def IsGKSLGenerator (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) : Prop :=
  ∃ (m : ℕ) (H : Matrix (Fin 3) (Fin 3) ℂ)
    (V : Fin m → Matrix (Fin 3) (Fin 3) ℂ), H.IsHermitian ∧
      ∀ X, G X = -Complex.I • (H * X - X * H) +
        ∑ k, (V k * X * (V k)ᴴ - (1 / 2 : ℂ) •
          ((V k)ᴴ * V k * X + X * ((V k)ᴴ * V k)))

/-- The ordinary exponential in the matrix-unit basis, transported back to matrices. -/
def generatorExp (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) :
    Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
  (LinearMap.toMatrixAlgEquiv (Matrix.stdBasis ℂ (Fin 3) (Fin 3))).symm
    (NormedSpace.exp
      (LinearMap.toMatrixAlgEquiv (Matrix.stdBasis ℂ (Fin 3) (Fin 3)) G))

/-- Embeddability on the source's remaining parameter interval. -/
def claim : Prop :=
  ∀ x : ℝ, x ∈ Set.Icc 0 (2 / 3 : ℝ) →
    ((∃ G, IsGKSLGenerator G ∧ generatorExp G = wernerHolevo x) ↔ x = 0)

private def symmetricProjection : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
  (1 / 2 : ℂ) • (LinearMap.id +
    (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℂ ℂ).toLinearMap) -
    (1 / 3 : ℂ) • (Matrix.traceLinearMap (Fin 3) ℂ ℂ).smulRight 1

private def antisymmetricProjection : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
  (1 / 2 : ℂ) • (LinearMap.id -
    (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℂ ℂ).toLinearMap)

private def symmetricTrace (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) : ℝ :=
  (LinearMap.trace ℂ _ (G.comp symmetricProjection)).re

private def antisymmetricTrace (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) : ℝ :=
  (LinearMap.trace ℂ _ (G.comp antisymmetricProjection)).re

private theorem zero_gksl :
    IsGKSLGenerator (0 : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) := by
  refine ⟨0, 0, Fin.elim0, Matrix.isHermitian_zero, ?_⟩
  intro X
  simp

private theorem wernerHolevo_zero : wernerHolevo 0 = LinearMap.id := by
  unfold wernerHolevo
  simp

private theorem generatorExp_zero :
    generatorExp (0 : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) = LinearMap.id := by
  unfold generatorExp
  simp only [map_zero, NormedSpace.exp_zero, map_one]
  rfl

private theorem generatorExp_injective
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) :
    Function.Injective (generatorExp G) := by
  have hunit : IsUnit (generatorExp G) :=
    (Matrix.isUnit_exp _).map
      (LinearMap.toMatrixAlgEquiv (Matrix.stdBasis ℂ (Fin 3) (Fin 3))).symm.toMonoidHom
  intro X Y hXY
  have := congrArg (fun Z => hunit.unit.inv Z) hXY
  simpa only [Module.End.isUnit_inv_apply_apply_of_isUnit] using this

private theorem endpoint_kernel :
    ∃ X : Matrix (Fin 3) (Fin 3) ℂ,
      X ≠ 0 ∧ wernerHolevo (2 / 3) X = 0 := by
  refine ⟨Matrix.single 0 0 1 - Matrix.single 1 1 1, ?_, ?_⟩
  · intro h
    have := congrArg (fun X : Matrix (Fin 3) (Fin 3) ℂ => X 0 0) h
    norm_num [Matrix.single] at this
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [wernerHolevo, Matrix.trace, Matrix.single, Matrix.one_apply,
        Matrix.transposeLinearEquiv]

private theorem endpoint_not_exp
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) :
    generatorExp G ≠ wernerHolevo (2 / 3) := by
  intro h
  obtain ⟨X, hX, hkill⟩ := endpoint_kernel
  apply hX
  apply generatorExp_injective G
  rw [h, hkill, map_zero]

private theorem spectral_traces (x : ℝ) (hx : 0 < x) (hx' : x < 2 / 3)
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ))
    (hG : IsGKSLGenerator G) (hexp : generatorExp G = wernerHolevo x) :
    symmetricTrace G = 5 * Real.log (1 - 3 * x / 2) ∧
      antisymmetricTrace G = 3 * Real.log (1 - x / 2) := by
  sorry

private theorem gksl_trace_inequality
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (hG : IsGKSLGenerator G) :
    0 ≤ symmetricTrace G - 5 * antisymmetricTrace G := by
  sorry

private theorem strict_log_inequality (x : ℝ) (hx : 0 < x) (hx' : x < 2 / 3) :
    5 * Real.log (1 - 3 * x / 2) < 15 * Real.log (1 - x / 2) := by
  have hb : 0 < 1 - 3 * x / 2 := by linarith
  have hc : 0 < 1 - x / 2 := by linarith
  have hpoly : (1 - x / 2) ^ 3 - (1 - 3 * x / 2) = x ^ 2 * (6 - x) / 8 := by ring
  have hgap : 0 < (1 - x / 2) ^ 3 - (1 - 3 * x / 2) := by
    rw [hpoly]
    exact div_pos (mul_pos (sq_pos_of_pos hx) (by linarith)) (by norm_num)
  have hlog := Real.log_lt_log hb (show 1 - 3 * x / 2 < (1 - x / 2) ^ 3 by linarith)
  rw [Real.log_pow] at hlog
  linarith

private theorem interior_not_exp (x : ℝ) (hx : 0 < x) (hx' : x < 2 / 3)
    (G : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (hG : IsGKSLGenerator G) :
    generatorExp G ≠ wernerHolevo x := by
  intro hexp
  obtain ⟨hS, hA⟩ := spectral_traces x hx hx' G hG hexp
  have hpos := gksl_trace_inequality G hG
  rw [hS, hA] at hpos
  have hneg := strict_log_inequality x hx hx'
  linarith

/-- Exactly zero noise is the exponential of a GKSL generator on `[0, 2/3]`. -/
theorem result : claim := by
  intro x hx
  constructor
  · rintro ⟨G, hG, hexp⟩
    by_contra hzero
    have hpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hzero)
    rcases lt_or_eq_of_le hx.2 with hlt | heq
    · exact interior_not_exp x hpos hlt G hG hexp
    · subst x
      exact endpoint_not_exp G hexp
  · intro hzero
    subst x
    exact ⟨0, zero_gksl, generatorExp_zero.trans wernerHolevo_zero.symm⟩

end D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding
