/- GID: D5/S3/Quantum/Information/FisherDiscord/Result
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FisherDiscord/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/FisherDiscord/Defs.claim; result=D5/S3/Quantum/Information/FisherDiscord/Result.result; claim=D5/S3/Quantum/Information/FisherDiscord/Defs.claim
   digest: The flagged two-qubit state refutes partial-trace monotonicity of Fisher discord. -/

import D5.S3.Quantum.Information.FisherDiscord.Extension
import Mathlib.Tactic

noncomputable section
open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Information.FisherDiscord.Result
open D5.S3.Quantum.Information.FisherDiscord.Defs
open D5.S3.Quantum.Information.FisherDiscord.Spectral
open D5.S3.Quantum.Information.FisherDiscord.Extension

def weights : Fin 2 → ℝ := fun i => if i = 0 then 1 / 5 else 4 / 5

def qubitX : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then 1 else 0

def qubitSLD : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 0 ∧ j = 1 then -(6 / 5 : ℂ) * Complex.I else
  if i = 1 ∧ j = 0 then (6 / 5 : ℂ) * Complex.I else 0

def flagSLD : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun x y =>
  if x = (0, 0) ∧ y = (1, 0) then 2 * Complex.I else
  if x = (1, 0) ∧ y = (0, 0) then -(2 * Complex.I) else
  if x = (0, 1) ∧ y = (1, 1) then -(2 * Complex.I) else
  if x = (1, 1) ∧ y = (0, 1) then 2 * Complex.I else 0

private theorem weights_nonneg : ∀ i, 0 ≤ weights i := by
  intro i
  fin_cases i <;> delta weights <;> norm_num

private theorem weights_sum : ∑ i, weights i = 1 := by
  delta weights
  norm_num [Fin.sum_univ_two]

private theorem qubitX_hermitian : qubitX.IsHermitian := by
  ext i j
  change star (qubitX j i) = qubitX i j
  fin_cases i <;> fin_cases j <;> delta qubitX <;>
    simp [Matrix.IsHermitian, Matrix.conjTranspose_apply]

private theorem qubit_sld : IsSLD (diagonal (fun i => (weights i : ℂ))) qubitX qubitSLD := by
  constructor
  · ext i j
    change star (qubitSLD j i) = qubitSLD i j
    fin_cases i <;> fin_cases j <;>
      delta qubitSLD <;>
      norm_num [Matrix.IsHermitian, Matrix.conjTranspose_apply,
        Matrix.of_apply]
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.add_apply,
      Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      delta weights qubitX qubitSLD <;>
      norm_num [Matrix.diagonal, Matrix.diagonal_apply_eq,
        Matrix.diagonal_apply_ne, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
      apply Complex.ext <;> norm_num

private theorem flag_sld :
    IsSLD (flagExtension weights) (liftLeft (d₂ := 2) qubitX) flagSLD := by
  constructor
  · ext ⟨i, b⟩ ⟨j, c⟩
    change star (flagSLD (j, c) (i, b)) = flagSLD (i, b) (j, c)
    fin_cases i <;> fin_cases b <;> fin_cases j <;> fin_cases c <;>
      delta flagSLD <;>
      norm_num [Matrix.IsHermitian, Matrix.conjTranspose_apply, Matrix.of_apply]
  · ext ⟨i, b⟩ ⟨j, c⟩
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.add_apply,
      Matrix.mul_apply]
    delta liftLeft
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases b <;> fin_cases j <;> fin_cases c <;>
      delta weights qubitX flagSLD <;>
      norm_num [flagExtension,
        Matrix.kroneckerMap_apply, Matrix.diagonal, Matrix.diagonal_apply_eq,
        Matrix.diagonal_apply_ne, Matrix.of_apply, Matrix.mul_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two] <;>
      apply Complex.ext <;> norm_num

private theorem base_discord (L : Matrix (Fin 2) (Fin 2) ℂ)
    (hL : IsSLD (diagonal (fun i => (weights i : ℂ))) qubitX L) :
    fisherSLD (diagonal (fun i => (weights i : ℂ))) L -
      skewWY (diagonal (fun i => (weights i : ℂ))) qubitX = 4 / 25 := by
  rw [discord_diag weights weights_nonneg qubitX L qubitX_hermitian hL]
  delta weights qubitX pairKernel
  norm_num [Fin.sum_univ_two]
  field_simp
  ring_nf
  have hs : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := by norm_num
  nlinarith

/-- The universal partial-trace monotonicity claim is false. -/
theorem result : ¬ claim := by
  intro hclaim
  have hall : ∀ d₂, extensionIneq weights qubitX qubitSLD d₂ := by
    intro d₂ σ Lσ hσ hMarg hLσ
    have hLbase : IsSLD (partialTrace₂ σ) qubitX qubitSLD := by
      simpa [hMarg] using qubit_sld
    simpa [hMarg] using
      (hclaim 2 d₂ σ qubitX Lσ qubitSLD hσ qubitX_hermitian hLσ hLbase)
  have hzero := monotone_discord_zero weights weights_nonneg weights_sum
    qubitX qubitSLD qubitX_hermitian qubit_sld ⟨flagSLD, flag_sld⟩ hall
  rw [base_discord qubitSLD qubit_sld] at hzero
  norm_num at hzero

end D5.S3.Quantum.Information.FisherDiscord.Result
