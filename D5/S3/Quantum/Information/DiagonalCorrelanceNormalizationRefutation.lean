/- GID: D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation; result=D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.result; claim=D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.claim
   digest: Seven-qubit diagonal correlance exceeds Hedemann's normalization bound. -/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
open scoped BigOperators

@[expose] public section

namespace D5.S3.Quantum.Information.DiagonalCorrelanceNormalizationRefutation

def IsProbability {n : ℕ} (p : (Fin n → Bool) → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

def marginal {n : ℕ} (p : (Fin n → Bool) → ℝ) (i : Fin n) (b : Bool) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => x i = b), p x

def reductionProduct {n : ℕ} (p : (Fin n → Bool) → ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  Matrix.diagonal (fun x => ∏ i, marginal p i (x i))

def correlanceRaw {n : ℕ} (p : (Fin n → Bool) → ℝ) : ℝ :=
  ((Matrix.diagonal p - reductionProduct p) ^ 2).trace

def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p : (Fin n → Bool) → ℝ, IsProbability p →
    correlanceRaw p ≤ 1 / 2 - 1 / 2 ^ n

private def witness (x : Fin 7 → Bool) : ℝ :=
  if x = fun _ => false then 3 / 5 else if x = fun _ => true then 2 / 5 else 0

private lemma witness_probability : IsProbability witness := by sorry

private lemma witness_raw : correlanceRaw witness = 3023545392 / 6103515625 := by sorry

theorem result : ¬ claim := by
  intro h
  have hb := h 7 (by norm_num) witness witness_probability
  rw [witness_raw] at hb
  norm_num at hb

end D5.S3.Quantum.Information.DiagonalCorrelanceNormalizationRefutation
