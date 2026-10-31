/- GID: D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.claim; result=D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.result; claim=D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.claim
   digest: A three-qubit state refutes the Shannon branch-and-bound entropy lower bound. -/

import D5.S3.Entropy.MaxEntropy
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The full-support stabilizer standard form in Section V.C of Tarabunga et al.,
arXiv:2411.05766v1, specialized to k = N and R = I. The conjecture following (69)
asserts the Shannon inequality below. Entropy is measured in nats. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation

open D5.S3.Entropy.MaxEntropy (shannonEntropy)

/-- Computational basis strings, with one binary coordinate for each qubit. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The quadratic exponent is evaluated in the binary field. -/
def quadForm {n : ℕ} (q : Fin n → Fin n → ZMod 2) (x : Bits n) : ZMod 2 :=
  ∑ i, ∑ j, x i * q i j * x j

/-- The off-diagonal part of the source's upper-triangular matrix. -/
def IsStrictUpper {n : ℕ} (q : Fin n → Fin n → ZMod 2) : Prop :=
  ∀ i j, ¬ i < j → q i j = 0

/-- The diagonal binary matrix with diagonal d. -/
def diagMatrix {n : ℕ} (d : Bits n) : Fin n → Fin n → ZMod 2 :=
  fun i j => if i = j then d i else 0

/-- The source stabilizer amplitude. The exponent cᵀx of i is the integer sum
of products of the representatives 0 and 1, rather than a binary-field sum. -/
def stabAmp {n : ℕ} (q : Fin n → Fin n → ZMod 2) (c : Bits n) (x : Bits n) : ℂ :=
  ((Real.sqrt (2 ^ n))⁻¹ : ℂ) * (-1) ^ (quadForm q x).val *
    Complex.I ^ (∑ i, (c i).val * (x i).val)

/-- The source distribution p at k = N, R = I, indexed by diagonal matrices. -/
def overlapProb {n : ℕ} (q : Fin n → Fin n → ZMod 2) (c : Bits n)
    (ψ : Bits n → ℂ) (d : Bits n) : ℝ :=
  Complex.normSq (∑ x, star (stabAmp (diagMatrix d + q) c x) * ψ x)

/-- The source distribution q at R = I, after taking absolute amplitudes. -/
def absProb {n : ℕ} (ψ : Bits n → ℂ) (d : Bits n) : ℝ :=
  Complex.normSq (∑ x, star (stabAmp (diagMatrix d) 0 x) * (‖ψ x‖ : ℂ))

/-- The Shannon branch-and-bound lower-bound conjecture, restricted to k = N, R = I. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ψ : Bits n → ℂ, (∑ x, Complex.normSq (ψ x)) = 1 →
    ∀ (q : Fin n → Fin n → ZMod 2) (c : Bits n), IsStrictUpper q →
      shannonEntropy (absProb ψ) ≤ shannonEntropy (overlapProb q c ψ)

/-- Coordinate 0 is most significant: the values in order 000,…,111 are
(1,0,2,-1,1,0,0,1). -/
private def coeff (x : Bits 3) : ℝ :=
  if x 0 = 0 then
    if x 1 = 0 then (if x 2 = 0 then 1 else 0) else (if x 2 = 0 then 2 else -1)
  else
    if x 1 = 0 then (if x 2 = 0 then 1 else 0) else (if x 2 = 0 then 0 else 1)

private def witness (x : Bits 3) : ℂ := (coeff x : ℂ) / (Real.sqrt 8 : ℂ)

private lemma witness_unit : (∑ x, Complex.normSq (witness x)) = 1 := by
  sorry

private lemma overlap_distribution (d : Bits 3) :
    overlapProb 0 0 witness d =
      if d 0 = 0 then (if d 1 = 0 then 1 / 4 else 0)
      else (if d 2 = 0 then 0 else 1 / 4) := by
  sorry

private lemma abs_distribution (d : Bits 3) :
    absProb witness d =
      if d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 0 then 9 / 16 else 1 / 16 := by
  sorry

private lemma overlap_entropy :
    shannonEntropy (overlapProb 0 0 witness) = 2 * Real.log 2 := by
  sorry

private lemma abs_entropy :
    shannonEntropy (absProb witness) = 4 * Real.log 2 - (9 / 8) * Real.log 3 := by
  sorry

private lemma log_gap : 9 * Real.log 3 < 16 * Real.log 2 := by
  sorry

/-- The certified three-qubit counterexample to the source's Shannon conjecture. -/
theorem result : ¬ claim := by
  intro h
  have hb := h 3 (by decide) witness witness_unit 0 0 (by
    intro i j hij
    rfl)
  rw [abs_entropy, overlap_entropy] at hb
  linarith [log_gap]

end D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation
