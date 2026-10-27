/- GID: D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.claim; result=D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.result; claim=D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation.claim
   digest: The Harrow channel pair has parallel Chernoff exponent at least two. -/

import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Topology.Instances.EReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.QuantumChannels.HarrowParallelChernoffExponentRefutation

open Matrix Filter
open scoped BigOperators Topology
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap (kron kron_def)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation (diagonal_norm)

/-- Example 5, with the input factors ordered as A, C. -/
def harrowM : MatrixMap (Fin 2 × Fin 2) (Fin 2) ℂ where
  toFun x := fun c d =>
    if c = d then
      (if c = 0 then x (0, 0) (0, 0) + x (1, 0) (1, 0) + x (0, 1) (0, 1) else 0) +
        x (1, 1) (1, 1) / 2
    else 0
  map_add' := by sorry
  map_smul' := by sorry

/-- The second channel of Example 5, including the off-diagonal A entries. -/
def harrowMbar : MatrixMap (Fin 2 × Fin 2) (Fin 2) ℂ where
  toFun x := fun c d =>
    (x (0, 0) (0, 0) + x (1, 0) (1, 0)) / 2 +
    (if c = 1 ∧ d = 1 then
      (x (0, 1) (0, 1) + x (0, 1) (1, 1) + x (1, 1) (0, 1) + x (1, 1) (1, 1)) / 2
    else 0) +
    (if c = d then
      (x (0, 1) (0, 1) - x (0, 1) (1, 1) - x (1, 1) (0, 1) + x (1, 1) (1, 1)) / 4
    else 0)
  map_add' := by sorry
  map_smul' := by sorry

/-- The tensor power specified on all matrix units, including n = 0. -/
def tensorPow {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (φ : MatrixMap ι κ ℂ) (n : ℕ) : MatrixMap (Fin n → ι) (Fin n → κ) ℂ where
  toFun x := fun c d => ∑ a, ∑ b, x a b * ∏ k, φ (single (a k) (b k) 1) (c k) (d k)
  map_add' := by sorry
  map_smul' := by sorry

/-- Stabilization by an input-sized reference, optimized over every density matrix. -/
def diamondNorm {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (φ : MatrixMap ι κ ℂ) : ℝ≥0∞ :=
  sSup {r | ∃ ρ : Matrix (ι × ι) (ι × ι) ℂ,
    ρ.PosSemidef ∧ ρ.trace = 1 ∧
      r = ENNReal.ofReal (traceNorm (kron φ (LinearMap.id : MatrixMap ι ι ℂ) ρ))}

/-- The source's equal-prior parallel discrimination error, in nonnegative extended reals. -/
def parallelError (n : ℕ) : ℝ≥0∞ :=
  (1 - diamondNorm (tensorPow harrowM n - tensorPow harrowMbar n) / 2) / 2

/-- Base-two error exponent; zero error has exponent +infinity at every positive n. -/
def exponent (n : ℕ) : EReal :=
  (((n : ℝ) * Real.log 2)⁻¹ : ℝ) * (-ENNReal.log (parallelError n))

/-- Salek--Hayashi--Winter's conjecture for the channels in Example 5. -/
def claim : Prop := Tendsto exponent atTop (𝓝 (1 : EReal))

private def input (n : ℕ) : Fin n → Fin 2 × Fin 2 := fun _ => (0, 1)

private def reference (n : ℕ) : Fin n → Fin 2 × Fin 2 := fun _ => (0, 0)

private def weight (n : ℕ) (c : Fin n → Fin 2) : ℝ :=
  ∏ k, if c k = 0 then (1 / 4 : ℝ) else 3 / 4

private def difference (n : ℕ) (c : (Fin n → Fin 2) × (Fin n → Fin 2 × Fin 2)) : ℝ :=
  if c.2 = reference n then (if c.1 = fun _ => 0 then 1 else 0) - weight n c.1 else 0

private theorem channel_values :
    harrowM (single (0, 1) (0, 1) 1) = diagonal (fun c => if c = 0 then 1 else 0) ∧
    harrowMbar (single (0, 1) (0, 1) 1) =
      diagonal (fun c => if c = 0 then 1 / 4 else 3 / 4) := by sorry

private theorem tensor_values (n : ℕ) :
    (tensorPow harrowM n - tensorPow harrowMbar n) (single (input n) (input n) 1) =
      diagonal (fun c => (((if c = fun _ => 0 then 1 else 0) - weight n c : ℝ) : ℂ)) := by
  sorry

private theorem input_density (n : ℕ) :
    (single (input n, reference n) (input n, reference n) (1 : ℂ)).PosSemidef ∧
    (single (input n, reference n) (input n, reference n) (1 : ℂ)).trace = 1 := by sorry

private theorem amplified_output (n : ℕ) :
    kron (tensorPow harrowM n - tensorPow harrowMbar n) LinearMap.id
      (single (input n, reference n) (input n, reference n) 1) =
      diagonal (fun c => (difference n c : ℂ)) := by sorry

private theorem weight_mass (n : ℕ) :
    (∑ c, weight n c) = 1 ∧ weight n (fun _ => 0) = (1 / 4 : ℝ) ^ n ∧
      (∀ c, 0 ≤ weight n c) ∧ (∀ c, weight n c ≤ 1) := by sorry

private theorem witness_norm (n : ℕ) :
    traceNorm (diagonal (fun c => (difference n c : ℂ))) =
      2 * (1 - (1 / 4 : ℝ) ^ n) := by sorry

private theorem diamond_lower (n : ℕ) :
    ENNReal.ofReal (2 * (1 - (1 / 4 : ℝ) ^ n)) ≤
      diamondNorm (tensorPow harrowM n - tensorPow harrowMbar n) := by sorry

private theorem error_upper (n : ℕ) : parallelError n ≤ (1 / 4 : ℝ≥0∞) ^ n / 2 := by
  sorry

private theorem exponent_lower (n : ℕ) (hn : 1 ≤ n) : (2 : EReal) ≤ exponent n := by
  sorry

private theorem not_tendsto (h : ∀ n : ℕ, 1 ≤ n → (2 : EReal) ≤ exponent n) : ¬ claim := by
  sorry

 theorem result : ¬ claim := not_tendsto exponent_lower

end D5.S3.Quantum.QuantumChannels.HarrowParallelChernoffExponentRefutation
