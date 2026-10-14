/- GID: D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/QutritComplementaryEntropyFrontier
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Qutrit complementary map entropies have a sharp lower frontier. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier

open scoped BigOperators ComplexOrder Matrix Kronecker
open D5.S3.Quantum.Information.PartialTraceMutualInformation

-- Channel and state definitions.
def admissible
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) : Prop :=
  V.conjTranspose * V = 1

def swap
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  fun p i => V (p.2, p.1) i

def channelB
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (R : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  partialTraceRight (V * R * V.conjTranspose)

def joint
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  V * ((1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) *
    V.conjTranspose

def rhoB
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  partialTraceRight (joint V)

def rhoE
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  partialTraceLeft (joint V)

def choi
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q =>
    (1 / 3 : ℝ) •
      ((channelB V (Matrix.single p.1 q.1 (1 : ℂ))) p.2 q.2)

-- Gram identities, positivity, normalization, and exchange of the factors.
private theorem joint_eq_scaled_gram (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    joint V = (1 / 3 : ℝ) • (V * V.conjTranspose) := by
  rw [joint, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

private theorem joint_posSemidef (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    (joint V).PosSemidef := by
  rw [joint_eq_scaled_gram]
  exact (Matrix.posSemidef_self_mul_conjTranspose V).smul (by norm_num : (0 : ℝ) ≤ 1 / 3)

private theorem rhoB_posSemidef (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    (rhoB V).PosSemidef :=
  partialTraceRight_posSemidef (joint_posSemidef V)

private theorem rhoE_posSemidef (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    (rhoE V).PosSemidef :=
  partialTraceLeft_posSemidef (joint_posSemidef V)

private theorem joint_trace (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (hV : admissible V) : (joint V).trace = 1 := by
  rw [joint_eq_scaled_gram, Matrix.trace_smul, Matrix.trace_mul_comm, hV,
    Matrix.trace_one]
  norm_num [Complex.real_smul]

private theorem joint_upper (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (hV : admissible V) :
    ((1 / 3 : ℝ) • (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) -
      joint V).PosSemidef := by
  have hp : (1 - V * V.conjTranspose) * (1 - V * V.conjTranspose).conjTranspose =
      1 - V * V.conjTranspose := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_sub, sub_mul,
      mul_one, one_mul]
    rw [Matrix.mul_assoc V V.conjTranspose (V * V.conjTranspose),
      ← Matrix.mul_assoc V.conjTranspose V V.conjTranspose, hV]
    simp only [Matrix.one_mul]
    abel
  rw [joint_eq_scaled_gram, ← smul_sub, ← hp]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (by norm_num : (0 : ℝ) ≤ 1 / 3)

private theorem swap_swap (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    swap (swap V) = V := rfl

private theorem swap_admissible (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (hV : admissible V) : admissible (swap V) := by
  change (swap V).conjTranspose * swap V = 1
  rw [← hV]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, swap, Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem channelB_swap (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ)
    (R : Matrix (Fin 3) (Fin 3) ℂ) :
    channelB (swap V) R = partialTraceLeft (V * R * V.conjTranspose) := by
  ext i j
  simp only [channelB, partialTraceLeft, partialTraceRight, Matrix.mul_apply,
    Matrix.conjTranspose_apply, swap]

private theorem rhoB_swap (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    rhoB (swap V) = rhoE V :=
  channelB_swap V ((1 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ))

-- The normalized block Choi matrix and the complementary Gram matrix.
private def reshuffle (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  fun p e => V (p.2, e) p.1

private theorem choi_eq_scaled_gram (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    choi V = (1 / 3 : ℝ) • (reshuffle V * (reshuffle V).conjTranspose) := by
  ext p q
  simp [choi, channelB, partialTraceRight, Matrix.mul_apply, Matrix.single,
    Matrix.conjTranspose_apply, reshuffle, Matrix.smul_apply, Finset.mul_sum, ite_and, eq_comm]

private theorem choi_posSemidef (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) :
    (choi V).PosSemidef := by
  rw [choi_eq_scaled_gram]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (by norm_num : (0 : ℝ) ≤ 1 / 3)

def outputEntropy
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) : ℝ :=
  spectralEntropy (rhoB_posSemidef V).isHermitian

def mapEntropy
    (V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ) : ℝ :=
  spectralEntropy (choi_posSemidef V).isHermitian

def entropy3 (x : Fin 3 → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (x i)

def h (a : ℝ) : ℝ :=
  Real.binEntropy a

def g (a : ℝ) : ℝ :=
  Real.negMulLog (1 / 3 + a) +
  Real.negMulLog (1 / 3) +
  Real.negMulLog (1 / 3 - a)

def attainer (a : ℝ) :
    Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  Matrix.single (0, 0) 0 1 +
  Matrix.single (1, 0) 1 (Real.sqrt (1 - 3 * a) : ℂ) +
  Matrix.single (0, 1) 1 (Real.sqrt (3 * a) : ℂ) +
  Matrix.single (2, 0) 2 1

def claim : Prop :=
  (∀ V : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ,
    admissible V →
    ∀ a : ℝ, a ∈ Set.Icc 0 (1 / 3 : ℝ) →
      (mapEntropy V ≤ h a →
        g a ≤ mapEntropy (swap V)) ∧
      (mapEntropy (swap V) ≤ h a →
        g a ≤ mapEntropy V)) ∧
  (∀ a : ℝ, a ∈ Set.Icc 0 (1 / 3 : ℝ) →
    (admissible (attainer a) ∧
      mapEntropy (attainer a) = h a ∧
      mapEntropy (swap (attainer a)) = g a) ∧
    (admissible (swap (attainer a)) ∧
      mapEntropy (swap (attainer a)) = g a ∧
      mapEntropy (swap (swap (attainer a))) = h a))

end D5.S3.Quantum.Information.QutritComplementaryEntropyFrontier
