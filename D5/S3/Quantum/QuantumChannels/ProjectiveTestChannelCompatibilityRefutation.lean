/- GID: D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.claim; result=D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.result; claim=D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.claim
   digest: Projective tests miss self-incompatibility of the qubit depolarizing channel at 7/10. -/

import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.QuantumBounds.CHSHWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.QuantumBounds.CHSHWitness
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness

namespace D5.S3.Quantum.QuantumChannels.ProjectiveTestChannelCompatibilityRefutation

def IsCPTP {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (Φ : MatrixMap A B ℂ) : Prop :=
  Φ.IsCompletelyPositive ∧ ∀ X, (Φ X).trace = X.trace

def POVMCompatible {d : ℕ} (A B : Fin d → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ C : Fin d → Fin d → Matrix (Fin d) (Fin d) ℂ,
    (∀ i j, (C i j).PosSemidef) ∧ (∑ i, ∑ j, C i j) = 1 ∧
      (∀ i, ∑ j, C i j = A i) ∧ (∀ j, ∑ i, C i j = B j)

def basisPOVM {d : ℕ} (Φ : MatrixMap (Fin d) (Fin d) ℂ)
    (U : unitaryGroup (Fin d) ℂ) : Fin d → Matrix (Fin d) (Fin d) ℂ :=
  fun i => Φ.dual (rankOneDensity (fun k => (U : Matrix (Fin d) (Fin d) ℂ) k i))

def ChannelCompatible {d : ℕ} (Φ Ψ : MatrixMap (Fin d) (Fin d) ℂ) : Prop :=
  ∃ Λ : MatrixMap (Fin d) (Fin d × Fin d) ℂ, IsCPTP Λ ∧
    (∀ X, partialTraceRight (Λ X) = Φ X) ∧ (∀ X, partialTraceLeft (Λ X) = Ψ X)

def claim : Prop :=
  ∀ (d : ℕ) (Φ Ψ : MatrixMap (Fin d) (Fin d) ℂ), IsCPTP Φ → IsCPTP Ψ →
    (∀ U V : unitaryGroup (Fin d) ℂ, POVMCompatible (basisPOVM Φ U) (basisPOVM Ψ V)) →
      ChannelCompatible Φ Ψ

private def depol : MatrixMap (Fin 2) (Fin 2) ℂ :=
  (7 / 10 : ℂ) • LinearMap.id +
    (3 / 20 : ℂ) • (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight 1

private theorem depol_cptp : IsCPTP depol := by
  sorry

private theorem depol_dual : depol.dual = depol := by
  sorry

private def effect (U : unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ := rankOneDensity (fun k => (U : Matrix (Fin 2) (Fin 2) ℂ) k i)

private def centered (U : unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ := (2 : ℂ) • effect U i - 1

private theorem effect_facts (U : unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    (effect U i).IsHermitian ∧ (effect U i).trace = 1 ∧
      effect U i * effect U i = effect U i ∧ effect U 0 + effect U 1 = 1 := by
  sorry

private theorem centered_facts (U : unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    (centered U i).IsHermitian ∧ (centered U i).trace = 0 ∧
      centered U i * centered U i = 1 ∧ centered U 0 + centered U 1 = 0 := by
  sorry

private theorem traceless_anticommutator (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.trace = 0) (hB : B.trace = 0) :
    A * B + B * A = (A * B).trace • 1 := by
  sorry

private def parent (U V : unitaryGroup (Fin 2) ℂ) (a b : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 4 : ℂ) • ((1 + (49 / 200 : ℂ) * (centered U a * centered V b).trace) • 1 +
    (7 / 10 : ℂ) • (centered U a + centered V b))

private theorem parent_positive (U V : unitaryGroup (Fin 2) ℂ) (a b : Fin 2) :
    (parent U V a b).PosSemidef := by
  sorry

private theorem parent_marginals (U V : unitaryGroup (Fin 2) ℂ) :
    (∑ a, ∑ b, parent U V a b) = 1 ∧
      (∀ a, ∑ b, parent U V a b = basisPOVM depol U a) ∧
      (∀ b, ∑ a, parent U V a b = basisPOVM depol V b) := by
  sorry

private theorem all_projective_tests (U V : unitaryGroup (Fin 2) ℂ) :
    POVMCompatible (basisPOVM depol U) (basisPOVM depol V) := by
  exact ⟨parent U V, parent_positive U V, parent_marginals U V⟩

private def jointChoi (Λ : MatrixMap (Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  (1 / 2 : ℂ) • Λ.choi_matrix

private def P : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  fun x y => bellDensity (x.1.1, x.2) (y.1.1, y.2) * if x.1.2 = y.1.2 then 1 else 0

private def Q : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  fun x y => bellDensity (x.1.2, x.2) (y.1.2, y.2) * if x.1.1 = y.1.1 then 1 else 0

private theorem jointChoi_positive (Λ : MatrixMap (Fin 2) (Fin 2 × Fin 2) ℂ)
    (hΛ : IsCPTP Λ) : (jointChoi Λ).PosSemidef := by
  sorry

private theorem jointChoi_trace (Λ : MatrixMap (Fin 2) (Fin 2 × Fin 2) ℂ)
    (hΛ : IsCPTP Λ) : (jointChoi Λ).trace = 1 := by
  sorry

private theorem jointChoi_overlaps (Λ : MatrixMap (Fin 2) (Fin 2 × Fin 2) ℂ)
    (hL : ∀ X, partialTraceRight (Λ X) = depol X)
    (hR : ∀ X, partialTraceLeft (Λ X) = depol X) :
    (jointChoi Λ * P).trace = 31 / 40 ∧ (jointChoi Λ * Q).trace = 31 / 40 := by
  sorry

private theorem witness_positive :
    ((3 / 2 : ℂ) • (1 : Matrix ((Fin 2 × Fin 2) × Fin 2)
      ((Fin 2 × Fin 2) × Fin 2) ℂ) - P - Q).PosSemidef := by
  sorry

private theorem no_joint_channel : ¬ ChannelCompatible depol depol := by
  rintro ⟨Λ, hΛ, hL, hR⟩
  have hn := (jointChoi_positive Λ hΛ).trace_mul_nonneg witness_positive
  have ht := jointChoi_trace Λ hΛ
  obtain ⟨hp, hq⟩ := jointChoi_overlaps Λ hL hR
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, ht, hp, hq] at hn
  norm_num [Complex.le_def] at hn

theorem result : ¬ claim := by
  intro h
  exact no_joint_channel (h 2 depol depol depol_cptp depol_cptp all_projective_tests)

end D5.S3.Quantum.QuantumChannels.ProjectiveTestChannelCompatibilityRefutation
