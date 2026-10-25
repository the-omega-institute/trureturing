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

/-! Noisy qubit projective tests admit parents while their channel has no joint extension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

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
  have heq : depol = pauliChannel ![31 / 40, 3 / 40, 3 / 40, 3 / 40] := by
    ext X i j
    fin_cases i <;> fin_cases j <;>
      norm_num [depol, pauliChannel, sigma,
        D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
        D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_succ] <;>
      ring_nf <;> norm_num [Complex.I_sq] <;> ring
  rw [heq]
  exact channel_cptp _ (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])

private theorem depol_dual : depol.dual = depol := by
  apply LinearMap.ext
  intro A
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  calc
    (depol.dual A * X).trace = (A * depol X).trace := by
      rw [Matrix.trace_mul_comm, ← MatrixMap.Dual.trace_eq, Matrix.trace_mul_comm]
    _ = (depol A * X).trace := by
      simp only [depol, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.trace_add,
        Matrix.trace_smul]
      ring

private def effect (U : unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ := rankOneDensity (fun k => (U : Matrix (Fin 2) (Fin 2) ℂ) k i)

private def centered (U : unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ := (2 : ℂ) • effect U i - 1

private theorem effect_facts (U : unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    (effect U i).IsHermitian ∧ (effect U i).trace = 1 ∧
      effect U i * effect U i = effect U i ∧ effect U 0 + effect U 1 = 1 := by
  have hn : star (fun k => (U : Matrix (Fin 2) (Fin 2) ℂ) k i) ⬝ᵥ
      (fun k => (U : Matrix (Fin 2) (Fin 2) ℂ) k i) = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i i)
      (Matrix.UnitaryGroup.star_mul_self U)
    simpa [Matrix.star_eq_conjTranspose, Matrix.mul_apply, dotProduct] using h
  refine ⟨(Matrix.posSemidef_vecMulVec_self_star _).isHermitian, ?_,
    (pure_state_handshake _ hn 1).1, ?_⟩
  · change (rankOneDensity _).trace = 1
    simpa only [rankOneDensity, Matrix.trace_vecMulVec, dotProduct, Pi.star_apply,
      mul_comm] using hn
  · have h := Unitary.coe_mul_star_self U
    change (U : Matrix (Fin 2) (Fin 2) ℂ) *
      (U : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = 1 at h
    rw [← h]
    ext a b
    simp [effect, rankOneDensity, Matrix.vecMulVec_apply, Matrix.mul_apply, Fin.sum_univ_two]

private theorem centered_facts (U : unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    (centered U i).IsHermitian ∧ (centered U i).trace = 0 ∧
      centered U i * centered U i = 1 ∧ centered U 0 + centered U 1 = 0 := by
  obtain ⟨hh, ht, hs, hc⟩ := effect_facts U i
  refine ⟨(hh.smul (by norm_num)).sub Matrix.isHermitian_one, ?_, ?_, ?_⟩
  · simp only [centered, Matrix.trace_sub, Matrix.trace_smul, ht, Matrix.trace_one,
      Fintype.card_fin]
    norm_num
  · unfold centered
    calc
      _ = (4 : ℂ) • (effect U i * effect U i) - (4 : ℂ) • effect U i + 1 := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_one, Matrix.one_mul]
        module
      _ = 1 := by rw [hs]; module
  · unfold centered
    linear_combination (norm := module) (2 : ℂ) • hc

private theorem traceless_anticommutator (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.trace = 0) (hB : B.trace = 0) :
    A * B + B * A = (A * B).trace • 1 := by
  have ha : A 1 1 = -A 0 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, eq_neg_iff_add_eq_zero, add_comm] using hA
  have hb : B 1 1 = -B 0 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, eq_neg_iff_add_eq_zero, add_comm] using hB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two, ha, hb] <;> ring

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
  exact ((MatrixMap.choi_PSD_iff_CP_map Λ).mp hΛ.1).smul
    (show (0 : ℂ) ≤ 1 / 2 by norm_num [Complex.le_def])

private theorem jointChoi_trace (Λ : MatrixMap (Fin 2) (Fin 2 × Fin 2) ℂ)
    (hΛ : IsCPTP Λ) : (jointChoi Λ).trace = 1 := by
  unfold jointChoi
  rw [Matrix.trace_smul]
  change (1 / 2 : ℂ) * (∑ p : (Fin 2 × Fin 2) × Fin 2,
    Λ (Matrix.single p.2 p.2 1) p.1 p.1) = 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  change (1 / 2 : ℂ) * (∑ i : Fin 2, (Λ (Matrix.single i i 1)).trace) = 1
  simp_rw [hΛ.2]
  norm_num [Matrix.trace, Matrix.single, Fin.sum_univ_two]

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
