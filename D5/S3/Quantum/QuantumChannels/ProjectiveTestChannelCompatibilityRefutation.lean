/- GID: D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.claim; result=D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.result; claim=D5/S3/Quantum/QuantumChannels/ProjectiveTestChannelCompatibilityRefutation.claim
   digest: Projective tests miss self-incompatibility of the qubit depolarizing channel at 7/10. -/

import D5.S3.QuantumChannels.PurelyNonUnitalEternalNonMarkovianity
import D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation
import D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Divergence.CoherenceL1RelativeEntropyBound
import D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound

/-! Noisy qubit projective tests admit parents while their channel has no joint extension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.QuantumBounds.CHSHWitness
open D5.S3.QuantumChannels.PurelyNonUnitalEternalNonMarkovianity (dep_cptp)
open D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation (IsCPTP)
open D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation (measurementProjector)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (Compatible IsPOVM)
open D5.S3.Divergence.CoherenceL1RelativeEntropyBound (reflection reflection_hermitian reflection_unitary)
open D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound (depolarized)

namespace D5.S3.Quantum.QuantumChannels.ProjectiveTestChannelCompatibilityRefutation

def basisPOVM {d : ℕ} (φ : MatrixMap (Fin d) (Fin d) ℂ)
    (U : unitaryGroup (Fin d) ℂ) : Fin d → Matrix (Fin d) (Fin d) ℂ :=
  fun i => φ.dual (measurementProjector U i)

def ChannelCompatible {d : ℕ} (φ ψ : MatrixMap (Fin d) (Fin d) ℂ) : Prop :=
  ∃ J : MatrixMap (Fin d) (Fin d × Fin d) ℂ, IsCPTP J ∧
    (∀ X, partialTraceRight (J X) = φ X) ∧ (∀ X, partialTraceLeft (J X) = ψ X)

def claim : Prop :=
  ∀ (d : ℕ) (φ ψ : MatrixMap (Fin d) (Fin d) ℂ), IsCPTP φ → IsCPTP ψ →
    (∀ U V : unitaryGroup (Fin d) ℂ, Compatible (basisPOVM φ U) (basisPOVM ψ V)) →
      ChannelCompatible φ ψ

private def depol : MatrixMap (Fin 2) (Fin 2) ℂ :=
  depolarized LinearMap.id (3 / 10)

private theorem depol_dual : depol.dual = depol := by
  apply LinearMap.ext
  intro A
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  calc
    (depol.dual A * X).trace = (A * depol X).trace := by
      rw [Matrix.trace_mul_comm, ← MatrixMap.Dual.trace_eq, Matrix.trace_mul_comm]
    _ = (depol A * X).trace := by
      norm_num [depol, depolarized, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.trace_add,
        Matrix.trace_smul]
      ring

private theorem effect_facts (U : unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    (measurementProjector U i).IsHermitian ∧ (measurementProjector U i).trace = 1 ∧
      measurementProjector U i * measurementProjector U i = measurementProjector U i ∧
      measurementProjector U 0 + measurementProjector U 1 = 1 := by
  have hn : star (fun k => (U : Matrix (Fin 2) (Fin 2) ℂ) k i) ⬝ᵥ
      (fun k => (U : Matrix (Fin 2) (Fin 2) ℂ) k i) = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i i)
      (Matrix.UnitaryGroup.star_mul_self U)
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply] at h
    unfold dotProduct
    simpa using h
  have hp := D5.S3.Observer.Existence.EmpiricalReflexiveSeparation.rankOneDensity_isNormalized _ hn
  refine ⟨hp.1, hp.2.2.1, hp.2.1, ?_⟩
  · have h := Unitary.coe_mul_star_self U
    change (U : Matrix (Fin 2) (Fin 2) ℂ) *
      (U : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = 1 at h
    rw [← h]
    ext a b
    simp [measurementProjector, rankOneDensity, Matrix.vecMulVec_apply, Matrix.mul_apply, Fin.sum_univ_two]

private theorem centered_facts (U : unitaryGroup (Fin 2) ℂ) (i : Fin 2) :
    (reflection (measurementProjector U i)).IsHermitian ∧
      (reflection (measurementProjector U i)).trace = 0 ∧
      reflection (measurementProjector U i) * reflection (measurementProjector U i) = 1 ∧
      reflection (measurementProjector U 0) + reflection (measurementProjector U 1) = 0 := by
  obtain ⟨hh, ht, hs, hc⟩ := effect_facts U i
  refine ⟨reflection_hermitian _ hh, ?_, ?_, ?_⟩
  · rw [reflection.eq_1]
    simp only [Matrix.trace_sub, Matrix.trace_smul, ht, Matrix.trace_one,
      Fintype.card_fin]
    norm_num
  · have hu := (reflection_unitary (measurementProjector U i) hh hs).1
    simpa only [Matrix.star_eq_conjTranspose, (reflection_hermitian _ hh).eq] using hu
  · unfold reflection
    linear_combination (norm := module) (2 : ℂ) • hc

private theorem traceless_anticommutator (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.trace = 0) (hB : B.trace = 0) :
    A * B + B * A = (A * B).trace • 1 := by
  unfold Matrix.trace at hA hB
  have ha : A 1 1 = -A 0 0 := by
    simpa [Fin.sum_univ_two, eq_neg_iff_add_eq_zero, add_comm] using hA
  have hb : B 1 1 = -B 0 0 := by
    simpa [Fin.sum_univ_two, eq_neg_iff_add_eq_zero, add_comm] using hB
  ext i j
  unfold Matrix.trace
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb] <;> ring

private def parent (U V : unitaryGroup (Fin 2) ℂ) (a b : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 4 : ℂ) •
    ((1 + (49 / 200 : ℂ) *
      (reflection (measurementProjector U a) * reflection (measurementProjector V b)).trace) • 1 +
      (7 / 10 : ℂ) •
        (reflection (measurementProjector U a) + reflection (measurementProjector V b)))

private theorem parent_positive (U V : unitaryGroup (Fin 2) ℂ) (a b : Fin 2) :
    (parent U V a b).PosSemidef := by
  let A := reflection (measurementProjector U a)
  let B := reflection (measurementProjector V b)
  let K := A + B
  obtain ⟨hA, htA, hsA, _⟩ := centered_facts U a
  obtain ⟨hB, htB, hsB, _⟩ := centered_facts V b
  have hK : K.IsHermitian := hA.add hB
  have hs : K * K = (2 + (A * B).trace) • 1 := by
    calc
      K * K = A * A + B * B + (A * B + B * A) := by dsimp only [K]; noncomm_ring
      _ = (2 + (A * B).trace) • 1 := by
        rw [hsA, hsB, traceless_anticommutator A B htA htB]
        module
  have hp := Matrix.posSemidef_conjTranspose_mul_self K
  rw [hK.eq, hs] at hp
  have hd : (0 : ℂ) ≤ 2 + (A * B).trace := by
    simpa using hp.diag_nonneg (i := 0)
  let τ : ℝ := (A * B).trace.re
  have hr : (A * B).trace = (τ : ℂ) := by
    apply Complex.ext
    · rfl
    · have := (Complex.nonneg_iff.mp hd).2
      norm_num at this
      simpa using this.symm
  have ht : -2 ≤ τ := by
    have := (Complex.nonneg_iff.mp hd).1
    norm_num at this
    change 0 ≤ 2 + τ at this
    linarith
  rw [hr] at hs
  let α : ℝ := 1 + 49 / 200 * τ
  let c : ℝ := 1 / 50 + 2401 / 40000 * τ ^ 2
  have ha : 0 < α := by dsimp only [α]; linarith
  have hc : 0 < c := by dsimp only [c]; nlinarith [sq_nonneg τ]
  have hce : (c : ℂ) = (α : ℂ) ^ 2 - (49 / 100 : ℂ) * (2 + (τ : ℂ)) := by
    dsimp only [c, α]
    push_cast
    ring
  let H := (α : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (7 / 10 : ℂ) • K
  have hH : H.IsHermitian :=
    (Matrix.isHermitian_one.smul (by unfold IsSelfAdjoint; simp)).add
      (hK.smul (by unfold IsSelfAdjoint; norm_num))
  have he : H.conjTranspose * H + (c : ℂ) • 1 = (2 * (α : ℂ)) • H := by
    rw [hH.eq]
    dsimp only [H]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul, hs]
    rw [hce]
    module
  have han : (α : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hi : H = (1 / (2 * (α : ℂ))) • (H.conjTranspose * H + (c : ℂ) • 1) := by
    rw [he, smul_smul]
    have hz : (1 / (2 * (α : ℂ))) * (2 * (α : ℂ)) = 1 := by field_simp
    rw [hz, one_smul]
  have hcp : (0 : ℂ) ≤ (c : ℂ) := by exact_mod_cast le_of_lt hc
  have hfactor : (0 : ℂ) ≤ 1 / (2 * (α : ℂ)) := by
    rw [show (1 / (2 * (α : ℂ))) = ((1 / (2 * α) : ℝ) : ℂ) by push_cast; rfl]
    exact_mod_cast le_of_lt (div_pos (by norm_num) (mul_pos (by norm_num) ha))
  have hpos : H.PosSemidef := by
    rw [hi]
    exact ((Matrix.posSemidef_conjTranspose_mul_self H).add
      (Matrix.PosSemidef.one.smul hcp)).smul hfactor
  have hae : (α : ℂ) = 1 + (49 / 200 : ℂ) * (τ : ℂ) := by
    dsimp only [α]
    push_cast
    rfl
  unfold parent
  change ((1 / 4 : ℂ) • ((1 + (49 / 200 : ℂ) * (A * B).trace) • 1 +
    (7 / 10 : ℂ) • K)).PosSemidef
  rw [hr, ← hae]
  exact hpos.smul (show (0 : ℂ) ≤ 1 / 4 by norm_num [Complex.le_def])

private theorem parent_marginals (U V : unitaryGroup (Fin 2) ℂ) :
    (∑ a, ∑ b, parent U V a b) = 1 ∧
      (∀ a, ∑ b, parent U V a b = basisPOVM depol U a) ∧
      (∀ b, ∑ a, parent U V a b = basisPOVM depol V b) := by
  have rows (U V : unitaryGroup (Fin 2) ℂ) (a : Fin 2) :
      ∑ b, parent U V a b = basisPOVM depol U a := by
    have hv : reflection (measurementProjector V 1) = -reflection (measurementProjector V 0) := by
      linear_combination (norm := module) (centered_facts V 0).2.2.2
    rw [Fin.sum_univ_two]
    change parent U V a 0 + parent U V a 1 = depol.dual (measurementProjector U a)
    rw [depol_dual]
    unfold parent
    rw [hv]
    simp only [Matrix.mul_neg, Matrix.trace_neg]
    norm_num [depol, depolarized, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, (effect_facts U a).2.1]
    unfold reflection
    module
  have cols (b : Fin 2) : ∑ a, parent U V a b = basisPOVM depol V b := by
    rw [← rows V U b]
    apply Finset.sum_congr rfl
    intro a _
    unfold parent
    rw [Matrix.trace_mul_comm (reflection (measurementProjector U a)),
      add_comm (reflection (measurementProjector U a))]
  refine ⟨?_, rows U V, cols⟩
  simp_rw [rows]
  rw [Fin.sum_univ_two]
  change depol.dual (measurementProjector U 0) + depol.dual (measurementProjector U 1) = 1
  rw [depol_dual, ← map_add, (effect_facts U 0).2.2.2]
  norm_num [depol, depolarized, Matrix.trace_one]
  module

private theorem all_projective_tests (U V : unitaryGroup (Fin 2) ℂ) :
    Compatible (basisPOVM depol U) (basisPOVM depol V) := by
  obtain ⟨hn, hr, hc⟩ := parent_marginals U V
  have hU : IsPOVM (basisPOVM depol U) := by
    constructor
    · intro a
      rw [← hr a]
      exact Matrix.posSemidef_sum _ (fun b _ => parent_positive U V a b)
    · simp_rw [← hr]
      exact hn
  have hV : IsPOVM (basisPOVM depol V) := by
    constructor
    · intro b
      rw [← hc b]
      exact Matrix.posSemidef_sum _ (fun a _ => parent_positive U V a b)
    · simp_rw [← hc]
      rw [Finset.sum_comm]
      exact hn
  refine ⟨hU, hV, (fun p => parent U V p.1 p.2), ⟨?_, ?_⟩, hr, hc⟩
  · rintro ⟨a, b⟩
    exact parent_positive U V a b
  · simpa only [Fintype.sum_prod_type] using hn

private def jointChoi (J : MatrixMap (Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  (1 / 2 : ℂ) • J.choi_matrix

private def P : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  (bellDensity ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix
    (fun x => ((x.1.1, x.2), x.1.2)) (fun x => ((x.1.1, x.2), x.1.2))

private def Q : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  (bellDensity ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)).submatrix
    (fun x => ((x.1.2, x.2), x.1.1)) (fun x => ((x.1.2, x.2), x.1.1))

private theorem jointChoi_positive (J : MatrixMap (Fin 2) (Fin 2 × Fin 2) ℂ)
    (hJ : IsCPTP J) : (jointChoi J).PosSemidef := by
  exact ((MatrixMap.choi_PSD_iff_CP_map J).mp hJ.1).smul
    (show (0 : ℂ) ≤ 1 / 2 by norm_num [Complex.le_def])

private theorem jointChoi_trace (J : MatrixMap (Fin 2) (Fin 2 × Fin 2) ℂ)
    (hJ : IsCPTP J) : (jointChoi J).trace = 1 := by
  rw [jointChoi.eq_1, Matrix.trace_smul]
  change (1 / 2 : ℂ) * (∑ p : (Fin 2 × Fin 2) × Fin 2,
    J (Matrix.single p.2 p.2 1) p.1 p.1) = 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  change (1 / 2 : ℂ) * (∑ i : Fin 2, (J (Matrix.single i i 1)).trace) = 1
  simp_rw [hJ.2]
  unfold Matrix.trace Matrix.single
  norm_num [Fin.sum_univ_two]

private theorem jointChoi_overlaps (J : MatrixMap (Fin 2) (Fin 2 × Fin 2) ℂ)
    (hL : ∀ X, partialTraceRight (J X) = depol X)
    (hR : ∀ X, partialTraceLeft (J X) = depol X) :
    (jointChoi J * P).trace = 31 / 40 ∧ (jointChoi J * Q).trace = 31 / 40 := by
  have hl (i j : Fin 2) : (∑ b : Fin 2,
      J (Matrix.single i j 1) (i, b) (j, b)) = depol (Matrix.single i j 1) i j :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) (hL (Matrix.single i j 1))
  have hr (i j : Fin 2) : (∑ a : Fin 2,
      J (Matrix.single i j 1) (a, i) (a, j)) = depol (Matrix.single i j 1) i j :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) (hR (Matrix.single i j 1))
  have hp : (jointChoi J * P).trace = (1 / 4 : ℂ) *
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ b : Fin 2,
        J (Matrix.single i j 1) (i, b) (j, b) := by
    rw [jointChoi, Matrix.smul_mul, Matrix.trace_smul]
    change (1 / 2 : ℂ) *
      (∑ x : (Fin 2 × Fin 2) × Fin 2, ∑ y : (Fin 2 × Fin 2) × Fin 2,
        J (Matrix.single x.2 y.2 1) x.1 y.1 * P y x) = _
    norm_num [P,
      Fintype.sum_prod_type, Fin.sum_univ_two, bellDensity, bellVector,
      D5.S3.Quantum.QubitWitnesses.bellCoefficients, Matrix.vecMulVec_apply,
      complex_sqrt_two_inv_mul_self]
    ring
  have hq : (jointChoi J * Q).trace = (1 / 4 : ℂ) *
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ a : Fin 2,
        J (Matrix.single i j 1) (a, i) (a, j) := by
    rw [jointChoi, Matrix.smul_mul, Matrix.trace_smul]
    change (1 / 2 : ℂ) *
      (∑ x : (Fin 2 × Fin 2) × Fin 2, ∑ y : (Fin 2 × Fin 2) × Fin 2,
        J (Matrix.single x.2 y.2 1) x.1 y.1 * Q y x) = _
    norm_num [Q,
      Fintype.sum_prod_type, Fin.sum_univ_two, bellDensity, bellVector,
      D5.S3.Quantum.QubitWitnesses.bellCoefficients, Matrix.vecMulVec_apply,
      complex_sqrt_two_inv_mul_self]
    ring
  rw [hp, hq]
  simp_rw [hl, hr]
  norm_num [depol, depolarized, Fin.sum_univ_two]

private theorem witness_positive :
    ((3 / 2 : ℂ) • (1 : Matrix ((Fin 2 × Fin 2) × Fin 2)
      ((Fin 2 × Fin 2) × Fin 2) ℂ) - P - Q).PosSemidef := by
  let B : Matrix (Fin 4) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
    ![fun x => if x = ((0, 0), 0) then 1 else
        if x = ((0, 1), 1) ∨ x = ((1, 0), 1) then -1 else 0,
      fun x => if x = ((0, 1), 1) then 1 else if x = ((1, 0), 1) then -1 else 0,
      fun x => if x = ((1, 1), 1) then 1 else
        if x = ((0, 1), 0) ∨ x = ((1, 0), 0) then -1 else 0,
      fun x => if x = ((0, 1), 0) then 1 else if x = ((1, 0), 0) then -1 else 0]
  let D : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
    Matrix.diagonal fun x => if x = ((0, 0), 1) ∨ x = ((1, 1), 0) then 3 / 2 else 0
  have hD : D.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro x
    dsimp only
    split_ifs <;> norm_num [Complex.le_def]
  have he : (3 / 2 : ℂ) • (1 : Matrix ((Fin 2 × Fin 2) × Fin 2)
      ((Fin 2 × Fin 2) × Fin 2) ℂ) - P - Q = (1 / 2 : ℂ) • (B.conjTranspose * B) + D := by
    ext x y
    change (3 / 2 : ℂ) * (1 : Matrix ((Fin 2 × Fin 2) × Fin 2)
      ((Fin 2 × Fin 2) × Fin 2) ℂ) x y - P x y - Q x y =
        (1 / 2 : ℂ) * (∑ k : Fin 4, star (B k x) * B k y) + D x y
    rw [P.eq_1, Q.eq_1]
    rcases x with ⟨⟨a, b⟩, r⟩
    rcases y with ⟨⟨c, d⟩, s⟩
    fin_cases a <;> fin_cases b <;> fin_cases r <;>
      fin_cases c <;> fin_cases d <;> fin_cases s <;>
      norm_num [B, D, Fin.sum_univ_succ,
        bellDensity, bellVector, D5.S3.Quantum.QubitWitnesses.bellCoefficients,
        Matrix.vecMulVec_apply, complex_sqrt_two_inv_mul_self]
  rw [he]
  exact ((Matrix.posSemidef_conjTranspose_mul_self B).smul
    (show (0 : ℂ) ≤ 1 / 2 by norm_num [Complex.le_def])).add hD

private theorem no_joint_channel : ¬ ChannelCompatible depol depol := by
  rintro ⟨J, hJ, hL, hR⟩
  have hn := (jointChoi_positive J hJ).trace_mul_nonneg witness_positive
  have ht := jointChoi_trace J hJ
  obtain ⟨hp, hq⟩ := jointChoi_overlaps J hL hR
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, ht, hp, hq] at hn
  norm_num [Complex.le_def] at hn

theorem result : ¬ claim := by
  intro h
  have hc : IsCPTP depol := by
    rw [depol.eq_1]
    simpa only [IsCPTP, D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation.IsCPTP,
      show (1 - (7 / 10 : ℝ)) = 3 / 10 by norm_num] using dep_cptp (7 / 10) (by norm_num) (by norm_num)
  exact no_joint_channel (h 2 depol depol hc hc all_projective_tests)

end D5.S3.Quantum.QuantumChannels.ProjectiveTestChannelCompatibilityRefutation
