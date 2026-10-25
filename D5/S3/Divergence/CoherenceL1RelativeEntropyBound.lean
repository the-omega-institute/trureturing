/- GID: D5/S3/Divergence/CoherenceL1RelativeEntropyBound
   generality: G
   mirror-B: D5/B/S3/Divergence/CoherenceL1RelativeEntropyBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The l1 coherence dominates relative entropy coherence in every finite dimension. -/

/- result
   proof_shape: content
   escape_witness: AudenaertBinaryHolevoBound.log_hasDerivAt_affine_of_lower_bound
   admission_basis: open-problem-resolution (#16965; Proved)
   Direct frozen dependencies (declaration identities from the scoped Lean report):
     D5/S3/ArithSums/TwoPointSlabSupport — D5.S3.ArithSums.TwoPointSlabSupport.logWidths
       statement_id: sha256:189bd2747ec55979eeaa109e8a25ce976d33c61cba999590c9ac6d19b17d5a3b
     D5/S3/ArithSums/TwoPointSlabSupport — D5.S3.ArithSums.TwoPointSlabSupport.log_widths_bounds
       statement_id: sha256:bcaece7b400e20f09087f962ec91d0d57e3e86b3d2221141bc1ae5c69ae5e642
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.logDeriv
       statement_id: sha256:a90f9dee354f46f189f6580ba1b3ae88bf427894750c54a05e740869b0e89512
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.logDeriv_integrable
       statement_id: sha256:d29e5e978197cc2c2de8ca45a2a7755f2a8e20db18bc426f43ecd264d09883ef
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.pairKernel_integrable
       statement_id: sha256:2d1aa7b386439f55fc7ab6b5c4cba569df303e5472bb677060159813bc77f53c
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.resolvent_eq_spectral
       statement_id: sha256:32418c28ea14eea0ab3014b59c0f7eca014560cee394906ca2dc45ba82bdc469
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.scalarKernel_integrable
       statement_id: sha256:762111bf42f950c5b47a6fd56962947daa7e826439dcce62728a45fbcc7ca303
     D5/S3/Divergence/LogDerivTrace — D5.S3.Divergence.LogDerivTrace.trace_mul_logDeriv
       statement_id: sha256:f6fc2b2f36fe0ff12234183b5817929ace3e6949f49b2e10b7bf0f4ab5c1bbd5
     D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics — D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.sum_succ_sub_castSucc
       statement_id: sha256:4f021acd0150993eb37275dae31f1933287bfd4483ef95a2b47d9921dffc8a79
     D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability — D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_isometry
       statement_id: sha256:4788fda704d1194f8a5bde2ab1145d8e251a3dab3778b671874f5829488f6faa
     D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability — D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg
       statement_id: sha256:4e1e2463b054d4f1a17a47dfa173be720d81b8370e9189ac369460319c5840c1
     D5/S3/Quantum/Foundation/FiniteKrausChannel — D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
       statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
     D5/S3/Quantum/Foundation/FiniteKrausChannel — D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
       statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
     D5/S3/Quantum/Foundation/FiniteTraceDistance — D5.S3.Quantum.Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues
       statement_id: sha256:e079c550fa808a0eb9281e4fd4662a1ea12091a4328d1330c268597ffc16be91
     D5/S3/Quantum/Foundation/FiniteTraceDistance — D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
       statement_id: sha256:12ad034b5758446e6d628c75121b3ad5f0c80bb305937e8c9ff87e82076bc059
     D5/S3/Quantum/Foundation/FiniteTraceDistance — D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_neg
       statement_id: sha256:d7a81ef774c91a733d963a18aa1a998fd412bb6e352db4f96b70ec875b1b00ec
     D5/S3/Quantum/Foundation/FiniteTraceDistance — D5.S3.Quantum.Foundation.FiniteTraceDistance.trace_norm_jordan_mass
       statement_id: sha256:fdb8cb601f51df385251551cad923f9150a7104b67ce271fcb777ba680d61c61
     D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation — D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence
       statement_id: sha256:98e51dfcc3b4c9749f7203b01d5724517298b01fb61eb11df4034597f346db3b
     D5/S3/Quantum/Subentropy/UniformIntegrals — D5.S3.Quantum.Subentropy.UniformIntegrals.reciprocal_difference
       statement_id: sha256:cc1fc2c5546f64c4f3b667a1256819478938b93163884fe5498e566d0ac44d70
     D5/S3/Weil/ZetaLinear/RankTrace — RHLinalg.trace_mul_nonneg_of_posSemidef
       statement_id: sha256:d0be9623184a0aa6b2753f04a89d828122fe7292de10124c81506a795f6decf6
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17312.
   The published owner FinitePathDynamics.sum_succ_sub_castSucc is also an unfinished
   audit target in #17312; its declaration statement_id is
   sha256:4f021acd0150993eb37275dae31f1933287bfd4483ef95a2b47d9921dffc8a79.
   IsState and vonNeumann2 are shared with the frozen I module
   QuantumTriangularJensenShannonRefutation, which imports this G owner.
   TraceExpExponentialConvexityRefutation.IsDensity states the same condition;
   its I module is not on this module's dependency path.
   The claim uses the frozen l1Coherence owner as specified by the convention;
   its off-diagonal source expression is normalized termwise inside the proof.
   The binary entropy difference is expanded inside the proof.
   Binary pinching uses the frozen finite Kraus-map construction with the two
   complementary factors P and 1-P.
   Declarations and actual consumers:
     coordinate_binaryPinch_apply: proof_shape: bind-only; consumers: partialPinch_succ.
     rowL2_le_rowL1: proof_shape: bind-only; consumers: row_bound_le_coherenceL1.
     result: proof_shape: content; escape_witness: AudenaertBinaryHolevoBound.log_hasDerivAt_affine_of_lower_bound; consumers: none in the selected source modules.
     vectorSq_nonneg: proof_shape: bind-only; consumers: traceNorm_basis_row.
     reflection_hermitian: proof_shape: bind-only; consumers: pinch_entropy_eq_qjs, pinch_entropy_le.
     binaryPinch: proof_shape: bind-only; consumers: binaryPinch_average, coordinate_binaryPinch_apply, coordinate_pinch_entropy_le, isState_binaryPinch, partialPinch_isState, partialPinch_succ, pinch_entropy_eq_qjs, pinch_entropy_le, trace_binaryPinch.
     entropy_telescope: proof_shape: bind-only; consumers: claim_of_binaryHolevo.
     vectorSq_eq_zero: proof_shape: bind-only; consumers: traceNorm_basis_row.
     basisVector_sq: proof_shape: bind-only; consumers: traceNorm_basis_row.
     pinching_row_traceNorm: proof_shape: bind-only; consumers: coordinate_pinch_entropy_le.
     vector_dot_star: proof_shape: bind-only; consumers: traceNorm_basis_row.
     reflection_unitary: proof_shape: bind-only; consumers: pinch_entropy_eq_qjs, pinch_entropy_le.
     projection_offdiag_sq_zero: proof_shape: bind-only; consumers: reflection_traceNorm.
     coordinateProjection_hermitian: proof_shape: bind-only; consumers: coordinate_pinch_entropy_le, partialPinch_isState.
     row_bound_le_coherenceL1: proof_shape: bind-only; consumers: claim_of_binaryHolevo.
     trace_binaryPinch: proof_shape: bind-only; consumers: isState_binaryPinch.
     partialPinch_isState: proof_shape: content; escape_witness: partialPinch_isState; consumers: coordinate_pinch_entropy_le.
     coordinateProjection_idempotent: proof_shape: bind-only; consumers: coordinate_pinch_entropy_le, partialPinch_isState.
     reflection_difference: proof_shape: bind-only; consumers: reflection_traceNorm.
     reflection: proof_shape: bind-only; consumers: binaryPinch_average, pinch_entropy_eq_qjs, pinch_entropy_le, reflection_difference, reflection_hermitian, reflection_traceNorm, reflection_unitary.
     sqrt_add_of_mul_eq_zero: proof_shape: bind-only; consumers: traceNorm_nilpotent_symmetrize.
     pinch_entropy_eq_qjs: proof_shape: bind-only; consumers: pinch_entropy_le.
     vonNeumann2_unitary: proof_shape: bind-only; consumers: pinch_entropy_eq_qjs.
     reflection_traceNorm: proof_shape: bind-only; consumers: pinch_entropy_le.
     partialPinch_succ: proof_shape: bind-only; consumers: coordinate_pinch_entropy_le, partialPinch_isState.
     sqrt_mul_eq_zero: proof_shape: bind-only; consumers: sqrt_add_of_mul_eq_zero.
     partialPinch_final: proof_shape: bind-only; consumers: claim_of_binaryHolevo.
     traceNorm_isometry_right: proof_shape: bind-only; consumers: traceNorm_two_unitaries.
     traceNorm_basis_row: proof_shape: bind-only; consumers: pinching_row_traceNorm.
     isState_unitary: proof_shape: bind-only; consumers: pinch_entropy_le.
     traceNorm_two_unitaries: proof_shape: bind-only; consumers: traceNorm_conjTranspose.
     pinch_entropy_le: proof_shape: bind-only; consumers: coordinate_pinch_entropy_le.
     partialPinch_zero: proof_shape: bind-only; consumers: claim_of_binaryHolevo, partialPinch_isState.
     claim_of_binaryHolevo: proof_shape: content; escape_witness: partialPinch_isState; consumers: result.
     claim: proof_shape: bind-only; consumers: claim_of_binaryHolevo, result.
     traceNorm_conjTranspose: proof_shape: bind-only; consumers: traceNorm_nilpotent_symmetrize.
     traceNorm_isometry_left: proof_shape: bind-only; consumers: traceNorm_isometry_right, traceNorm_two_unitaries.
     pinching_row_eq_outer: proof_shape: bind-only; consumers: pinching_row_traceNorm.
     coherenceRel: proof_shape: bind-only; consumers: claim, claim_of_binaryHolevo.
     IsState: proof_shape: bind-only; consumers: claim, claim_of_binaryHolevo, coordinate_pinch_entropy_le, isState_binaryPinch, isState_unitary, partialPinch_isState, pinch_entropy_eq_qjs, pinch_entropy_le.
     binaryPinch_average: proof_shape: bind-only; consumers: pinch_entropy_eq_qjs.
     traceNorm_nilpotent_symmetrize: proof_shape: bind-only; consumers: reflection_traceNorm.
     coherenceL1_eq_twice_upper: proof_shape: bind-only; consumers: row_bound_le_coherenceL1.
     isState_binaryPinch: proof_shape: bind-only; consumers: partialPinch_isState.
     coordinate_pinch_entropy_le: proof_shape: content; escape_witness: partialPinch_isState; consumers: claim_of_binaryHolevo.
     partialPinch: proof_shape: bind-only; consumers: claim_of_binaryHolevo, coordinate_pinch_entropy_le, partialPinch_final, partialPinch_isState, partialPinch_succ, partialPinch_zero, pinching_row_eq_outer, pinching_row_traceNorm.
     vonNeumann2: proof_shape: bind-only; consumers: claim_of_binaryHolevo, coherenceRel, coordinate_pinch_entropy_le, pinch_entropy_eq_qjs, pinch_entropy_le, vonNeumann2_unitary.
-/

import D5.S3.Divergence.AudenaertBinaryHolevoBound
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation
import D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics

noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators NNReal Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Divergence.CoherenceL1RelativeEntropyBound
open D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation (l1Coherence)
open scoped BigOperators ComplexOrder

def IsState {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

noncomputable def vonNeumann2 {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re

noncomputable def coherenceRel {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  vonNeumann2 (Matrix.diagonal fun i => ρ i i) - vonNeumann2 ρ

def claim : Prop :=
  ∀ n : ℕ, ∀ ρ : Matrix (Fin n) (Fin n) ℂ, IsState ρ → coherenceRel ρ ≤
    D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence ρ

open Matrix
open scoped BigOperators ComplexOrder


private def binaryPinch {n : ℕ} (P ρ : Matrix (Fin n) (Fin n) ℂ) :=
  D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    (fun b : Bool => if b then P else 1-P)
    (fun b : Bool => (if b then P else 1-P)ᴴ) ρ

def reflection {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) := (2 : ℂ) • P - 1

theorem reflection_hermitian {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.IsHermitian) : (reflection P).IsHermitian := by
  change ((2 : ℂ) • P - 1)ᴴ = (2 : ℂ) • P - 1
  simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP.eq]

theorem reflection_unitary {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) : reflection P ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hp : IsStarProjection P := ⟨hPP, hP.isSelfAdjoint⟩
  simpa only [reflection, Matrix.unitaryGroup, two_smul, two_mul] using
    hp.two_mul_sub_one_mem_unitary

private theorem binaryPinch_average {n : ℕ} (P ρ : Matrix (Fin n) (Fin n) ℂ) :
    binaryPinch P ρ = (1/2 : ℂ) • (ρ + reflection P * ρ * reflection P) := by
  simp only [binaryPinch, D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus,
    Fintype.sum_bool, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Bool.false_eq_true, if_false, if_true, Matrix.conjTranspose_conjTranspose, reflection, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.one_mul, smul_add, smul_sub, smul_smul]
  module

private theorem vonNeumann2_unitary {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    vonNeumann2 (U.val * ρ * U.valᴴ) = vonNeumann2 ρ := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) U
  have hf : ContinuousOn (fun x : ℝ => x * Real.logb 2 x) (spectrum ℝ ρ) :=
    (Set.toFinite (spectrum ℝ ρ)).continuousOn _
  have hs : IsSelfAdjoint ρ := hρ
  have hc := StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    φ (fun x : ℝ => x * Real.logb 2 x) ρ (hf := hf)
    (hφ := φ.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional)
    (ha := hρ) (hφa := hs.map φ)
  have hc' : cfc (fun x : ℝ => x * Real.logb 2 x) (U.val * ρ * U.valᴴ) =
      U.val * cfc (fun x : ℝ => x * Real.logb 2 x) ρ * U.valᴴ := by
    simpa [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hc.symm
  have huu : U.valᴴ * U.val = 1 := by simpa only [Matrix.star_eq_conjTranspose] using U.prop.1
  simp only [vonNeumann2, hc', Matrix.trace_mul_cycle, huu, Matrix.one_mul]

private theorem isState_unitary {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : IsState ρ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    IsState (U.val * ρ * U.valᴴ) := by
  constructor
  · exact hρ.1.mul_mul_conjTranspose_same U.val
  · have huu : U.valᴴ * U.val = 1 := by simpa only [Matrix.star_eq_conjTranspose] using U.prop.1
    rw [Matrix.trace_mul_cycle, huu, Matrix.one_mul, hρ.2]

private theorem trace_binaryPinch {n : ℕ} (P ρ : Matrix (Fin n) (Fin n) ℂ)
    (hPP : P * P = P) : (binaryPinch P ρ).trace = ρ.trace := by
  have hQQ : (1-P) * (1-P) = 1-P := (show IsIdempotentElem P from hPP).one_sub
  simp only [binaryPinch, D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus,
    Fintype.sum_bool, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Bool.false_eq_true, if_false, if_true, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.trace_add, Matrix.trace_mul_cycle P ρ P,
    Matrix.trace_mul_cycle (1-P) ρ (1-P), hPP, hQQ]
  rw [← Matrix.trace_add]
  congr 1
  noncomm_ring

private theorem isState_binaryPinch {n : ℕ} (P ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : IsState ρ) (hP : P.IsHermitian) (hPP : P * P = P) : IsState (binaryPinch P ρ) := by
  constructor
  · have hQ : (1-P).IsHermitian := Matrix.isHermitian_one.sub hP
    have hp := hρ.1.mul_mul_conjTranspose_same P
    have hq := hρ.1.mul_mul_conjTranspose_same (1-P)
    simpa only [hP.eq, hQ.eq, binaryPinch, D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus,
    Fintype.sum_bool, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Bool.false_eq_true, if_false, if_true, Matrix.conjTranspose_conjTranspose] using hp.add hq
  · rw [trace_binaryPinch P ρ hPP, hρ.2]

private theorem pinch_entropy_eq_qjs {n : ℕ} (P ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : IsState ρ) (hP : P.IsHermitian) (hPP : P * P = P) :
    vonNeumann2 (binaryPinch P ρ) - vonNeumann2 ρ =
      (fun {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) => vonNeumann2 ((1/2 : ℂ) • (ρ + σ)) - (vonNeumann2 ρ + vonNeumann2 σ) / 2) ρ (reflection P * ρ * reflection P) := by
  have hv := vonNeumann2_unitary ρ hρ.1.isHermitian ⟨reflection P, reflection_unitary P hP hPP⟩
  simp only [(reflection_hermitian P hP).eq] at hv
  dsimp only
  rw [ ← binaryPinch_average, hv]
  ring

open Matrix
open scoped BigOperators ComplexOrder

private def partialPinch {n : ℕ} (m : ℕ) (ρ : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i => Set.indicator {j | i = j ∨ (m ≤ i.val ∧ m ≤ j.val)} (ρ i)

private theorem coordinateProjection_hermitian {n : ℕ} (k : Fin n) :
    ((Matrix.diagonal (Pi.single k (1 : ℂ)))).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  by_cases h : i = k <;> simp [Pi.single_apply, h, isSelfAdjoint_iff]

private theorem coordinateProjection_idempotent {n : ℕ} (k : Fin n) :
    (Matrix.diagonal (Pi.single k (1 : ℂ))) * (Matrix.diagonal (Pi.single k (1 : ℂ))) = (Matrix.diagonal (Pi.single k (1 : ℂ))) := by
  simp only [Pi.single_apply, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [Pi.single_apply]

private theorem coordinate_binaryPinch_apply {n : ℕ} (k i j : Fin n)
    (ρ : Matrix (Fin n) (Fin n) ℂ) :
    binaryPinch ((Matrix.diagonal (Pi.single k (1 : ℂ)))) ρ i j =
      if (i = k ↔ j = k) then ρ i j else 0 := by
  have hQ : (1 : Matrix (Fin n) (Fin n) ℂ) - (Matrix.diagonal (Pi.single k (1 : ℂ))) =
      diagonal (fun i => if i = k then 0 else 1) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    simp only [Pi.sub_apply, Pi.one_apply, Pi.single_apply]
    split_ifs <;> simp
  simp only [binaryPinch, D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus,
    Fintype.sum_bool, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Bool.false_eq_true, if_false, if_true, Matrix.conjTranspose_conjTranspose]
  rw [hQ]
  simp only [Pi.single_apply, Matrix.add_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i = k <;> by_cases hj : j = k <;> simp [hi, hj]

private theorem partialPinch_zero {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) :
    partialPinch 0 ρ = ρ := by
  ext i j
  simp [partialPinch, Set.indicator_apply, Set.mem_setOf_eq]

private theorem partialPinch_succ {n : ℕ} (k : Fin n) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    binaryPinch ((Matrix.diagonal (Pi.single k (1 : ℂ)))) (partialPinch k.val ρ) =
      partialPinch (k.val+1) ρ := by
  ext i j
  rw [coordinate_binaryPinch_apply]
  simp only [partialPinch, Set.indicator_apply, Set.mem_setOf_eq]
  by_cases hij : i = j
  · subst j
    simp
  · by_cases hi : i = k <;> by_cases hj : j = k
    · exact False.elim (hij (hi.trans hj.symm))
    · subst i
      simp only [hij, hj, iff_false, not_true_eq_false, ite_false, true_iff,
        Nat.not_succ_le_self, false_and, or_false]
    · subst j
      simp [hi, Ne.symm hi, Nat.not_succ_le_self]
    · have h1 : (k.val ≤ i.val ∧ k.val ≤ j.val) ↔
          (k.val+1 ≤ i.val ∧ k.val+1 ≤ j.val) := by omega
      simp only [hi, hj, false_iff, not_false_eq_true, ite_true, hij, false_or]
      simp only [h1]

private theorem partialPinch_final {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) :
    partialPinch n ρ = Matrix.diagonal (fun i => ρ i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [partialPinch, Set.indicator_apply, Set.mem_setOf_eq]
  · simp [partialPinch, Set.indicator_apply, Set.mem_setOf_eq, Matrix.diagonal, hij, Ne.symm hij, Nat.not_le.mpr i.isLt]

private theorem partialPinch_isState {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : IsState ρ) (m : ℕ) (hm : m ≤ n) : IsState (partialPinch m ρ) := by
  induction m with
  | zero => simpa [partialPinch_zero] using hρ
  | succ m ih =>
    have hmn : m < n := Nat.lt_of_succ_le hm
    let k : Fin n := ⟨m, hmn⟩
    have hs := isState_binaryPinch ((Matrix.diagonal (Pi.single k (1 : ℂ)))) (partialPinch m ρ)
      (ih (by omega)) (coordinateProjection_hermitian k) (coordinateProjection_idempotent k)
    change IsState (binaryPinch ((Matrix.diagonal (Pi.single k (1 : ℂ)))) (partialPinch k.val ρ)) at hs
    rw [partialPinch_succ] at hs
    exact hs

private theorem pinching_row_eq_outer {n : ℕ} (k : Fin n) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.diagonal (Pi.single k (1 : ℂ))) * partialPinch k.val ρ * (1-(Matrix.diagonal (Pi.single k (1 : ℂ)))) =
      Matrix.vecMulVec (fun i => if i = k then (1 : ℂ) else 0)
        (fun j => if k.val < j.val then ρ k j else 0) := by
  have hQ : (1 : Matrix (Fin n) (Fin n) ℂ) - (Matrix.diagonal (Pi.single k (1 : ℂ))) =
      diagonal (fun i => if i = k then 0 else 1) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    simp only [Pi.sub_apply, Pi.one_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hQ]
  ext i j
  simp only [Pi.single_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.vecMulVec_apply, partialPinch, Set.indicator_apply, Set.mem_setOf_eq]
  by_cases hi : i = k
  · subst i
    by_cases hj : j = k
    · subst j; simp
    · have ht : (k.val ≤ j.val) ↔ k.val < j.val := Ne.ge_iff_gt (Fin.val_ne_of_ne hj)
      have hf : (k ≤ j) ↔ k < j := by exact ht
      simp [hj, Ne.symm hj, hf]
  · simp [hi]

open scoped BigOperators ComplexOrder

private theorem rowL2_le_rowL1 {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    ‖WithLp.toLp 2 (fun j : Fin n => if k < j then ρ k j else 0)‖ ≤ ‖WithLp.toLp 1 (fun j : Fin n => if k < j then ρ k j else 0)‖ := by
  let v : Fin n → ℂ := fun j => if k < j then ρ k j else 0
  have hv : WithLp.toLp 2 v = ∑ i, PiLp.single 2 i (v i) := by
    ext j
    simp
  rw [show WithLp.toLp 2 (fun j : Fin n => if k < j then ρ k j else 0) =
      ∑ i, PiLp.single 2 i (v i) from hv]
  simpa only [PiLp.norm_single, PiLp.norm_eq_of_L1, PiLp.toLp_apply] using
    norm_sum_le (Finset.univ) (fun i => PiLp.single 2 i (v i))

private theorem coherenceL1_eq_twice_upper {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) : l1Coherence ρ = 2 * ∑ k, ‖WithLp.toLp 1 (fun j : Fin n => if k < j then ρ k j else 0)‖ := by
  have hnorm (i j : Fin n) : ‖ρ i j‖ = ‖ρ j i‖ := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) hρ.eq
    change star (ρ j i) = ρ i j at h
    rw [← h, norm_star]
  have hsplit (i j : Fin n) :
      (if i ≠ j then ‖ρ i j‖ else 0) =
      (if i < j then ‖ρ i j‖ else 0) + (if j < i then ‖ρ i j‖ else 0) := by
    rcases lt_trichotomy i j with h | h | h <;> simp [h, ne_of_lt, ne_of_gt, not_lt_of_ge, le_of_lt]
  have hswap : (∑ i : Fin n, ∑ j : Fin n, if j < i then ‖ρ i j‖ else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then ‖ρ i j‖ else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hnorm]
  have hsource : l1Coherence ρ = ∑ i, ∑ j, if i ≠ j then ‖ρ i j‖ else 0 := by
    simp only [l1Coherence, ite_not]
  rw [hsource]
  simp only [hsplit, Finset.sum_add_distrib, hswap,
    PiLp.norm_eq_of_L1, PiLp.toLp_apply, apply_ite norm, norm_zero]
  ring

private theorem row_bound_le_coherenceL1 {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) : 2 * (∑ k, ‖WithLp.toLp 2 (fun j : Fin n => if k < j then ρ k j else 0)‖) ≤ l1Coherence ρ := by
  rw [coherenceL1_eq_twice_upper ρ hρ]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => rowL2_le_rowL1 ρ k)) (by norm_num)

private theorem entropy_telescope {n : ℕ} (s : Fin (n+1) → ℝ) :
    s (Fin.last n) - s 0 = ∑ k : Fin n, (s k.succ - s k.castSucc) := by
  have hc := D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.sum_succ_sub_castSucc n (fun i => (s i : ℂ))
  exact_mod_cast hc.symm

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance



private theorem basisVector_sq {n : ℕ} (k : Fin n) : star ((Pi.single k (1 : ℂ))) ⬝ᵥ (Pi.single k (1 : ℂ)) = 1 := by
  simpa only [dotProduct_single_one, Pi.star_apply, Pi.single_eq_same, star_one]

private theorem vector_dot_star {n : ℕ} (v : Fin n → ℂ) : v ⬝ᵥ star v = ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_sum, Complex.ofReal_pow]

private theorem vectorSq_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ (∑ j, ‖v j‖ ^ 2 : ℝ) := by
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

private theorem vectorSq_eq_zero {n : ℕ} (v : Fin n → ℂ) (h : (∑ j, ‖v j‖ ^ 2 : ℝ) = 0) : v = 0 := by
  have hz : ‖WithLp.toLp 2 v‖ ^ 2 = 0 := by
    simpa only [PiLp.norm_sq_eq_of_L2] using h
  have hv := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact congrArg WithLp.ofLp hv

private theorem traceNorm_basis_row {n : ℕ} (k : Fin n) (v : Fin n → ℂ) :
    traceNorm (vecMulVec ((Pi.single k (1 : ℂ))) v) = Real.sqrt ((∑ j, ‖v j‖ ^ 2 : ℝ)) := by
  by_cases hv : (∑ j, ‖v j‖ ^ 2 : ℝ) = 0
  · rw [vectorSq_eq_zero v hv]
    have hm : vecMulVec ((Pi.single k (1 : ℂ))) (0 : Fin n → ℂ) = 0 := Matrix.vecMulVec_zero _
    rw [hm]
    simp [traceNorm]
  · have hp : 0 < (∑ j, ‖v j‖ ^ 2 : ℝ) := lt_of_le_of_ne (vectorSq_nonneg v) (Ne.symm hv)
    let r := Real.sqrt ((∑ j, ‖v j‖ ^ 2 : ℝ))
    have hr : 0 < r := Real.sqrt_pos.mpr hp
    have hs : r*r = (∑ j, ‖v j‖ ^ 2 : ℝ) := Real.mul_self_sqrt hp.le
    let V := vecMulVec (star v) v
    have hgram : (vecMulVec ((Pi.single k (1 : ℂ))) v)ᴴ * vecMulVec ((Pi.single k (1 : ℂ))) v = V := by
      rw [conjTranspose_vecMulVec, vecMulVec_mul_vecMulVec, basisVector_sq]
      simp [V]
    have hV : V.PosSemidef := posSemidef_vecMulVec_star_self v
    have hVV : V*V = ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) • V := by
      simp only [V, vecMulVec_mul_vecMulVec, vector_dot_star, vecMulVec_smul]
    have hroot : ((r : ℂ)⁻¹ • V) * ((r : ℂ)⁻¹ • V) = V := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hVV, smul_smul]
      have hrr : (r : ℂ)⁻¹ * (r : ℂ)⁻¹ * ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) = 1 := by
        have hs' : (r : ℂ)*(r : ℂ) = ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) := by exact_mod_cast hs
        rw [← hs']
        field_simp
      rw [hrr, one_smul]
    have hb : 0 ≤ (r : ℂ)⁻¹ • V := by
      apply Matrix.PosSemidef.nonneg
      exact hV.smul (by exact_mod_cast (inv_nonneg.mpr hr.le))
    have hsqrt := CFC.sqrt_unique hroot hb
    unfold traceNorm
    rw [hgram, hsqrt, trace_smul, trace_vecMulVec]
    have hdot : star v ⬝ᵥ v = ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) := by
      rw [dotProduct_comm, vector_dot_star]
    rw [hdot]
    change (((r : ℂ)⁻¹ * ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ))).re = r
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re, ← hs]
    field_simp

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance

/- The left-unitary trace-norm identity adapts Alex Meiburg's physlib
   QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean at
   6a09b2d1761a0d4430083045a247eb121d8da260 (Apache-2.0).
   Copyright (c) 2025 Alex Meiburg. The license and immutable locator are retained
   in Library/QuantumStates/meiburg2025svd.md. -/
private theorem traceNorm_isometry_left {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ*U=1) : traceNorm (U*A)=traceNorm A := by
  unfold traceNorm
  congr 1
  simp only [Matrix.conjTranspose_mul, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc Aᴴ Uᴴ U, hU, Matrix.mul_one]

private theorem traceNorm_isometry_right {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ*U=1) : traceNorm (A*Uᴴ)=traceNorm A := by
  rw [← traceNorm_isometry_left (A*Uᴴ) U hU]
  rw [← Matrix.mul_assoc]
  exact D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_isometry U hU A

private theorem traceNorm_two_unitaries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (U V : unitaryGroup (Fin n) ℂ) : traceNorm (U.val*A*V.valᴴ)=traceNorm A := by
  rw [traceNorm_isometry_right _ _ (by simpa only [Matrix.star_eq_conjTranspose] using V.prop.1),
    traceNorm_isometry_left _ _ (by simpa only [Matrix.star_eq_conjTranspose] using U.prop.1)]

private theorem traceNorm_conjTranspose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    traceNorm Aᴴ=traceNorm A := by
  have hH : (Aᴴ*A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  obtain ⟨V,W,hA⟩ := exists_svd_sqrt_eigenvalues A
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  have hDH : Dᴴ=D := by simp [D,Matrix.diagonal_conjTranspose]
  have hAt : Aᴴ=W.val*D*V.valᴴ := by
    rw [hA,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,hDH]
    simp only [Matrix.mul_assoc]
  calc
    traceNorm Aᴴ=traceNorm (W.val*D*V.valᴴ) := by rw [hAt]
    _=traceNorm D := traceNorm_two_unitaries D W V
    _=traceNorm (V.val*D*W.valᴴ) := (traceNorm_two_unitaries D V W).symm
    _=traceNorm A := by rw [hA]

private theorem sqrt_mul_eq_zero {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : 0≤A) (hB : 0≤B) (hAB : A*B=0) : CFC.sqrt A*CFC.sqrt B=0 := by
  let S := CFC.sqrt A
  let T := CFC.sqrt B
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hT : T.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian
  have hBh : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hB).isHermitian
  have hSS : S*S=A := CFC.sqrt_mul_sqrt_self A hA
  have hTT : T*T=B := CFC.sqrt_mul_sqrt_self B hB
  have hSB : S*B=0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    have he : (S*B)ᴴ*(S*B)=0 := by
      simp only [Matrix.conjTranspose_mul,hS.eq,hBh.eq]
      calc
        _=B*(S*S)*B := by noncomm_ring
        _=0 := by rw [hSS,Matrix.mul_assoc,hAB,Matrix.mul_zero]
    rw [he]; simp
  have hTS : T*S=0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    have he : (T*S)ᴴ*(T*S)=0 := by
      simp only [Matrix.conjTranspose_mul,hS.eq,hT.eq]
      calc
        _=S*(T*T)*S := by noncomm_ring
        _=0 := by rw [hTT, hSB,Matrix.zero_mul]
    rw [he]; simp
  have he := congrArg Matrix.conjTranspose hTS
  simpa only [Matrix.conjTranspose_mul,hS.eq,hT.eq,Matrix.conjTranspose_zero] using he

private theorem sqrt_add_of_mul_eq_zero {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : 0≤A) (hB : 0≤B) (hAB : A*B=0) :
    CFC.sqrt (A+B)=CFC.sqrt A+CFC.sqrt B := by
  have hBA : B*A=0 := by
    have hAh := (Matrix.nonneg_iff_posSemidef.mp hA).isHermitian
    have hBh := (Matrix.nonneg_iff_posSemidef.mp hB).isHermitian
    have h := congrArg Matrix.conjTranspose hAB
    simpa only [Matrix.conjTranspose_mul,hAh.eq,hBh.eq,Matrix.conjTranspose_zero] using h
  apply CFC.sqrt_unique _ (add_nonneg (CFC.sqrt_nonneg A) (CFC.sqrt_nonneg B))
  simp only [Matrix.add_mul,Matrix.mul_add,sqrt_mul_eq_zero A B hA hB hAB,
    sqrt_mul_eq_zero B A hB hA hBA,zero_add,add_zero,CFC.sqrt_mul_sqrt_self A hA,
    CFC.sqrt_mul_sqrt_self B hB]

private theorem traceNorm_nilpotent_symmetrize {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hBB : B*B=0) : traceNorm (B+Bᴴ)=2*traceNorm B := by
  have hBdBd : Bᴴ*Bᴴ=0 := by rw [← Matrix.conjTranspose_mul,hBB]; simp
  have hg : (B+Bᴴ)ᴴ*(B+Bᴴ)=B*Bᴴ+Bᴴ*B := by
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_conjTranspose,Matrix.add_mul,
      Matrix.mul_add,hBB,hBdBd,zero_add,add_zero,add_comm]
  have hp : 0≤B*Bᴴ := (Matrix.posSemidef_self_mul_conjTranspose B).nonneg
  have hq : 0≤Bᴴ*B := (Matrix.posSemidef_conjTranspose_mul_self B).nonneg
  have hz : (B*Bᴴ)*(Bᴴ*B)=0 := by
    calc
      _=B*(Bᴴ*Bᴴ)*B := by noncomm_ring
      _=0 := by rw [hBdBd]; simp
  unfold traceNorm at hg ⊢
  rw [hg,sqrt_add_of_mul_eq_zero _ _ hp hq hz,Matrix.trace_add,map_add]
  have ht := traceNorm_conjTranspose B
  unfold traceNorm at ht
  simp only [Matrix.conjTranspose_conjTranspose] at ht
  rw [ht]
  ring

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance

private theorem projection_offdiag_sq_zero {n : ℕ} (P ρ : Matrix (Fin n) (Fin n) ℂ)
    (hPP : P*P=P) : (P*ρ*(1-P))*(P*ρ*(1-P))=0 := by
  have hqp : (1-P)*P=0 := (show IsIdempotentElem P from hPP).one_sub_mul_self
  calc
    _=P*ρ*((1-P)*P)*ρ*(1-P) := by noncomm_ring
    _=0 := by rw [hqp]; simp

private theorem reflection_difference {n : ℕ} (P ρ : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.IsHermitian) (hρ : ρ.IsHermitian) :
    ρ - reflection P * ρ * reflection P =
      (2 : ℂ) • (P*ρ*(1-P) + (P*ρ*(1-P))ᴴ) := by
  simp only [reflection, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one,hP.eq,hρ.eq,sub_mul,mul_sub,Matrix.mul_one,
    Matrix.one_mul,Matrix.smul_mul,Matrix.mul_smul,smul_add,smul_sub,smul_smul,Matrix.mul_assoc]
  module


private theorem reflection_traceNorm {n : ℕ} (P ρ : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P) (hρ : ρ.IsHermitian) :
    traceNorm (ρ-reflection P*ρ*reflection P)=4*traceNorm (P*ρ*(1-P)) := by
  rw [reflection_difference P ρ hP hρ]
  have hs := D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg (P*ρ*(1-P)+(P*ρ*(1-P))ᴴ) 2 (by norm_num)
  norm_num only [Complex.ofReal_ofNat] at hs
  rw [hs,traceNorm_nilpotent_symmetrize _ (projection_offdiag_sq_zero P ρ hPP)]
  ring

private theorem pinch_entropy_le (hH : (∀ n : ℕ, ∀ σ τ : Matrix (Fin n) (Fin n) ℂ, IsState σ → IsState τ → (fun {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) => vonNeumann2 ((1/2 : ℂ) • (ρ + σ)) - (vonNeumann2 ρ + vonNeumann2 σ) / 2) σ τ ≤ traceNorm (σ-τ)/2)) {n : ℕ}
    (P ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : IsState ρ)
    (hP : P.IsHermitian) (hPP : P*P=P) :
    vonNeumann2 (binaryPinch P ρ)-vonNeumann2 ρ≤2*traceNorm (P*ρ*(1-P)) := by
  let U : unitaryGroup (Fin n) ℂ := ⟨reflection P,reflection_unitary P hP hPP⟩
  have hu := isState_unitary ρ hρ U
  change IsState (reflection P*ρ*(reflection P)ᴴ) at hu
  rw [(reflection_hermitian P hP).eq] at hu
  have h := hH n ρ (reflection P*ρ*reflection P) hρ hu
  rw [← pinch_entropy_eq_qjs P ρ hρ hP hPP,reflection_traceNorm P ρ hP hPP hρ.1.isHermitian] at h
  linarith

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance

private theorem pinching_row_traceNorm {n : ℕ} (k : Fin n) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    traceNorm ((Matrix.diagonal (Pi.single k (1 : ℂ))) * partialPinch k.val ρ * (1-(Matrix.diagonal (Pi.single k (1 : ℂ))))) =
      ‖WithLp.toLp 2 (fun j : Fin n => if k < j then ρ k j else 0)‖ := by
  rw [pinching_row_eq_outer]
  have hb : (fun i : Fin n => if i = k then (1 : ℂ) else 0) = Pi.single k 1 := by
    funext i
    simp only [Pi.single_apply, eq_comm]
  rw [hb]
  change traceNorm (vecMulVec (Pi.single k (1 : ℂ))
    (fun j : Fin n => if k.val < j.val then ρ k j else 0)) = ‖WithLp.toLp 2 (fun j : Fin n => if k < j then ρ k j else 0)‖
  rw [traceNorm_basis_row k (fun j : Fin n => if k.val < j.val then ρ k j else 0)]
  rw [PiLp.norm_eq_of_L2]
  rfl

private theorem coordinate_pinch_entropy_le (hH : (∀ n : ℕ, ∀ σ τ : Matrix (Fin n) (Fin n) ℂ, IsState σ → IsState τ → (fun {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) => vonNeumann2 ((1/2 : ℂ) • (ρ + σ)) - (vonNeumann2 ρ + vonNeumann2 σ) / 2) σ τ ≤ traceNorm (σ-τ)/2)) {n : ℕ}
    (k : Fin n) (ρ : Matrix (Fin n) (Fin n) ℂ) (hρ : IsState ρ) :
    vonNeumann2 (partialPinch (k.val+1) ρ) - vonNeumann2 (partialPinch k.val ρ) ≤
      2 * ‖WithLp.toLp 2 (fun j : Fin n => if k < j then ρ k j else 0)‖ := by
  have h := pinch_entropy_le hH ((Matrix.diagonal (Pi.single k (1 : ℂ)))) (partialPinch k.val ρ)
    (partialPinch_isState ρ hρ k.val k.isLt.le)
    (coordinateProjection_hermitian k) (coordinateProjection_idempotent k)
  rw [partialPinch_succ, pinching_row_traceNorm] at h
  exact h

private theorem claim_of_binaryHolevo (hH : (∀ n : ℕ, ∀ σ τ : Matrix (Fin n) (Fin n) ℂ, IsState σ → IsState τ → (fun {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) => vonNeumann2 ((1/2 : ℂ) • (ρ + σ)) - (vonNeumann2 ρ + vonNeumann2 σ) / 2) σ τ ≤ traceNorm (σ-τ)/2)) : claim := by
  intro n ρ hρ
  let s : Fin (n+1) → ℝ := fun m => vonNeumann2 (partialPinch m.val ρ)
  have ht := entropy_telescope s
  have hc : coherenceRel ρ = ∑ k : Fin n,
      (vonNeumann2 (partialPinch (k.val+1) ρ)-vonNeumann2 (partialPinch k.val ρ)) := by
    simpa [s,coherenceRel,partialPinch_zero,partialPinch_final] using ht
  rw [hc]
  calc
    _ ≤ ∑ k : Fin n, 2*‖WithLp.toLp 2 (fun j : Fin n => if k < j then ρ k j else 0)‖ := Finset.sum_le_sum (fun k _ => coordinate_pinch_entropy_le hH k ρ hρ)
    _ = 2*∑ k : Fin n, ‖WithLp.toLp 2 (fun j : Fin n => if k < j then ρ k j else 0)‖ := (Finset.mul_sum ..).symm
    _ ≤ l1Coherence ρ := row_bound_le_coherenceL1 ρ hρ.1.isHermitian

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
theorem result : claim := claim_of_binaryHolevo D5.S3.Divergence.AudenaertBinaryHolevoBound.binaryHolevoBound

end D5.S3.Divergence.CoherenceL1RelativeEntropyBound
