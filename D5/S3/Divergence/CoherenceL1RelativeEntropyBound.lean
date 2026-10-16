/- GID: D5/S3/Divergence/CoherenceL1RelativeEntropyBound
   generality: G
   mirror-B: D5/B/S3/Divergence/CoherenceL1RelativeEntropyBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The l1 coherence dominates relative entropy coherence in every finite dimension. -/

/- result
   proof_shape: content
   escape_witness: none
   admission_basis: open-problem-resolution (#16965; Proved)
   Direct frozen dependencies (declaration identities at the synchronized base):
     D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm
       statement_id: sha256:ec2ace26dd8d3b1f1b18defca9f881e75ab25f3e1a67abd2b14cdc72e2702569
     D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
       statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
     D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
       statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
     D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_1
       statement_id: sha256:5dc7bcde8ce2ae710c058683e5324d31e0ca70317f167566967eee1cf3b23bbb
     D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus._proof_2
       statement_id: sha256:9b70ce4858eb731b17facafe93b167007eb9ca6533c641dc770fc553d31ddaa1
     D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_eq_max_re_tr_U
       statement_id: sha256:3487611db943d93cce4a86af60f6499c8a001bc73fe819953d9bfd08a4e811b1
     D5/S3/Quantum/Foundation/FiniteTraceDistance.exists_svd_sqrt_eigenvalues
       statement_id: sha256:e079c550fa808a0eb9281e4fd4662a1ea12091a4328d1330c268597ffc16be91
     D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm._proof_1
       statement_id: sha256:8ce2e9d271f33da05e69000cafc91db499f50cd47f0e5f7b154baa975a3a9cc6
     D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm._proof_2
       statement_id: sha256:2217a97717ba8d198ee9ee17356dad545d41f95282add3ad5df1790beb6ff791
     D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm._proof_7
       statement_id: sha256:5f854fd7eee62349e53f46e6718cdea507d64df8d2f6b1e2ba8e1da15cd9898c
     D5/S3/Divergence/LogDerivTrace.logDeriv
       statement_id: sha256:a90f9dee354f46f189f6580ba1b3ae88bf427894750c54a05e740869b0e89512
     D5/S3/Divergence/LogDerivTrace.spectralKernel_integrable
       statement_id: sha256:ce84a7384a48cb822aa5bc1d7f7aa973e3574de6bac1f1c2c2dcdc921eb7f380
     D5/S3/Divergence/LogDerivTrace.integrand_eq_spectral
       statement_id: sha256:99d9256f7f4e64c1b674ef70f29eac193906985fc138419f893118df96f68362
     D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef
       statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
     D5/S3/Divergence/LogDerivTrace.trace_mul_logDeriv
       statement_id: sha256:f6fc2b2f36fe0ff12234183b5817929ace3e6949f49b2e10b7bf0f4ab5c1bbd5
     D5/S3/Quantum/Foundation/FiniteTraceDistance.trace_norm_jordan_mass
       statement_id: sha256:fdb8cb601f51df385251551cad923f9150a7104b67ce271fcb777ba680d61c61
     D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_neg
       statement_id: sha256:d7a81ef774c91a733d963a18aa1a998fd412bb6e352db4f96b70ec875b1b00ec
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17312.
   The published owner FinitePathDynamics.sum_succ_sub_castSucc is also an unfinished
   audit target in #17312; its public declaration identity awaits the Stage B report.
   IsState and vonNeumann2 are moved unchanged from the frozen I owner
   QuantumTriangularJensenShannonRefutation; that module imports this G owner.
   The existing IsDensity predicate in TraceExpExponentialConvexityRefutation
   has the same condition but belongs to an I module; no G-to-I import is added.
   The binary entropy difference is expanded; no duplicate QJS2 alias is retained.
   Binary pinching uses the frozen finite Kraus-map construction with the two
   complementary factors P and 1-P; no separate sandwich-map construction is retained.
   Declarations and actual consumers:
     IsState: proof_shape: bind-only; consumers: claim, isState_unitary, isState_binaryPinch,
       pinch_entropy_eq_qjs, partialPinch_isState, pinch_entropy_le,
       coordinate_pinch_entropy_le, claim_of_binaryHolevo.
     vonNeumann2: proof_shape: bind-only; consumers: coherenceRel, vonNeumann2_unitary,
       pinch_entropy_eq_qjs, pinch_entropy_le, coordinate_pinch_entropy_le,
       claim_of_binaryHolevo.
     coherenceL1: proof_shape: bind-only; consumers: claim, coherenceL1_eq_twice_upper,
       row_bound_le_coherenceL1, claim_of_binaryHolevo.
     coherenceRel: proof_shape: bind-only; consumers: claim, claim_of_binaryHolevo.
     claim: proof_shape: bind-only; consumers: claim_of_binaryHolevo, result.
     binaryPinch: proof_shape: bind-only; consumers: binaryPinch_average, trace_binaryPinch,
       isState_binaryPinch, pinch_entropy_eq_qjs, coordinate_binaryPinch_apply,
       partialPinch_succ, partialPinch_isState, pinch_entropy_le, coordinate_pinch_entropy_le.
     reflection: proof_shape: bind-only; consumers: reflection_hermitian,
       reflection_unitary, binaryPinch_average, pinch_entropy_eq_qjs, reflection_difference,
       reflection_traceNorm, pinch_entropy_le.
     reflection_hermitian: proof_shape: bind-only; consumers:
       pinch_entropy_eq_qjs, pinch_entropy_le.
     reflection_unitary: proof_shape: bind-only; consumers: pinch_entropy_eq_qjs,
       pinch_entropy_le.
     binaryPinch_average: proof_shape: bind-only; consumers: pinch_entropy_eq_qjs.
     vonNeumann2_unitary: proof_shape: bind-only; consumers: pinch_entropy_eq_qjs.
     isState_unitary: proof_shape: bind-only; consumers: pinch_entropy_le.
     trace_binaryPinch: proof_shape: bind-only; consumers: isState_binaryPinch.
     isState_binaryPinch: proof_shape: bind-only; consumers: partialPinch_isState.
     pinch_entropy_eq_qjs: proof_shape: bind-only; consumers: pinch_entropy_le.
     partialPinch: proof_shape: bind-only; consumers: partialPinch_zero, partialPinch_succ,
       partialPinch_final, partialPinch_isState, pinching_row_eq_outer, pinching_row_traceNorm,
       coordinate_pinch_entropy_le, claim_of_binaryHolevo.
     coordinateProjection_hermitian: proof_shape: bind-only; consumers: partialPinch_isState,
       coordinate_pinch_entropy_le.
     coordinateProjection_idempotent: proof_shape: bind-only; consumers: partialPinch_isState,
       coordinate_pinch_entropy_le.
     coordinate_binaryPinch_apply: proof_shape: bind-only; consumers: partialPinch_succ.
     partialPinch_zero: proof_shape: bind-only; consumers: partialPinch_isState,
       claim_of_binaryHolevo.
     partialPinch_succ: proof_shape: bind-only; consumers: partialPinch_isState,
       coordinate_pinch_entropy_le.
     partialPinch_final: proof_shape: bind-only; consumers: claim_of_binaryHolevo.
     partialPinch_isState: proof_shape: content; consumers: coordinate_pinch_entropy_le.
     pinching_row_eq_outer: proof_shape: bind-only; consumers: pinching_row_traceNorm.
     rowL2_le_rowL1: proof_shape: bind-only; consumers: row_bound_le_coherenceL1.
     coherenceL1_eq_twice_upper: proof_shape: bind-only; consumers: row_bound_le_coherenceL1.
     row_bound_le_coherenceL1: proof_shape: bind-only; consumers: claim_of_binaryHolevo.
     entropy_telescope: proof_shape: bind-only; consumers: claim_of_binaryHolevo.
     basisVector_sq: proof_shape: bind-only; consumers: traceNorm_basis_row.
     vector_dot_star: proof_shape: bind-only; consumers: traceNorm_basis_row.
     vectorSq_nonneg: proof_shape: bind-only; consumers: traceNorm_basis_row.
     vectorSq_eq_zero: proof_shape: bind-only; consumers: traceNorm_basis_row.
     traceNorm_basis_row: proof_shape: bind-only; consumers: pinching_row_traceNorm.
     traceNorm_isometry_left: proof_shape: bind-only; consumers: traceNorm_isometry_right,
       traceNorm_two_unitaries.
     traceNorm_isometry_right: proof_shape: bind-only; consumers: traceNorm_two_unitaries.
     traceNorm_two_unitaries: proof_shape: bind-only; consumers: traceNorm_conjTranspose.
     traceNorm_conjTranspose: proof_shape: bind-only; consumers:
       traceNorm_nilpotent_symmetrize.
     sqrt_mul_eq_zero: proof_shape: bind-only; consumers: sqrt_add_of_mul_eq_zero.
     sqrt_add_of_mul_eq_zero: proof_shape: bind-only; consumers:
       traceNorm_nilpotent_symmetrize.
     traceNorm_nilpotent_symmetrize: proof_shape: bind-only; consumers: reflection_traceNorm.
     projection_offdiag_sq_zero: proof_shape: bind-only; consumers: reflection_traceNorm.
     reflection_difference: proof_shape: bind-only; consumers: reflection_traceNorm.
     reflection_traceNorm: proof_shape: bind-only; consumers: pinch_entropy_le.
     pinch_entropy_le: proof_shape: bind-only; consumers: coordinate_pinch_entropy_le.
     pinching_row_traceNorm: proof_shape: bind-only; consumers: coordinate_pinch_entropy_le.
     coordinate_pinch_entropy_le: proof_shape: bind-only; consumers: claim_of_binaryHolevo.
     claim_of_binaryHolevo: proof_shape: content; consumers: result.
-/

import D5.S3.Divergence.AudenaertBinaryHolevoBound
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics

noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators NNReal Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Divergence.CoherenceL1RelativeEntropyBound
open scoped BigOperators ComplexOrder

def IsState {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

noncomputable def vonNeumann2 {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  -(Matrix.trace (cfc (fun x : ℝ => x * Real.logb 2 x) ρ)).re

noncomputable def coherenceL1 {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, if i ≠ j then ‖ρ i j‖ else 0

noncomputable def coherenceRel {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  vonNeumann2 (Matrix.diagonal fun i => ρ i i) - vonNeumann2 ρ

def claim : Prop :=
  ∀ n : ℕ, ∀ ρ : Matrix (Fin n) (Fin n) ℂ, IsState ρ → coherenceRel ρ ≤ coherenceL1 ρ

open Matrix
open scoped BigOperators ComplexOrder


private def binaryPinch {n : ℕ} (P ρ : Matrix (Fin n) (Fin n) ℂ) :=
  D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    (fun b : Bool => if b then P else 1-P)
    (fun b : Bool => (if b then P else 1-P)ᴴ) ρ

private def reflection {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) := (2 : ℂ) • P - 1

private theorem reflection_hermitian {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.IsHermitian) : (reflection P).IsHermitian := by
  change ((2 : ℂ) • P - 1)ᴴ = (2 : ℂ) • P - 1
  simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP.eq]

private theorem reflection_unitary {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
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
  have hnonneg : ∀ j : Fin n, 0 ≤ (if k < j then ‖ρ k j‖ else 0) := by
    intro j; split_ifs <;> positivity
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun j : Fin n => if k < j then ‖ρ k j‖ else 0)
    (fun j _ => hnonneg j)
  have hh : (∑ j : Fin n, (if k < j then ‖ρ k j‖ else 0)^2) =
      ∑ j : Fin n, if k < j then ‖ρ k j‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro j _; split_ifs <;> simp
  have hp : 0 ≤ ∑ j : Fin n, if k < j then ‖ρ k j‖ else 0 :=
    Finset.sum_nonneg (fun j _ => hnonneg j)
  simp only [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L1, PiLp.toLp_apply]
  simp only [apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  calc
    _ ≤ Real.sqrt ((∑ j : Fin n, if k < j then ‖ρ k j‖ else 0)^2) := Real.sqrt_le_sqrt (hh ▸ hs)
    _ = _ := Real.sqrt_sq hp

private theorem coherenceL1_eq_twice_upper {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) : coherenceL1 ρ = 2 * ∑ k, ‖WithLp.toLp 1 (fun j : Fin n => if k < j then ρ k j else 0)‖ := by
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
  simp only [coherenceL1, hsplit, Finset.sum_add_distrib, hswap,
    PiLp.norm_eq_of_L1, PiLp.toLp_apply, apply_ite norm, norm_zero]
  ring

private theorem row_bound_le_coherenceL1 {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.IsHermitian) : 2 * (∑ k, ‖WithLp.toLp 2 (fun j : Fin n => if k < j then ρ k j else 0)‖) ≤ coherenceL1 ρ := by
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
    _ ≤ coherenceL1 ρ := row_bound_le_coherenceL1 ρ hρ.1.isHermitian

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
theorem result : claim := claim_of_binaryHolevo D5.S3.Divergence.AudenaertBinaryHolevoBound.binaryHolevoBound

end D5.S3.Divergence.CoherenceL1RelativeEntropyBound
