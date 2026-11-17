/- GID: D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnLimit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubspaceCodes/MRDDensityColumnLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-field MRD density: limit argument. -/
/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments.kernel_frame_moment_limit
question_answered: https://github.com/the-omega-institute/trureturing/issues/26598
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27411
Direct frozen declaration identities (not module pins):
D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_zero_of_lt: sha256:0e125cb16efe1cee78886ce2c6b059bc6a36c38c6740dcddafa53b67a66ba327
D5.S3.Combinatorics.CylindricPartition.LiUncuDefs.gauss: sha256:f926774c1dcfc4f25ac8221be84ee089ae2dae1d643c4699259ccb4d03819006
D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.qbinom: sha256:68e8c0ddbc9607a30b65c1287978f90ef5697b9b7d1e4d398109c2163ca6a5c0
D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.qfact: sha256:4af4fb4b2a9a58c0413510027dc6344acdd7d67dcadcce7fb1396461c01e776f
D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.qnum: sha256:449bd3b087eb7428cc7010dc10aa2e0c53f621f7924580deac57590f61f4d8c1
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue: sha256:5eb9692ec654f291a1d656372d8e03b193e76c908bc1e2ff2eb45a5aa4627037
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_eq_qbinom: sha256:0bf560da58c37f02c1e7b7913db835f73dca4fb983ff22fca277abc2ec264401
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.qfact_pos: sha256:42d505b1b8cc898f522c07e647782dc2de4488f122103b1e5ef0232e7a7fe384
D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_pascal_dual: sha256:732a0e73b6db4590bb33329cc31b58e8818df5c4b5d2a012c5011148f65b049b
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_pascal: sha256:550c63d0efe0003d4bb8674a9a069eb9048fa35a2b2721ea6dfbfd2c1c0d85b0
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_right: sha256:d58867f67d4b21d6518bcad6227443794d8780bb74a241bc42e185889e4f18cb
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_succ: sha256:d4588b9721b518bd3ee79163f6f0bdf7f7335512ac2d76ddce88ef93efe452ce
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.finite_q_binomial_from_gauss: sha256:0d3bf74327a42b8f7f5f39be91816d39ea8ce631d05e24468060a488c7ace4bd
D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_symmetry: sha256:b83baaa08c18e66ee406173ad88427b09c8adef06bb689ecbfd3fb286955acbf
Per-declaration proof_shape; escape_witness; consumers:
MRDDensityTuples.tuple_injection_ratio: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTuples.weighted_frame_moment_limit
MRDDensityTuples.weightedFrameMoment: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityTuples.weighted_frame_moment_limit
MRDDensityTuples.weighted_frame_moment_limit: proof_shape=content; escape_witness=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting.noninjective_map_count; consumers=MRDDensityMoments.kernel_frame_moment_limit
MRDDensityMoments.frame_card_gaussian: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityMoments.kernel_frame_card_gaussian, MRDDensityScalar.normalized_gaussian
MRDDensityMoments.kernelFrameEquiv: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityMoments.kernel_frame_card_gaussian
MRDDensityMoments.kernel_frame_card_gaussian: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityMoments.frame_incidence_product
MRDDensityMoments.frame_incidence_product: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityMoments.kernel_frame_moment_limit
MRDDensityMoments.mapFintype: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityMoments.kernel_frame_moment_limit, blocks_probability
MRDDensityMoments.kernel_frame_moment_limit: proof_shape=content; escape_witness=MRDDensityMoments.kernel_frame_moment_limit; consumers=blocks_probability_limit
generatorTensorEquiv: proof_shape=bind-only; escape_witness=none; consumers=generator_block
generator_block: proof_shape=bind-only; escape_witness=none; consumers=generator_mrd_iff
generator_mrd_iff: proof_shape=bind-only; escape_witness=none; consumers=density_tensor_ratio
injection_ratio_codomain: proof_shape=bind-only; escape_witness=none; consumers=result
density_generator_ratio: proof_shape=bind-only; escape_witness=none; consumers=density_tensor_ratio
density_tensor_ratio: proof_shape=bind-only; escape_witness=none; consumers=density_normalized
MRDDensityJoint.polynomial_moment_limit: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityJoint.joint_zero_limit_of_moments
MRDDensityJoint.average_abs_error: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityJoint.joint_zero_limit_of_moments
MRDDensityJoint.joint_zero_limit_of_moments: proof_shape=content; escape_witness=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius.prod_error; consumers=blocks_probability_limit
MRDDensityScalar.b: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityScalar.a, MRDDensityScalar.normalized_gaussian
MRDDensityScalar.normalized_gaussian: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityScalar.normalized_gaussian_bounds, MRDDensityScalar.normalized_gaussian_limit
MRDDensityScalar.normalized_gaussian_limit: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityScalar.scalar_series_value, MRDDensityScalar.series_summable
MRDDensityScalar.normalized_gaussian_bounds: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityScalar.a_norm_bound
MRDDensityScalar.a: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityScalar.a_norm_bound, MRDDensityScalar.finite_series_product
MRDDensityScalar.c: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityScalar.scalar_series_value, MRDDensityScalar.series_summable
MRDDensityScalar.series_bound: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityScalar.a_norm_bound
MRDDensityScalar.a_norm_bound: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityScalar.scalar_series_value, MRDDensityScalar.series_summable
MRDDensityScalar.series_summable: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityScalar.scalar_partial_limit
MRDDensityScalar.finite_series_product: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityScalar.scalar_series_value
MRDDensityScalar.scalar_series_value: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityScalar.scalar_partial_limit
MRDDensityScalar.scalar_partial_limit: proof_shape=bind-only; escape_witness=none; consumers=blocks_probability_limit
blocks_probability: proof_shape=bind-only; escape_witness=none; consumers=blocks_probability_limit
blocks_probability_limit: proof_shape=content; escape_witness=MRDDensityMoments.kernel_frame_moment_limit; consumers=result
claim: proof_shape=bind-only; escape_witness=none; consumers=result
density_normalized: proof_shape=bind-only; escape_witness=none; consumers=result
result: proof_shape=content; escape_witness=MRDDensityMoments.kernel_frame_moment_limit; consumers=none (settling result)
-/

import D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling
import D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor
import D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
import D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
import D5.S3.Combinatorics.CylindricPartition.LiUncuGaussian
import D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode
import Mathlib.Analysis.Normed.Group.Tannery

open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityCounting
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityMoments
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis
open D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode

set_option maxHeartbeats 500000
set_option maxRecDepth 512
set_option linter.unusedSimpArgs false

open Module Filter
open scoped Classical BigOperators TensorProduct Topology
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples
variable {K E ι : Type*} [Field K] [Fintype K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Fintype ι] [DecidableEq ι]

private theorem tuple_injection_ratio {D : Type*} [AddCommGroup D] [Module K D]
    [FiniteDimensional K D] (k : ι → ℕ) :
    (Nat.card {f : ((Σ i, Fin (k i)) → K) →ₗ[K] D // Function.Injective f} : ℝ) /
      (Nat.card (((Σ i, Fin (k i)) → K) →ₗ[K] D) : ℝ) =
    (Nat.card {f : (Fin (∑ i,k i) → K) →ₗ[K] D // Function.Injective f} : ℝ) /
      (Nat.card ((Fin (∑ i,k i) → K) →ₗ[K] D) : ℝ) := by
  let e : ((Σ i, Fin (k i)) → K) ≃ₗ[K] (Fin (∑ i,k i) → K) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  let a : ((((Σ i, Fin (k i)) → K) →ₗ[K] D)) ≃ₗ[K]
      ((Fin (∑ i,k i) → K) →ₗ[K] D) := e.arrowCongr (LinearEquiv.refl K D)
  have hp (f : ((Σ i, Fin (k i)) → K) →ₗ[K] D) :
      Function.Injective f ↔ Function.Injective (a f) := by
    change Function.Injective f ↔ Function.Injective (f ∘ e.symm)
    exact (e.symm.toEquiv.injective_comp f).symm
  let a' : {f : ((Σ i, Fin (k i)) → K) →ₗ[K] D // Function.Injective f} ≃
      {f : (Fin (∑ i,k i) → K) →ₗ[K] D // Function.Injective f} := Equiv.subtypeEquiv a.toEquiv hp
  rw [Nat.card_congr a', Nat.card_congr a.toEquiv]

private noncomputable def weightedFrameMoment (U : ι → Submodule K E) (r m : ℕ) (k : ι → ℕ) : ℝ :=
  ∑ v ∈ frameTuples (K := K) (D := Fin (r*m) → K) k,
    ((Fintype.card K : ℝ)^(m * finrank K ↥(Finset.univ.sup
      (fun i => D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor.rectangle (U i) (Submodule.span K (Set.range (v i)))))))⁻¹

private theorem weighted_frame_moment_limit
    (U : ι → Submodule K E) (r : ℕ) (hr : 1 ≤ r)
    (hU : ∀ i, finrank K ↥(U i) = r) (hinj : Function.Injective U) (k : ι → ℕ) :
    Tendsto (fun m : ℕ => weightedFrameMoment U r m k) atTop (𝓝 1) := by
  classical
  let a (m : ℕ) : ℝ :=
    (Nat.card {f : ((Σ i, Fin (k i)) → K) →ₗ[K] (Fin (r*m) → K) // Function.Injective f} : ℝ) /
      (Nat.card (((Σ i, Fin (k i)) → K) →ₗ[K] (Fin (r*m) → K)) : ℝ)
  let b (m : ℕ) : ℝ :=
    ∑ v ∈ nondirectTuples (K := K) (D := Fin (r*m) → K) k,
      ((Fintype.card K : ℝ)^(m * finrank K ↥(Finset.univ.sup
        (fun i => D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor.rectangle (U i) (Submodule.span K (Set.range (v i)))))))⁻¹
  have ha : Tendsto a atTop (𝓝 1) := by
    have heq (m : ℕ) : a m =
        (Nat.card {f : (Fin (∑ i,k i) → K) →ₗ[K] (Fin (m*r) → K) // Function.Injective f} : ℝ) /
          (Nat.card ((Fin (∑ i,k i) → K) →ₗ[K] (Fin (m*r) → K)) : ℝ) := by
      dsimp only [a]
      rw [tuple_injection_ratio,Nat.mul_comm r m]
    exact (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting.fixed_source_injection_limit (K := K) (∑ i,k i) r hr).congr'
      (Eventually.of_forall (fun m => (heq m).symm))
  have hb0 : ∀ m, 0 ≤ b m := by
    intro m
    exact Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))
  have hb : ∀ m, b m ≤
      (∑ s ∈ Finset.range (∑ i,k i), (Fintype.card K : ℝ)^(s*(∑ i,k i))) *
        ((Fintype.card K : ℝ)^m)⁻¹ := by
    intro m
    exact nondirect_tensor_weight_sum U r m hU hinj (by simp) k
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hblim : Tendsto b atTop (𝓝 0) :=
    D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.vanishing_nondirect _ hq _ b
      (Eventually.of_forall hb0) (Eventually.of_forall hb)
  have hid (m : ℕ) : weightedFrameMoment U r m k = a m+b m := by
    exact frame_weight_decomposition U r m hU (by simp) k
  simpa only [hid, add_zero] using ha.add hblim

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples
open Module Filter
open scoped BigOperators TensorProduct Topology
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments
variable {K D F : Type*} [Field K] [Fintype K]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D] [Fintype D]
  [AddCommGroup F] [Module K F]

private theorem frame_card_gaussian (k : ℕ) :
    (Nat.card {v : Fin k → D // LinearIndependent K v} : ℝ) =
      gaussValue (Fintype.card K : ℝ) (finrank K D) k *
        D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct (Fintype.card K) k := by
  classical
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card (α := K)
  by_cases hk : k ≤ finrank K D
  · rw [← Nat.card_congr (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting.injectionFrameEquiv (K := K) (E := D) k),
      D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel.real_injection_count k hk,
      ← D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.gaussian_eq_polynomial _ _ _ hq hk]
    unfold D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.gaussian D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct
    rw [Finset.prod_div_distrib]
    have ha : (∏ h ∈ Finset.range k,
        ((Fintype.card K : ℝ)^k-(Fintype.card K : ℝ)^h)) ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le (by positivity)
        (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphism_product_lower (Fintype.card K) (by exact_mod_cast hq) k))
    exact (div_mul_cancel₀ _ ha).symm
  · haveI : IsEmpty {v : Fin k → D // LinearIndependent K v} := ⟨by
      rintro ⟨v,hv⟩
      have h : k ≤ finrank K D := by simpa only [Fintype.card_fin] using hv.fintype_card_le_finrank
      exact hk h⟩
    have hg : gaussValue (Fintype.card K : ℝ) (finrank K D) k = 0 := by
      simp [gaussValue,
        D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_zero_of_lt _ _ (Nat.lt_of_not_ge hk)]
    simp [hg, Nat.card_eq_fintype_card]

private noncomputable def kernelFrameEquiv (f : D →ₗ[K] F) (k : ℕ) :
    {v : Fin k → D // LinearIndependent K v ∧ ∀ j, f (v j) = 0} ≃
      {v : Fin k → LinearMap.ker f // LinearIndependent K v} where
  toFun v := ⟨fun j => ⟨v.val j,v.property.2 j⟩,
    v.property.1.codRestrict (LinearMap.ker f) (fun j => v.property.2 j)⟩
  invFun v := ⟨fun j => (v.val j : D),
    v.property.map' (LinearMap.ker f).subtype (LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _)),
    fun j => (v.val j).property⟩
  left_inv v := by rfl
  right_inv v := by rfl

private theorem kernel_frame_card_gaussian (f : D →ₗ[K] F) (k : ℕ) :
    (Nat.card {v : Fin k → D // LinearIndependent K v ∧ ∀ j, f (v j) = 0} : ℝ) =
      gaussValue (Fintype.card K : ℝ) (finrank K ↥(LinearMap.ker f)) k *
        D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct (Fintype.card K) k := by
  classical
  rw [Nat.card_congr (kernelFrameEquiv f k)]
  exact frame_card_gaussian k

section Incidence
variable {E ι : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Fintype ι] [DecidableEq ι]
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples

private theorem frame_incidence_product (U : ι → Submodule K E)
    (g : (E ⊗[K] D) →ₗ[K] F) (k : ι → ℕ) :
    (∑ v ∈ frameTuples (K := K) (D := D) k,
      (if ∀ i j, blockMap g (U i) (v i j) = 0 then (1 : ℝ) else 0)) =
    ∏ i, gaussValue (Fintype.card K : ℝ)
      (finrank K ↥(LinearMap.ker (blockMap g (U i)))) (k i) *
        D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct (Fintype.card K) (k i) := by
  classical
  let A := {v : ∀ i, Fin (k i) → D //
    (∀ i, LinearIndependent K (v i)) ∧ ∀ i j, blockMap g (U i) (v i j) = 0}
  let B := ∀ i, {v : Fin (k i) → D //
    LinearIndependent K v ∧ ∀ j, blockMap g (U i) (v j) = 0}
  let e : A ≃ B :=
    {toFun := fun v i => ⟨v.val i,v.property.1 i,v.property.2 i⟩
     invFun := fun v => ⟨fun i => (v i).val,fun i => (v i).property.1,
       fun i => (v i).property.2⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}
  have hc : (∑ v ∈ frameTuples (K := K) (D := D) k,
      (if ∀ i j, blockMap g (U i) (v i j) = 0 then (1 : ℝ) else 0)) = (Nat.card A : ℝ) := by
    simp only [frameTuples, Finset.sum_filter,
      Nat.card_eq_fintype_card, Fintype.card_subtype, A,
      Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    split_ifs <;> simp_all
  rw [hc, Nat.card_congr e]
  simp only [B, Nat.card_eq_fintype_card, Fintype.card_pi, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [Nat.card_eq_fintype_card] using kernel_frame_card_gaussian (blockMap g (U i)) (k i)
end Incidence

section Limit
variable {E ι : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Fintype ι] [DecidableEq ι]
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTuples

private noncomputable instance mapFintype (r m : ℕ) :
    Fintype ((E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K)) := by
  letI : Finite ((E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K)) := Cardinal.lt_aleph0_iff_finite.mp (_root_.cardinal_lt_aleph0_of_finiteDimensional K _)
  exact Fintype.ofFinite _

private theorem kernel_frame_moment_limit (U : ι → Submodule K E) (r : ℕ) (hr : 1 ≤ r)
    (hU : ∀ i, finrank K ↥(U i) = r) (hinj : Function.Injective U) (k : ι → ℕ) :
    Tendsto (fun m : ℕ =>
      (∑ g : (E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K),
        ∏ i, gaussValue (Fintype.card K : ℝ)
          (finrank K ↥(LinearMap.ker (blockMap g (U i)))) (k i)) /
      (Nat.card ((E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K)) : ℝ))
      atTop (𝓝 (∏ i, (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct (Fintype.card K) (k i))⁻¹)) := by
  classical
  let C : ℝ := ∏ i, D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct (Fintype.card K) (k i)
  have hq : (2 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hC : C ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact ne_of_gt (lt_of_lt_of_le (by positivity)
      (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphism_product_lower _ hq (k i)))
  have hid (m : ℕ) : weightedFrameMoment U r m k =
      ((∑ g : (E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K),
        ∏ i, gaussValue (Fintype.card K : ℝ)
          (finrank K ↥(LinearMap.ker (blockMap g (U i)))) (k i)) /
      (Nat.card ((E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K)) : ℝ)) * C := by
    unfold weightedFrameMoment
    rw [← frame_incidence_average m U k]
    simp_rw [frame_incidence_product,Finset.prod_mul_distrib]
    rw [← Finset.sum_mul]
    simp only [C]
    ring
  have ht := (weighted_frame_moment_limit U r hr hU hinj k).div_const C
  have heq (m : ℕ) : weightedFrameMoment U r m k / C =
      (∑ g : (E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K),
        ∏ i, gaussValue (Fintype.card K : ℝ)
          (finrank K ↥(LinearMap.ker (blockMap g (U i)))) (k i)) /
      (Nat.card ((E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K)) : ℝ) := by
    rw [hid, mul_div_cancel_right₀ _ hC]
  have ht' := ht.congr' (Eventually.of_forall heq)
  simpa only [one_div,C,Finset.prod_inv_distrib] using ht'
end Limit

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments
open Module Filter
open scoped BigOperators TensorProduct Topology
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit
variable {K D : Type*} [Field K] [Fintype K] [AddCommGroup D] [Module K D]

private noncomputable def generatorTensorEquiv (n m : ℕ) :
    (D →ₗ[K] Matrix (Fin n) (Fin m) K) ≃ₗ[K] ((Fin n → K) ⊗[K] D) →ₗ[K] (Fin m → K) :=
  (LinearEquiv.congrRight
    ((Matrix.transposeLinearEquiv (Fin n) (Fin m) K K).trans Matrix.toLin')).trans
      ((LinearMap.lflip).trans
        (TensorProduct.lift.equiv (RingHom.id K) (Fin n → K) D (Fin m → K)))

private theorem generator_block (n m : ℕ) (f : D →ₗ[K] Matrix (Fin n) (Fin m) K)
    (U : Submodule K (Fin n → K)) :
    D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor.blockMap (generatorTensorEquiv n m f) U = (restrictRows n m U).comp f := by
  exact LinearMap.ext_iff₂.mpr fun m_1 => congrFun rfl

private theorem generator_mrd_iff (n m d : ℕ) (hd0 : 1 ≤ d) (hd : d ≤ n)
    (f : D →ₗ[K] Matrix (Fin n) (Fin m) K) :
    (Function.Injective f ∧ MinDistanceAtLeast K n m d (LinearMap.range f)) ↔
      ∀ U : Submodule K (Fin n → K), finrank K U = n-d+1 →
        Function.Injective (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor.blockMap (generatorTensorEquiv n m f) U) := by
  simp_rw [generator_block]
  constructor
  · rintro ⟨hf,hm⟩
    exact (mrd_iff_restrictions_injective n m d hd f hf).mp hm
  · intro h
    obtain ⟨U,hUr,hU⟩ := subspace_of_dimension_le (⊤ : Submodule K (Fin n → K)) (n-d+1)
      (by simp only [finrank_top, finrank_fintype_fun_eq_card, Fintype.card_fin]; omega)
    have hf : Function.Injective f := by
      intro x y hxy
      apply h U hUr
      change restrictRows n m U (f x) = restrictRows n m U (f y)
      exact congrArg (restrictRows n m U) hxy
    exact ⟨hf,(mrd_iff_restrictions_injective n m d hd f hf).mpr h⟩

private theorem injection_ratio_codomain {V X Y : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] (e : X ≃ₗ[K] Y) :
    (Nat.card {f : V →ₗ[K] X // Function.Injective f} : ℝ) / (Nat.card (V →ₗ[K] X) : ℝ) =
      (Nat.card {f : V →ₗ[K] Y // Function.Injective f} : ℝ) / (Nat.card (V →ₗ[K] Y) : ℝ) := by
  let a : (V →ₗ[K] X) ≃ₗ[K] (V →ₗ[K] Y) := LinearEquiv.congrRight e
  have hp (f : V →ₗ[K] X) : Function.Injective f ↔ Function.Injective (a f) := by
    change Function.Injective f ↔ Function.Injective (e ∘ f)
    constructor
    · intro hf
      exact e.injective.comp hf
    · intro hf
      exact hf.of_comp
  let e' : {f : V →ₗ[K] X // Function.Injective f} ≃
      {f : V →ₗ[K] Y // Function.Injective f} := Equiv.subtypeEquiv a.toEquiv hp
  rw [Nat.card_congr e', Nat.card_congr a.toEquiv]

private theorem density_generator_ratio (n m k d : ℕ) :
    density K n m k d =
      (Nat.card {f : (Fin k → K) →ₗ[K] Matrix (Fin n) (Fin m) K //
        Function.Injective f ∧ MinDistanceAtLeast K n m d (LinearMap.range f)} : ℝ) /
      (Nat.card {f : (Fin k → K) →ₗ[K] Matrix (Fin n) (Fin m) K // Function.Injective f} : ℝ) := by
  let X := Matrix (Fin n) (Fin m) K
  let V := Fin k → K
  let eM : {f : {f : V →ₗ[K] X // Function.Injective f} //
      MinDistanceAtLeast K n m d (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel.imageCode f).val} ≃
      {f : V →ₗ[K] X // Function.Injective f ∧ MinDistanceAtLeast K n m d (LinearMap.range f)} :=
    {toFun := fun f => ⟨f.val.val,f.val.property,f.property⟩
     invFun := fun f => ⟨⟨f.val,f.property.1⟩,f.property.2⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}
  let eA : {U : Submodule K X // finrank K U = finrank K V} ≃ AllCodes K n m k :=
    {toFun := fun U => ⟨U.val,by simpa [V] using U.property⟩
     invFun := fun U => ⟨U.val,by simpa [V] using U.property⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}
  let eG : {U : {U : Submodule K X // finrank K U = finrank K V} // MinDistanceAtLeast K n m d U.val} ≃
      GoodCodes K n m k d :=
    {toFun := fun U => ⟨U.val.val,by simpa [V] using U.val.property,U.property⟩
     invFun := fun U => ⟨⟨U.val,by simpa [V] using U.property.1⟩,U.property.2⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}
  have h := D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel.uniform_image_ratio (K := K) (D := V) (E := X)
    (fun U => MinDistanceAtLeast K n m d U.val)
  rw [Nat.card_congr eM,Nat.card_congr eG,Nat.card_congr eA] at h
  exact h.symm

private theorem density_tensor_ratio (n m k d : ℕ) (hd0 : 1 ≤ d) (hd : d ≤ n) :
    density K n m k d =
      (Nat.card {g : ((Fin n → K) ⊗[K] (Fin k → K)) →ₗ[K] (Fin m → K) //
        ∀ U : Submodule K (Fin n → K), finrank K U = n-d+1 →
          Function.Injective (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor.blockMap g U)} : ℝ) /
      (Nat.card {f : (Fin k → K) →ₗ[K] Matrix (Fin n) (Fin m) K // Function.Injective f} : ℝ) := by
  rw [density_generator_ratio]
  congr 1
  let e : {f : (Fin k → K) →ₗ[K] Matrix (Fin n) (Fin m) K //
      Function.Injective f ∧ MinDistanceAtLeast K n m d (LinearMap.range f)} ≃
      {g : ((Fin n → K) ⊗[K] (Fin k → K)) →ₗ[K] (Fin m → K) //
        ∀ U : Submodule K (Fin n → K), finrank K U = n-d+1 →
          Function.Injective (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor.blockMap g U)} :=
    Equiv.subtypeEquiv (generatorTensorEquiv (K := K) (D := Fin k → K) n m).toEquiv
      (fun f => generator_mrd_iff n m d hd0 hd f)
  exact_mod_cast Nat.card_congr e

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit
open Module Filter Finset
open scoped BigOperators Topology
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityJoint
private theorem polynomial_moment_limit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ω : ℕ → Type*) [∀ m, Fintype (Ω m)]
    (q : ℝ) (ν : ∀ m, Ω m → ι → ℕ)
    (hM : ∀ k : ι → ℕ, Tendsto (fun m =>
      Finset.univ.expect (fun ω : Ω m => ∏ i, gaussValue q (ν m ω i) (k i))) atTop
        (𝓝 (∏ i, (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct q (k i))⁻¹)))
    (J : ι → Type*) [∀ i, Fintype (J i)]
    (a : ∀ i, J i → ℝ) (degree : ∀ i, J i → ℕ) :
    Tendsto (fun m => Finset.univ.expect (fun ω : Ω m =>
      ∏ i, ∑ j, a i j * gaussValue q (ν m ω i) (degree i j))) atTop
      (𝓝 (∏ i, ∑ j, a i j * (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct q (degree i j))⁻¹)) := by
  classical
  have hexpand (m : ℕ) :
      Finset.univ.expect (fun ω : Ω m => ∏ i, ∑ j, a i j * gaussValue q (ν m ω i) (degree i j)) =
      ∑ k : ∀ i, J i, (∏ i,a i (k i)) *
        Finset.univ.expect (fun ω : Ω m => ∏ i, gaussValue q (ν m ω i) (degree i (k i))) := by
    simp_rw [Fintype.expect_eq_sum_div_card]
    simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib]
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.mul_sum, mul_div_assoc]
  have ht : Tendsto (fun m => ∑ k : ∀ i,J i, (∏ i,a i (k i)) *
      Finset.univ.expect (fun ω : Ω m => ∏ i, gaussValue q (ν m ω i) (degree i (k i)))) atTop
      (𝓝 (∑ k : ∀ i,J i, (∏ i,a i (k i)) *
        (∏ i,(D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct q (degree i (k i)))⁻¹))) := by
    apply tendsto_finset_sum
    intro k hk
    exact (hM (fun i => degree i (k i))).const_mul _
  have hlim : (∑ k : ∀ i,J i, (∏ i,a i (k i)) *
      (∏ i,(D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct q (degree i (k i)))⁻¹)) =
      ∏ i, ∑ j, a i j * (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct q (degree i j))⁻¹ := by
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i j => a i j *
      (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct q (degree i j))⁻¹)).symm
  simpa only [hexpand,hlim] using ht

private theorem average_abs_error {Ω : Type*} [Fintype Ω]
    (a b e : Ω → ℝ) (h : ∀ ω, |a ω-b ω| ≤ e ω) :
    |Finset.univ.expect a-Finset.univ.expect b| ≤ Finset.univ.expect e := by
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card Ω from Nat.cast_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ω hω => h ω))

private theorem joint_zero_limit_of_moments
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ω : ℕ → Type*) [∀ m, Fintype (Ω m)] [∀ m, Nonempty (Ω m)]
    (q P : ℝ) (hq : 2 ≤ q) (ν : ∀ m, Ω m → ι → ℕ)
    (hM : ∀ k : ι → ℕ, Tendsto (fun m =>
      Finset.univ.expect (fun ω : Ω m => ∏ i, gaussValue q (ν m ω i) (k i))) atTop
        (𝓝 (∏ i, (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct q (k i))⁻¹)))
    (hscalar : Tendsto (fun R : ℕ => ∑ k : Fin (R+1),
      (-1 : ℝ)^(k.val) * q^(k.val.choose 2) *
        (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct q k.val)⁻¹) atTop (𝓝 P)) :
    Tendsto (fun m => Finset.univ.expect (fun ω : Ω m =>
      ∏ i, if ν m ω i = 0 then (1 : ℝ) else 0)) atTop (𝓝 (P^(Fintype.card ι))) := by
  classical
  let A (R m : ℕ) := Finset.univ.expect (fun ω : Ω m =>
    ∏ i, ∑ k : Fin (R+1), (-1 : ℝ)^k.val * q^(k.val.choose 2) *
      gaussValue q (ν m ω i) k.val)
  let B (R m : ℕ) := Finset.univ.expect (fun ω : Ω m =>
    (∏ i, (1 + q^((R+1).choose 2) * gaussValue q (ν m ω i) (R+1))) - 1)
  let c (R : ℕ) := (∑ k : Fin (R+1), (-1 : ℝ)^k.val * q^(k.val.choose 2) *
    (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct q k.val)⁻¹)^(Fintype.card ι)
  let e (R : ℕ) := (1 + q^((R+1).choose 2) /
    D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct q (R+1))^(Fintype.card ι)-1
  apply D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.approximating_limits _ A B c e _
  · intro R
    apply Eventually.of_forall
    intro m
    rw [abs_sub_comm]
    apply average_abs_error
    intro ω
    simpa only [← Fin.sum_univ_eq_sum_range] using
      D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius.mixed_mobius_error Finset.univ q (by linarith) (ν m ω) R
  · intro R
    have h := polynomial_moment_limit Ω q ν hM (fun _ : ι => Fin (R+1))
      (fun _ k => (-1 : ℝ)^k.val * q^(k.val.choose 2)) (fun _ k => k.val)
    simpa only [A,c,Finset.prod_const,Finset.card_univ] using h
  · intro R
    have h := polynomial_moment_limit Ω q ν hM (fun _ : ι => Bool)
      (fun _ j => if j then q^((R+1).choose 2) else 1)
      (fun _ j => if j then R+1 else 0)
    have hs := h.sub_const 1
    simpa [B,e,D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_right,
      D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.automorphismProduct,Finset.expect_sub_distrib,Fintype.expect_const,div_eq_mul_inv,
      add_comm] using hs
  · exact hscalar.pow _
  · have h := ((D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis.mobius_tail_limit q hq).const_add 1).pow (Fintype.card ι)
    simpa only [add_zero,one_pow,sub_self] using h.sub_const 1

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityJoint
open Module Filter Finset
open scoped BigOperators Topology
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityJoint
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityScalar
variable {K : Type*} [Field K] [Fintype K]
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting

private noncomputable def b (m k : ℕ) : ℝ := gaussValue (Fintype.card K : ℝ) m k / (Fintype.card K : ℝ)^(m*k)

private theorem normalized_gaussian (m k : ℕ) (hk : k ≤ m) :
    b (K := K) m k =
      ((Nat.card {f : (Fin k → K) →ₗ[K] (Fin m → K) // Function.Injective f} : ℝ) /
        (Nat.card ((Fin k → K) →ₗ[K] (Fin m → K)) : ℝ)) /
      automorphismProduct (Fintype.card K) k := by
  have hq : (2 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have ha : automorphismProduct (Fintype.card K) k ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by positivity) (automorphism_product_lower _ hq k))
  have hc := D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments.frame_card_gaussian (K := K) (D := Fin m → K) k
  rw [← Nat.card_congr (injectionFrameEquiv (K := K) (E := Fin m → K) k)] at hc
  simp only [finrank_fintype_fun_eq_card,Fintype.card_fin] at hc
  have hd : (Nat.card ((Fin k → K) →ₗ[K] (Fin m → K)) : ℝ) =
      (Fintype.card K : ℝ)^(m*k) := by
    rw [Module.natCard_eq_pow_finrank (K := K),Nat.card_eq_fintype_card,Nat.cast_pow,
      Module.finrank_linearMap,finrank_fintype_fun_eq_card,finrank_fintype_fun_eq_card,
      Fintype.card_fin,Fintype.card_fin,Nat.mul_comm]
  rw [hc,hd]
  unfold b
  field_simp

private theorem normalized_gaussian_limit (k : ℕ) :
    Tendsto (fun m => b (K := K) m k) atTop
      (𝓝 (automorphismProduct (Fintype.card K) k)⁻¹) := by
  let f (m : ℕ) : ℝ :=
    (Nat.card {g : (Fin k → K) →ₗ[K] (Fin m → K) // Function.Injective g} : ℝ) /
      (Nat.card ((Fin k → K) →ₗ[K] (Fin m → K)) : ℝ)
  have hf : Tendsto f atTop (𝓝 1) := by
    convert fixed_source_injection_limit (K := K) k 1 (by omega) using 1
    funext m
    dsimp only [f]
    rw [Nat.mul_one m]
  have h : Tendsto (fun m => f m / automorphismProduct (Fintype.card K) k) atTop
      (𝓝 (automorphismProduct (Fintype.card K) k)⁻¹) := by
    simpa only [one_div] using hf.div_const (automorphismProduct (Fintype.card K) k)
  have heq : (fun m => f m / automorphismProduct (Fintype.card K) k) =ᶠ[atTop]
      (fun m => b (K := K) m k) := by
    filter_upwards [eventually_ge_atTop k] with m hm
    exact (normalized_gaussian (K := K) m k hm).symm
  exact (tendsto_congr' heq).mp h

private theorem normalized_gaussian_bounds (m k : ℕ) :
    0 ≤ b (K := K) m k ∧ b (K := K) m k ≤ (automorphismProduct (Fintype.card K) k)⁻¹ := by
  classical
  have hq : (2 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have ha : 0 < automorphismProduct (Fintype.card K) k :=
    lt_of_lt_of_le (by positivity) (automorphism_product_lower _ hq k)
  by_cases hk : k ≤ m
  · rw [normalized_gaussian m k hk]
    have hp : 0 ≤ (Nat.card {f : (Fin k → K) →ₗ[K] (Fin m → K) // Function.Injective f} : ℝ) /
        (Nat.card ((Fin k → K) →ₗ[K] (Fin m → K)) : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hle : (Nat.card {f : (Fin k → K) →ₗ[K] (Fin m → K) // Function.Injective f} : ℝ) ≤
        (Nat.card ((Fin k → K) →ₗ[K] (Fin m → K)) : ℝ) := by
      letI : Finite ((Fin k → K) →ₗ[K] (Fin m → K)) := Cardinal.lt_aleph0_iff_finite.mp (_root_.cardinal_lt_aleph0_of_finiteDimensional K _)
      letI := Fintype.ofFinite ((Fin k → K) →ₗ[K] (Fin m → K))
      simp only [Nat.card_eq_fintype_card]
      exact_mod_cast Fintype.card_subtype_le (fun f : (Fin k → K) →ₗ[K] (Fin m → K) => Function.Injective f)
    have hratio : (Nat.card {f : (Fin k → K) →ₗ[K] (Fin m → K) // Function.Injective f} : ℝ) /
        (Nat.card ((Fin k → K) →ₗ[K] (Fin m → K)) : ℝ) ≤ 1 :=
      (div_le_one₀ (by
        rw [Module.natCard_eq_pow_finrank (K := K),Nat.card_eq_fintype_card,Nat.cast_pow]
        positivity)).mpr hle
    exact ⟨div_nonneg hp ha.le, (div_le_div_of_nonneg_right hratio ha.le).trans_eq (one_div _)⟩
  · have hg : gaussValue (Fintype.card K : ℝ) m k = 0 := by
      simp [gaussValue,D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_zero_of_lt m k (by omega)]
    simp [b,hg,ha.le]

private noncomputable def a (m k : ℕ) : ℝ := (-1 : ℝ)^k * (Fintype.card K : ℝ)^k.choose 2 * b (K := K) m k
private noncomputable def c (k : ℕ) : ℝ := (-1 : ℝ)^k * (Fintype.card K : ℝ)^k.choose 2 /
  automorphismProduct (Fintype.card K) k

private theorem series_bound (k : ℕ) :
    (Fintype.card K : ℝ)^k.choose 2 / automorphismProduct (Fintype.card K) k ≤
      (Fintype.card K : ℝ) * ((Fintype.card K : ℝ)⁻¹)^k := by
  have hq : (2 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hq0 : (0 : ℝ) < Fintype.card K := by linarith
  cases k with
  | zero =>
    simpa only [automorphismProduct,Finset.range_zero,Finset.prod_empty,
      Nat.choose_zero_succ,Nat.choose_zero_right,pow_zero,div_one,mul_one] using (show (1 : ℝ) ≤ Fintype.card K by linarith)
  | succ k =>
    have h := (mobius_tail_bound (Fintype.card K) hq k).2
    calc
      _ ≤ ((Fintype.card K : ℝ)^k)⁻¹ := h
      _ = (Fintype.card K : ℝ) * ((Fintype.card K : ℝ)⁻¹)^(k+1) := by
        rw [pow_succ,inv_pow]
        field_simp

private theorem a_norm_bound (m k : ℕ) : ‖a (K := K) m k‖ ≤
    (Fintype.card K : ℝ) * ((Fintype.card K : ℝ)⁻¹)^k := by
  have hb := normalized_gaussian_bounds (K := K) m k
  calc
    ‖a (K := K) m k‖ = (Fintype.card K : ℝ)^k.choose 2 * b (K := K) m k := by
      simp [a,Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card K from Nat.cast_nonneg _),abs_of_nonneg hb.1]
    _ ≤ (Fintype.card K : ℝ)^k.choose 2 / automorphismProduct (Fintype.card K) k := by
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hb.2 (pow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := series_bound k

private theorem series_summable : Summable (c (K := K)) := by
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hs := (summable_geometric_of_lt_one (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ Fintype.card K))
    (inv_lt_one_of_one_lt₀ hq)).mul_left (Fintype.card K : ℝ)
  apply hs.of_norm_bounded
  intro k
  have ha : Tendsto (fun m => a (K := K) m k) atTop (𝓝 (c (K := K) k)) := by
    simpa only [a,c,div_eq_mul_inv] using (normalized_gaussian_limit (K := K) k).const_mul
      ((-1 : ℝ)^k*(Fintype.card K : ℝ)^k.choose 2)
  exact le_of_tendsto ha.norm (Eventually.of_forall fun m => a_norm_bound m k)

private theorem finite_series_product (m : ℕ) :
    (∑' k, a (K := K) m k) =
      ∏ j ∈ range m, (1 - (Fintype.card K : ℝ)⁻¹^(j+1)) := by
  have hq : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := K)
  have ht : (∑' k, a (K := K) m k) = ∑ k ∈ range (m+1), a (K := K) m k := by
    apply tsum_eq_sum
    intro k hk
    have hmk : m < k := by
      have h : m+1 ≤ k := by simpa only [mem_range,not_lt] using hk
      omega
    simp [a,b,gaussValue,D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_zero_of_lt m k hmk]
  rw [ht]
  have hbin : (∏ j ∈ range m, (1 + (-(Fintype.card K : ℝ)^m)⁻¹ * (Fintype.card K : ℝ)^j)) =
      ∑ k ∈ range (m+1), (Fintype.card K : ℝ)^k.choose 2 * gaussValue (Fintype.card K : ℝ) m k *
        ((-(Fintype.card K : ℝ)^m)⁻¹)^k := by
    apply D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.finite_q_binomial_from_gauss
  have hs : (∑ k ∈ range (m+1), a (K := K) m k) =
      ∑ k ∈ range (m+1), (Fintype.card K : ℝ)^k.choose 2 * gaussValue (Fintype.card K : ℝ) m k *
        ((-(Fintype.card K : ℝ)^m)⁻¹)^k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hz : ((-(Fintype.card K : ℝ)^m)⁻¹)^k =
        (-1 : ℝ)^k * ((Fintype.card K : ℝ)^(m*k))⁻¹ := by
      rw [inv_neg,neg_pow ((Fintype.card K : ℝ)^m)⁻¹ k,← inv_pow,← pow_mul]
      simp only [inv_pow]
    dsimp only [a,b]
    rw [hz]
    ring
  rw [hs,← hbin,← prod_range_reflect (fun j => 1 + (-(Fintype.card K : ℝ)^m)⁻¹ * (Fintype.card K : ℝ)^j) m]
  apply prod_congr rfl
  intro j hj
  have hjm : m-1-j+(j+1)=m := by have := mem_range.mp hj; omega
  rw [inv_neg,neg_mul,← sub_eq_add_neg]
  congr 1
  have hp : (Fintype.card K : ℝ)^m = (Fintype.card K : ℝ)^(m-1-j) * (Fintype.card K : ℝ)^(j+1) := by rw [← pow_add,hjm]
  rw [hp,mul_inv,inv_pow]
  field_simp

private theorem scalar_series_value : (∑' k, c (K := K) k) = P (Fintype.card K) := by
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hs := (summable_geometric_of_lt_one (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ Fintype.card K))
    (inv_lt_one_of_one_lt₀ hq)).mul_left (Fintype.card K : ℝ)
  have hlim := tendsto_tsum_of_dominated_convergence hs
    (fun k => (by simpa only [a,c,div_eq_mul_inv] using
      (normalized_gaussian_limit (K := K) k).const_mul ((-1 : ℝ)^k*(Fintype.card K : ℝ)^k.choose 2)))
    (Eventually.of_forall fun m k => a_norm_bound (K := K) m k)
  simp_rw [finite_series_product] at hlim
  exact tendsto_nhds_unique hlim (product_limit _ (Fintype.one_lt_card (α := K)))

private theorem scalar_partial_limit :
    Tendsto (fun R : ℕ => ∑ k : Fin (R+1), (-1 : ℝ)^k.val * (Fintype.card K : ℝ)^k.val.choose 2 *
      (automorphismProduct (Fintype.card K) k.val)⁻¹) atTop (𝓝 (P (Fintype.card K))) := by
  have h := (series_summable (K := K)).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  rw [scalar_series_value] at h
  change Tendsto (fun R : ℕ => ∑ k ∈ range (R+1), c (K := K) k) atTop (𝓝 (P (Fintype.card K))) at h
  simpa only [← Fin.sum_univ_eq_sum_range,c,div_eq_mul_inv] using h

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityScalar
open Module Filter Finset
open scoped BigOperators TensorProduct Topology
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityJoint
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityScalar
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityMoments D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityJoint
variable {K E ι : Type*} [Field K] [Fintype K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Fintype ι] [DecidableEq ι]

private theorem blocks_probability (U : ι → Submodule K E) (r m : ℕ) :
    Finset.univ.expect (fun g : (E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K) =>
      ∏ i, if finrank K ↥(LinearMap.ker (blockMap g (U i))) = 0 then (1 : ℝ) else 0) =
    (Nat.card {g : (E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K) //
      ∀ i, Function.Injective (blockMap g (U i))} : ℝ) /
    (Nat.card ((E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K)) : ℝ) := by
  classical
  simp_rw [Fintype.expect_eq_sum_div_card]
  simp only [Nat.card_eq_fintype_card]
  congr 1
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_eq_sum_ones,
    Nat.cast_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g hg
  have hi (i : ι) : finrank K ↥(LinearMap.ker (blockMap g (U i))) = 0 ↔
      Function.Injective (blockMap g (U i)) := by
    rw [Submodule.finrank_eq_zero,LinearMap.ker_eq_bot]
  simp_rw [hi]
  by_cases h : ∀ i, Function.Injective (blockMap g (U i))
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [h]

private theorem blocks_probability_limit (U : ι → Submodule K E) (r : ℕ) (hr : 1 ≤ r)
    (hU : ∀ i, finrank K ↥(U i) = r) (hinj : Function.Injective U) :
    Tendsto (fun m =>
      (Nat.card {g : (E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K) //
        ∀ i, Function.Injective (blockMap g (U i))} : ℝ) /
      (Nat.card ((E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K)) : ℝ))
      atTop (𝓝 ((P (Fintype.card K))^(Fintype.card ι))) := by
  have h := joint_zero_limit_of_moments
    (fun m => (E ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K))
    (Fintype.card K) (P (Fintype.card K))
    (by exact_mod_cast Fintype.one_lt_card (α := K))
    (fun m g i => finrank K ↥(LinearMap.ker (blockMap g (U i))))
    (fun k => by
      simpa only [Fintype.expect_eq_sum_div_card,Nat.card_eq_fintype_card] using kernel_frame_moment_limit U r hr hU hinj k)
    (D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityScalar.scalar_partial_limit (K := K))
  simpa only [blocks_probability] using h

def claim : Prop :=
  ∀ (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽]
    (n d : ℕ),
    2 ≤ n → 1 ≤ d → d ≤ n →
    Tendsto
      (fun m : ℕ => density 𝔽 n m (mrdDimension n m d) d)
      atTop
      (𝓝 (if d = 1 then 1 else P (Fintype.card 𝔽) ^ gaussian (Fintype.card 𝔽) n (d - 1)))


section ExactTarget
variable (K)
private theorem density_normalized (n d r m : ℕ) (hr : r = n-d+1) (hd0 : 1 ≤ d) (hd : d ≤ n) :
    density K n m (r*m) d =
      ((Nat.card {g : ((Fin n → K) ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K) //
        ∀ U : {U : Submodule K (Fin n → K) // finrank K U = r},
          Function.Injective (blockMap g U.val)} : ℝ) /
        (Nat.card (((Fin n → K) ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K)) : ℝ)) /
      ((Nat.card {f : (Fin (r*m) → K) →ₗ[K] Matrix (Fin n) (Fin m) K // Function.Injective f} : ℝ) /
        (Nat.card ((Fin (r*m) → K) →ₗ[K] Matrix (Fin n) (Fin m) K) : ℝ)) := by
  rw [density_tensor_ratio n m (r*m) d hd0 hd]
  have hevent : {g : ((Fin n → K) ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K) //
      ∀ U : Submodule K (Fin n → K), finrank K U = n-d+1 → Function.Injective (blockMap g U)} ≃
      {g : ((Fin n → K) ⊗[K] (Fin (r*m) → K)) →ₗ[K] (Fin m → K) //
        ∀ U : {U : Submodule K (Fin n → K) // finrank K U = r}, Function.Injective (blockMap g U.val)} :=
    Equiv.subtypeEquivRight (fun g => by simp only [hr,Subtype.forall])
  rw [Nat.card_congr hevent]
  have hc := Nat.card_congr (generatorTensorEquiv (K := K) (D := Fin (r*m) → K) n m).toEquiv
  have hp : (Nat.card ((Fin (r*m) → K) →ₗ[K] Matrix (Fin n) (Fin m) K) : ℝ) ≠ 0 := by
    rw [Module.natCard_eq_pow_finrank (K := K),Nat.card_eq_fintype_card,Nat.cast_pow]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [← hc]
  exact (div_div_div_cancel_right₀ hp _ _).symm

theorem result : claim := by
  intro K instK instKF n d hn hd0 hd
  by_cases hd1 : d = 1
  · subst d
    simpa using limit_one (𝔽 := K) n (by omega)
  · let r := n-d+1
    have hr : 1 ≤ r := by exact Nat.le_add_left 1 (n - d)
    have hrn : r < n := by dsimp [r]; omega
    let I := {U : Submodule K (Fin n → K) // finrank K U = r}
    let U : I → Submodule K (Fin n → K) := Subtype.val
    have hU : ∀ i, finrank K ↥(U i) = r := fun i => i.property
    have hinj : Function.Injective U := Subtype.val_injective
    have hnum := blocks_probability_limit U r hr hU hinj
    have hden := D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting.injective_fraction_limit (K := K) r n hr hrn
    have hden' : Tendsto (fun m =>
        (Nat.card {f : (Fin (r*m) → K) →ₗ[K] Matrix (Fin n) (Fin m) K // Function.Injective f} : ℝ) /
          (Nat.card ((Fin (r*m) → K) →ₗ[K] Matrix (Fin n) (Fin m) K) : ℝ)) atTop (𝓝 1) := by
      have hid (m : ℕ) :
          (Nat.card {f : (Fin (r*m) → K) →ₗ[K] Matrix (Fin n) (Fin m) K // Function.Injective f} : ℝ) /
            (Nat.card ((Fin (r*m) → K) →ₗ[K] Matrix (Fin n) (Fin m) K) : ℝ) =
          (Nat.card {f : (Fin (r*m) → K) →ₗ[K] (Fin (n*m) → K) // Function.Injective f} : ℝ) /
            (Nat.card ((Fin (r*m) → K) →ₗ[K] (Fin (n*m) → K)) : ℝ) := by
        let e : Matrix (Fin n) (Fin m) K ≃ₗ[K] (Fin (n*m) → K) :=
          LinearEquiv.ofFinrankEq _ _ (by simp [Module.finrank_matrix])
        exact injection_ratio_codomain e
      apply hden.congr'
      exact Eventually.of_forall (fun m => by
        dsimp only
        rw [hid m,Nat.mul_comm r m,Nat.mul_comm n m])
    have h := hnum.div hden' one_ne_zero
    have hi : (Fintype.card I : ℝ) = gaussian (Fintype.card K) n (d-1) := by
      have hc := D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel.subspace_card_real (K := K) (E := Fin n → K) r (by simp; omega)
      simp only [finrank_fintype_fun_eq_card,Fintype.card_fin,Nat.card_eq_fintype_card] at hc
      change (Fintype.card I : ℝ) = gaussian (Fintype.card K) n r at hc
      rw [gaussian_symmetry _ n r (Fintype.one_lt_card (α := K)) (by omega)] at hc
      have he : n-r=d-1 := by dsimp [r]; omega
      simpa only [he,I] using hc
    have htarget : Tendsto (fun m => density K n m (r*m) d) atTop
        (𝓝 (P (Fintype.card K)^(Fintype.card I))) := by
      simpa only [div_one] using h.congr' (Eventually.of_forall (fun m =>
        (density_normalized K n d r m rfl hd0 hd).symm))
    rw [← Real.rpow_natCast,hi] at htarget
    simpa only [mrdDimension,Nat.mul_comm,r,if_neg hd1] using htarget
end ExactTarget
end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit
