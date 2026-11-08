/- GID: D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-field MRD density: reduction argument. -/
/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius.prod_error
question_answered: https://github.com/the-omega-institute/trureturing/issues/26598
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27411
Direct frozen declaration identities (not module pins):
D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_pascal_dual: sha256:732a0e73b6db4590bb33329cc31b58e8818df5c4b5d2a012c5011148f65b049b
D5.S3.Combinatorics.CylindricPartition.LiUncuDefs.gauss: sha256:f926774c1dcfc4f25ac8221be84ee089ae2dae1d643c4699259ccb4d03819006
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue: sha256:5eb9692ec654f291a1d656372d8e03b193e76c908bc1e2ff2eb45a5aa4627037
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_pascal: sha256:550c63d0efe0003d4bb8674a9a069eb9048fa35a2b2721ea6dfbfd2c1c0d85b0
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_right: sha256:d58867f67d4b21d6518bcad6227443794d8780bb74a241bc42e185889e4f18cb
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_succ: sha256:d4588b9721b518bd3ee79163f6f0bdf7f7335512ac2d76ddce88ef93efe452ce
D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.qnum: sha256:449bd3b087eb7428cc7010dc10aa2e0c53f621f7924580deac57590f61f4d8c1
D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.qbinom: sha256:68e8c0ddbc9607a30b65c1287978f90ef5697b9b7d1e4d398109c2163ca6a5c0
D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.qfact: sha256:4af4fb4b2a9a58c0413510027dc6344acdd7d67dcadcce7fb1396461c01e776f
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.qfact_pos: sha256:42d505b1b8cc898f522c07e647782dc2de4488f122103b1e5ef0232e7a7fe384
_private.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.0.D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_eq_qbinom: sha256:0bf560da58c37f02c1e7b7913db835f73dca4fb983ff22fca277abc2ec264401
D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_symmetry: sha256:b83baaa08c18e66ee406173ad88427b09c8adef06bb689ecbfd3fb286955acbf
Per-declaration proof_shape; escape_witness; consumers:
gaussian: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.claim, gaussian_eq_qbinom
P: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.claim, product_limit
MinDistanceAtLeast: proof_shape=bind-only; escape_witness=none; consumers=GoodCodes, min_distance_kernel_condition, min_distance_one
GoodCodes: proof_shape=bind-only; escape_witness=none; consumers=density
AllCodes: proof_shape=bind-only; escape_witness=none; consumers=density
density: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.claim, D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.density_generator_ratio, density_one
mrdDimension: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.claim, density_one
matrix_rank_pos: proof_shape=bind-only; escape_witness=none; consumers=min_distance_one
min_distance_one: proof_shape=bind-only; escape_witness=none; consumers=density_one
full_finrank: proof_shape=bind-only; escape_witness=none; consumers=density_one
density_one: proof_shape=bind-only; escape_witness=none; consumers=limit_one
limit_one: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.result
product_multipliable: proof_shape=bind-only; escape_witness=none; consumers=product_limit
product_limit: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityScalar.scalar_series_value
subspace_of_dimension_le: proof_shape=bind-only; escape_witness=none; consumers=rank_deficient_iff_kernel_contains
rank_deficient_iff_kernel_contains: proof_shape=bind-only; escape_witness=none; consumers=min_distance_kernel_condition
min_distance_kernel_condition: proof_shape=bind-only; escape_witness=none; consumers=mrd_iff_restrictions_injective
restrictRows: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.generator_block, restrictRows_zero_iff
restrictRows_zero_iff: proof_shape=bind-only; escape_witness=none; consumers=mrd_iff_restrictions_injective
mrd_iff_restrictions_injective: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.generator_mrd_iff
MRDDensityMobius.g_pascal_dual: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityMobius.partial_mobius
MRDDensityMobius.g_nonneg: proof_shape=content; escape_witness=MRDDensityMobius.g_nonneg; consumers=MRDDensityMobius.partial_mobius_error
MRDDensityMobius.partial_mobius: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityMobius.partial_mobius_error
MRDDensityMobius.partial_mobius_error: proof_shape=content; escape_witness=MRDDensityMobius.partial_mobius_error; consumers=MRDDensityMobius.mixed_mobius_error
MRDDensityMobius.prod_error: proof_shape=content; escape_witness=MRDDensityMobius.prod_error; consumers=MRDDensityMobius.mixed_mobius_error
MRDDensityMobius.mixed_mobius_error: proof_shape=content; escape_witness=MRDDensityMobius.prod_error; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityJoint.joint_zero_limit_of_moments
power_diff_qnum: proof_shape=bind-only; escape_witness=none; consumers=gaussian_factor
gaussian_factor: proof_shape=bind-only; escape_witness=none; consumers=gaussian_eq_qbinom
reverse_qnum_product: proof_shape=bind-only; escape_witness=none; consumers=gaussian_eq_qbinom
gaussian_eq_qbinom: proof_shape=bind-only; escape_witness=none; consumers=gaussian_eq_polynomial
gaussian_eq_polynomial: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments.frame_card_gaussian, gaussian_symmetry
MRDDensityAnalysis.approximating_limits: proof_shape=content; escape_witness=MRDDensityAnalysis.approximating_limits; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityJoint.joint_zero_limit_of_moments
MRDDensityAnalysis.vanishing_nondirect: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples.weighted_frame_moment_limit
MRDDensityAnalysis.automorphismProduct: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityJoint.polynomial_moment_limit, D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityScalar.c, MRDDensityAnalysis.automorphism_product_lower
MRDDensityAnalysis.automorphism_product_lower: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments.frame_card_gaussian, MRDDensityAnalysis.mobius_tail_bound
MRDDensityAnalysis.triangular_ge: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityAnalysis.mobius_tail_bound
MRDDensityAnalysis.mobius_tail_bound: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityScalar.series_bound, MRDDensityAnalysis.mobius_tail_limit
MRDDensityAnalysis.mobius_tail_limit: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityJoint.joint_zero_limit_of_moments
gaussian_symmetry: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.result
-/

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
import D5.S3.Combinatorics.CylindricPartition.LiUncuGaussian
import D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode

open D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode

open scoped BigOperators
open scoped Topology
open Filter

namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
/-- The q-binomial coefficient from the source, as a real-valued finite product. -/
noncomputable def gaussian (q a b : ℕ) : ℝ :=
  ∏ h ∈ Finset.range b,
    ((q : ℝ) ^ a - (q : ℝ) ^ h) / ((q : ℝ) ^ b - (q : ℝ) ^ h)

/-- The source's infinite product P(q)=∏_{j≥1}(1-q^(-j)). -/
noncomputable def P (q : ℕ) : ℝ :=
  ∏' j : ℕ, (1 - (q : ℝ)⁻¹ ^ (j + 1))

/-- Rank-metric minimum distance is at least d. -/
def MinDistanceAtLeast (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽]
    (n m d : ℕ) (C : Submodule 𝔽 (Matrix (Fin n) (Fin m) 𝔽)) : Prop :=
  ∀ (M : Matrix (Fin n) (Fin m) 𝔽), M ∈ C → M ≠ 0 → Matrix.rank M ≥ d

/-- The source's density numerator: k-dimensional subspaces with minimum distance at least d. -/
noncomputable def GoodCodes (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽]
    (n m k d : ℕ) : Type _ :=
  {C : Submodule 𝔽 (Matrix (Fin n) (Fin m) 𝔽) // Module.finrank 𝔽 C = k ∧ MinDistanceAtLeast 𝔽 n m d C}

/-- All k-dimensional 𝔽-linear subspaces of Mat_{n×m}(𝔽). -/
noncomputable def AllCodes (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽]
    (n m k : ℕ) : Type _ :=
  {C : Submodule 𝔽 (Matrix (Fin n) (Fin m) 𝔽) // Module.finrank 𝔽 C = k}

/-- δᵣ₍q₎(n×m,k,d), the source's proportion. -/
noncomputable def density (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽]
    (n m k d : ℕ) : ℝ :=
  (Nat.card (GoodCodes 𝔽 n m k d) : ℝ) / (Nat.card (AllCodes 𝔽 n m k) : ℝ)

/-- MRD codes are the codes attaining the Singleton-like dimension m(n−d+1). -/
def mrdDimension (n m d : ℕ) : ℕ := m * (n - d + 1)

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
private theorem matrix_rank_pos {𝔽 : Type*} [Field 𝔽] (n m : ℕ)
    (M : Matrix (Fin n) (Fin m) 𝔽) (hM : M ≠ 0) : 0 < Matrix.rank M := by
  apply Nat.pos_of_ne_zero
  intro h
  have hr : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
  have hm : M.mulVecLin = 0 := LinearMap.range_eq_bot.mp hr
  apply hM
  apply Matrix.ext
  intro i j
  have he := congrArg (fun f : (Fin m → 𝔽) →ₗ[𝔽] (Fin n → 𝔽) =>
    f (Pi.single j 1) i) hm
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using he

private theorem min_distance_one {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (n m : ℕ) (C : Submodule 𝔽 (Matrix (Fin n) (Fin m) 𝔽)) :
    MinDistanceAtLeast 𝔽 n m 1 C := by
  intro M _ hM
  exact matrix_rank_pos n m M hM

private theorem full_finrank {𝔽 : Type*} [Field 𝔽] (n m : ℕ)
    (C : Submodule 𝔽 (Matrix (Fin n) (Fin m) 𝔽)) :
    Module.finrank 𝔽 C = m * n ↔ C = ⊤ := by
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    simpa [Module.finrank_matrix, Nat.mul_comm] using h
  · intro h
    subst C
    simp [Module.finrank_matrix, Nat.mul_comm]

private theorem density_one {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (n m : ℕ) (hn : 1 ≤ n) : density 𝔽 n m (mrdDimension n m 1) 1 = 1 := by
  classical
  let e : GoodCodes 𝔽 n m (mrdDimension n m 1) 1 ≃
      AllCodes 𝔽 n m (mrdDimension n m 1) :=
    { toFun := fun C => ⟨C.1, C.2.1⟩
      invFun := fun C => ⟨C.1, C.2, min_distance_one n m C.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let c : AllCodes 𝔽 n m (mrdDimension n m 1) :=
    ⟨⊤, by simp [mrdDimension, Nat.sub_add_cancel hn, Module.finrank_matrix, Nat.mul_comm]⟩
  have hall : ∀ C : AllCodes 𝔽 n m (mrdDimension n m 1), C = c := by
    intro C
    apply Subtype.ext
    apply (full_finrank n m C.1).mp
    simpa [mrdDimension, Nat.sub_add_cancel hn] using C.2
  letI : Unique (AllCodes 𝔽 n m (mrdDimension n m 1)) :=
    { default := c, uniq := hall }
  unfold density
  rw [Nat.card_congr e]
  simp

theorem limit_one {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun m : ℕ => density 𝔽 n m (mrdDimension n m 1) 1) atTop (𝓝 1) := by
  simpa only [density_one n _ hn] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
private theorem product_multipliable (q : ℕ) (hq : 2 ≤ q) :
    Multipliable (fun j : ℕ => (1 - (q : ℝ)⁻¹ ^ (j + 1))) := by
  have hqR : (1 : ℝ) < q := by exact Nat.one_lt_cast.mpr hq
  have hpos : (0 : ℝ) < (q : ℝ)⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hqR)
  have hlt : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hqR
  apply multipliable_one_sub_of_summable
  simpa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos), abs_pow, pow_succ'] using
    ((summable_geometric_of_norm_lt_one (show ‖(q : ℝ)⁻¹‖ < 1 from by
      simpa [Real.norm_eq_abs, abs_of_pos hpos] using hlt)).mul_left (q : ℝ)⁻¹)

theorem product_limit (q : ℕ) (hq : 2 ≤ q) :
    Tendsto (fun k : ℕ => ∏ j ∈ Finset.range k, (1 - (q : ℝ)⁻¹ ^ (j + 1)))
      atTop (𝓝 (P q)) := by
  exact (product_multipliable q hq).tendsto_prod_tprod_nat

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
theorem subspace_of_dimension_le {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (W : Submodule K E) (r : ℕ) (hr : r ≤ Module.finrank K W) :
    ∃ U : Submodule K E, Module.finrank K U = r ∧ U ≤ W := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hr
  let u : Fin r → E := fun j => v j
  have hu : LinearIndependent K u := hv.map' W.subtype W.ker_subtype
  refine ⟨Submodule.span K (Set.range u), ?_, ?_⟩
  · simpa using finrank_span_eq_card hu
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact (v j).property

private theorem rank_deficient_iff_kernel_contains {K : Type*} [Field K]
    (n m d : ℕ) (hd : d ≤ n) (M : Matrix (Fin n) (Fin m) K) :
    M.rank < d ↔ ∃ U : Submodule K (Fin n → K),
      Module.finrank K U = n - d + 1 ∧ U ≤ LinearMap.ker M.transpose.mulVecLin := by
  have hk := M.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hk' : M.rank + Module.finrank K (LinearMap.ker M.transpose.mulVecLin) = n := by
    change M.transpose.rank + _ = _ at hk
    simpa only [Matrix.rank_transpose, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using hk
  constructor
  · intro h
    apply subspace_of_dimension_le _ (n - d + 1)
    omega
  · rintro ⟨U, hU, hle⟩
    have hdim := Submodule.finrank_mono hle
    rw [hU] at hdim
    omega

private theorem min_distance_kernel_condition {K : Type*} [Field K] [Fintype K]
    (n m d : ℕ) (hd : d ≤ n) (C : Submodule K (Matrix (Fin n) (Fin m) K)) :
    MinDistanceAtLeast K n m d C ↔
      ∀ U : Submodule K (Fin n → K), Module.finrank K U = n - d + 1 →
        ∀ M ∈ C, U ≤ LinearMap.ker M.transpose.mulVecLin → M = 0 := by
  constructor
  · intro h U hU M hM hk
    by_contra hn
    have hl := (rank_deficient_iff_kernel_contains n m d hd M).mpr ⟨U, hU, hk⟩
    exact Nat.not_lt_of_ge (h M hM hn) hl
  · intro h M hM hn
    by_contra hdM
    obtain ⟨U, hU, hk⟩ := (rank_deficient_iff_kernel_contains n m d hd M).mp
      (Nat.lt_of_not_ge hdM)
    exact hn (h U hU M hM hk)

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
noncomputable def restrictRows {K : Type*} [Field K] (n m : ℕ)
    (U : Submodule K (Fin n → K)) :
    Matrix (Fin n) (Fin m) K →ₗ[K] (U →ₗ[K] (Fin m → K)) where
  toFun M := (Matrix.toLin' M.transpose).comp U.subtype
  map_add' M N := by simp only [Matrix.transpose_add, map_add, LinearMap.add_comp]
  map_smul' a M := by simp only [Matrix.transpose_smul, map_smul, LinearMap.smul_comp, RingHom.id_apply]

private theorem restrictRows_zero_iff {K : Type*} [Field K] (n m : ℕ)
    (U : Submodule K (Fin n → K)) (M : Matrix (Fin n) (Fin m) K) :
    restrictRows n m U M = 0 ↔ U ≤ LinearMap.ker M.transpose.mulVecLin := by
  constructor
  · intro h u hu
    have hx := LinearMap.congr_fun h ⟨u,hu⟩
    exact hx
  · intro h
    apply LinearMap.ext
    intro u
    exact h u.property

theorem mrd_iff_restrictions_injective {K D : Type*} [Field K] [Fintype K]
    [AddCommGroup D] [Module K D]
    (n m d : ℕ) (hd : d ≤ n) (f : D →ₗ[K] (Matrix (Fin n) (Fin m) K))
    (hf : Function.Injective f) :
    MinDistanceAtLeast K n m d (LinearMap.range f) ↔
      ∀ U : Submodule K (Fin n → K), Module.finrank K U = n-d+1 →
        Function.Injective ((restrictRows n m U).comp f) := by
  rw [min_distance_kernel_condition n m d hd]
  constructor
  · intro h U hU
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hm : f x = 0 := h U hU (f x) ⟨x,rfl⟩
      ((restrictRows_zero_iff n m U (f x)).mp hx)
    apply hf
    simpa using hm
  · intro h U hU M hM hk
    obtain ⟨x,rfl⟩ := hM
    have hz : ((restrictRows n m U).comp f) x = 0 :=
      (restrictRows_zero_iff n m U (f x)).mpr hk
    have hx : x = 0 := (h U hU) (by simpa using hz)
    simp [hx]

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open scoped BigOperators
open Polynomial Finset
open D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
open D5.S3.Combinatorics.CylindricPartition.LiUncu
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius
private theorem g_pascal_dual (q : ℝ) (n k : ℕ) :
    gaussValue (q : ℝ) (n+1) (k+1) = q^(k+1) * gaussValue (q : ℝ) n (k+1) + gaussValue (q : ℝ) n k := by
  simp [gaussValue, gauss_pascal_dual]

private theorem g_nonneg {q : ℝ} (hq : 0 ≤ q) (n k : ℕ) : 0 ≤ gaussValue (q : ℝ) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_right, D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_succ]
  | succ n ih =>
    cases k with
    | zero => simp [D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_right]
    | succ k => rw [D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_pascal]; exact add_nonneg (ih _) (mul_nonneg (pow_nonneg hq _) (ih _))

private theorem partial_mobius (q : ℝ) (n R : ℕ) :
    (∑ k ∈ range (R+1), (-1 : ℝ)^k * q^k.choose 2 * gaussValue (q : ℝ) (n+1) k) =
      (-1 : ℝ)^R * q^(R+1).choose 2 * gaussValue (q : ℝ) n R := by
  induction R with
  | zero => simp [D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_right]
  | succ R ih =>
    rw [sum_range_succ, ih, g_pascal_dual]
    have hchoose : (R+2).choose 2 = (R+1).choose 2 + (R+1) := by
      simpa only [Nat.choose_two_right] using Nat.triangle_succ (R+1)
    rw [hchoose, pow_add q, pow_succ (-1 : ℝ) R]
    ring

private theorem partial_mobius_error (q : ℝ) (hq : 0 ≤ q) (t R : ℕ) :
    |(∑ k ∈ range (R+1), (-1 : ℝ)^k * q^k.choose 2 * gaussValue (q : ℝ) t k) -
       (if t = 0 then 1 else 0)| ≤ q^(R+1).choose 2 * gaussValue (q : ℝ) t (R+1) := by
  cases t with
  | zero =>
    have hz : (∑ k ∈ range (R+1), (-1 : ℝ)^k * q^k.choose 2 * gaussValue (q : ℝ) 0 k) = 1 := by
      rw [sum_eq_single 0]
      · simp [D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_right]
      · intro k hk hk0
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        simp [D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_succ]
      · simp
    rw [hz]
    simp [D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_zero_succ]
  | succ n =>
    rw [partial_mobius]
    simp only [Nat.succ_ne_zero, ite_false, sub_zero, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_of_nonneg (pow_nonneg hq _), abs_of_nonneg (g_nonneg hq _ _)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq _)
    rw [g_pascal_dual]
    exact le_add_of_nonneg_left (mul_nonneg (pow_nonneg hq _) (g_nonneg hq _ _))

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius
private theorem prod_error {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b e : ι → ℝ)
    (he : ∀ i ∈ s, 0 ≤ e i) (hb : ∀ i ∈ s, |b i| ≤ 1)
    (hab : ∀ i ∈ s, |a i - b i| ≤ e i) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤ (∏ i ∈ s, (1 + e i)) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hei := he i (mem_insert_self _ _)
    have hbi := hb i (mem_insert_self _ _)
    have habi := hab i (mem_insert_self _ _)
    have he' := fun j hj => he j (mem_insert_of_mem hj)
    have hb' := fun j hj => hb j (mem_insert_of_mem hj)
    have hab' := fun j hj => hab j (mem_insert_of_mem hj)
    have hprev := ih he' hb' hab'
    let Q := ∏ j ∈ s, (1 + e j)
    have hQ : 0 ≤ Q := by
      apply prod_nonneg
      intro j hj
      linarith [he' j hj]
    have ha (j : ι) (hj : j ∈ s) : |a j| ≤ 1 + e j := by
      calc
        |a j| = |a j - b j + b j| := by congr 1; ring
        _ ≤ |a j - b j| + |b j| := abs_add_le _ _
        _ ≤ 1 + e j := by linarith [hab' j hj, hb' j hj]
    have hA : |∏ j ∈ s, a j| ≤ Q := by
      rw [Finset.abs_prod]
      exact prod_le_prod₀ (fun _ _ => abs_nonneg _) ha
    rw [prod_insert hi, prod_insert hi, prod_insert hi]
    calc
      |a i * (∏ j ∈ s, a j) - b i * (∏ j ∈ s, b j)| =
          |(a i-b i) * (∏ j ∈ s, a j) + b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j)| := by
            congr 1; ring
      _ ≤ |a i-b i| * |∏ j ∈ s, a j| + |b i| * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| := by
        simpa only [abs_mul] using abs_add_le ((a i-b i) * (∏ j ∈ s, a j))
          (b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j))
      _ ≤ e i * Q + 1 * (Q-1) := add_le_add
        (mul_le_mul habi hA (abs_nonneg _) hei)
        (mul_le_mul hbi hprev (abs_nonneg _) zero_le_one)
      _ = (1+e i) * Q - 1 := by ring

theorem mixed_mobius_error {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (q : ℝ) (hq : 0 ≤ q) (t : ι → ℕ) (R : ℕ) :
    |(∏ i ∈ s, (∑ k ∈ range (R+1), (-1 : ℝ)^k * q^k.choose 2 * gaussValue (q : ℝ) (t i) k)) -
      (∏ i ∈ s, (if t i = 0 then (1 : ℝ) else 0))| ≤
      (∏ i ∈ s, (1 + q^(R+1).choose 2 * gaussValue (q : ℝ) (t i) (R+1))) - 1 := by
  apply prod_error
  · intro i hi
    exact mul_nonneg (pow_nonneg hq _) (g_nonneg hq _ _)
  · intro i hi
    split_ifs <;> norm_num
  · intro i hi
    exact partial_mobius_error q hq (t i) R

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode
private theorem power_diff_qnum (q : ℝ) (a h : ℕ) (hh : h ≤ a) :
    q^a - q^h = q^h * (q-1) * qnum q (a-h) := by
  rw [mul_assoc, show (q-1) * qnum q (a-h) = q^(a-h)-1 by exact mul_geom_sum q (a-h)]
  rw [mul_sub, ← pow_add, Nat.add_sub_of_le hh, mul_one]

private theorem gaussian_factor (q : ℕ) (hq : 2 ≤ q) (a b h : ℕ)
    (hab : b ≤ a) (hh : h < b) :
    ((q : ℝ)^a - (q : ℝ)^h) / ((q : ℝ)^b - (q : ℝ)^h) =
      qnum q (a-h) / qnum q (b-h) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hq1 : (q : ℝ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show q ≠ 1 by omega))
  rw [power_diff_qnum _ _ _ (by omega), power_diff_qnum _ _ _ (by omega), mul_div_mul_left _ _
    (mul_ne_zero (pow_ne_zero h hqR) hq1)]

private theorem reverse_qnum_product (q : ℝ) (a b : ℕ) (hab : b ≤ a) :
    (∏ h ∈ Finset.range b, qnum q (a-h)) =
      ∏ h ∈ Finset.range b, qnum q (a-b+h+1) := by
  rw [← Finset.prod_range_reflect (fun h => qnum q (a-b+h+1)) b]
  apply Finset.prod_congr rfl
  intro h hh
  congr 1
  have := Finset.mem_range.mp hh
  omega

private theorem gaussian_eq_qbinom (q a b : ℕ) (hq : 2 ≤ q) (hab : b ≤ a) :
    gaussian q a b = qbinom q a b := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hp (n : ℕ) : 0 < qfact (q : ℝ) n := by
    apply D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.qfact_pos
    exact hqpos
  have hn : qfact (q : ℝ) a = qfact q (a-b) *
      ∏ h ∈ Finset.range b, qnum q (a-b+h+1) := by
    unfold qfact
    conv_lhs => rw [show a = (a-b)+b by omega, Finset.prod_range_add]
  unfold gaussian
  have hg : (∏ h ∈ Finset.range b,
      ((q : ℝ)^a-(q : ℝ)^h)/((q : ℝ)^b-(q : ℝ)^h)) =
      (∏ h ∈ Finset.range b, qnum q (a-h)) /
        (∏ h ∈ Finset.range b, qnum q (b-h)) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro h hh
    exact gaussian_factor q hq a b h hab (Finset.mem_range.mp hh)
  rw [hg, reverse_qnum_product _ _ _ hab, reverse_qnum_product _ _ _ (le_refl b)]
  simp only [Nat.sub_self, zero_add]
  change (∏ h ∈ Finset.range b, qnum q (a-b+h+1)) / qfact q b = _
  unfold qbinom
  rw [if_pos hab, hn]
  field_simp [ne_of_gt (hp (a-b)), ne_of_gt (hp b)]

theorem gaussian_eq_polynomial (q a b : ℕ) (hq : 2 ≤ q) (hab : b ≤ a) :
    gaussian q a b = gaussValue (q : ℝ) a b := by
  rw [gaussian_eq_qbinom q a b hq hab]
  symm
  apply D5.S3.Combinatorics.Probability.AyyerMisraHalfDensityMode.gaussValue_eq_qbinom
  exact_mod_cast (show 0 < q by omega)

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open Filter
open scoped Topology
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis
theorem approximating_limits
    (p : ℕ → ℝ) (a b : ℕ → ℕ → ℝ) (c e : ℕ → ℝ) (L : ℝ)
    (hbound : ∀ R, ∀ᶠ m in atTop, |p m-a R m| ≤ b R m)
    (ha : ∀ R, Tendsto (a R) atTop (𝓝 (c R)))
    (hb : ∀ R, Tendsto (b R) atTop (𝓝 (e R)))
    (hc : Tendsto c atTop (𝓝 L)) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto p atTop (𝓝 L) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hε4 : 0 < ε/4 := by linarith
  have he' : ∀ᶠ R in atTop, e R < ε/4 := he.eventually (gt_mem_nhds hε4)
  have hc' : ∀ᶠ R in atTop, |c R-L| < ε/4 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hc (ε/4) hε4)
  obtain ⟨R, hRe, hRc⟩ := (he'.and hc').exists
  have ha' : ∀ᶠ m in atTop, |a R m-c R| < ε/4 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (ha R) (ε/4) hε4)
  have hb' : ∀ᶠ m in atTop, b R m < e R+ε/4 :=
    (hb R).eventually (gt_mem_nhds (by linarith : e R < e R+ε/4))
  rw [eventually_atTop] at ha' hb'
  obtain ⟨N₁,hN₁⟩ := ha'
  obtain ⟨N₂,hN₂⟩ := hb'
  obtain ⟨N₃,hN₃⟩ := (eventually_atTop.mp (hbound R))
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro m hm
  have h₁ := hN₁ m (le_trans (le_max_left _ _) hm)
  have h₂ := hN₂ m (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm)
  have h₃ := hN₃ m (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm)
  rw [Real.dist_eq]
  have ht : |p m-L| ≤ |p m-a R m|+|a R m-c R|+|c R-L| := by
    calc
      |p m-L| = |(p m-a R m)+(a R m-c R)+(c R-L)| := by congr 1; ring
      _ ≤ |(p m-a R m)+(a R m-c R)|+|c R-L| :=
        abs_add_le ((p m-a R m)+(a R m-c R)) (c R-L)
      _ ≤ |p m-a R m|+|a R m-c R|+|c R-L| :=
        by
        have h := abs_add_le (p m-a R m) (a R m-c R)
        linarith
  linarith

theorem vanishing_nondirect
    (q : ℝ) (hq : 1 < q) (C : ℝ) (w : ℕ → ℝ)
    (hzero : ∀ᶠ m in atTop, 0 ≤ w m)
    (hbound : ∀ᶠ m in atTop, w m ≤ C*(q^m)⁻¹) :
    Tendsto w atTop (𝓝 0) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hgeo : Tendsto (fun m : ℕ => (q^m)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_nonneg.mpr hq0.le) (inv_lt_one_of_one_lt₀ hq)
  have hupper : Tendsto (fun m => C*(q^m)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using hgeo.const_mul C
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper hzero hbound

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis
open Filter Finset
open scoped BigOperators Topology
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis
noncomputable def automorphismProduct (q : ℝ) (k : ℕ) : ℝ :=
  ∏ h ∈ range k, (q^k-q^h)

theorem automorphism_product_lower (q : ℝ) (hq : 2 ≤ q) (k : ℕ) :
    q^(k*(k-1)) ≤ automorphismProduct q k := by
  have hq0 : 0 < q := by linarith
  have hf (h : ℕ) (hh : h ∈ range k) : q^(k-1) ≤ q^k-q^h := by
    have hhk : h ≤ k-1 := by have := mem_range.mp hh; omega
    have hpow : q^h ≤ q^(k-1) := pow_le_pow_right₀ (by linarith) hhk
    have hk : k-1+1=k := by have := mem_range.mp hh; omega
    have hkpow : q^k=q^(k-1)*q := by simpa only [hk] using (pow_succ q (k-1))
    have hp := pow_nonneg hq0.le (k-1)
    nlinarith
  have h := prod_le_prod₀ (s := range k)
    (f := fun _h => q^(k-1)) (g := fun h => q^k-q^h)
    (fun _ _ => pow_nonneg hq0.le _) hf
  simpa only [automorphismProduct, prod_const, card_range, ← pow_mul, Nat.mul_comm] using h

private theorem triangular_ge (R : ℕ) : R ≤ (R+1).choose 2 := by
  induction R with
  | zero => simp
  | succ R ih =>
    change R+1 ≤ (R+2).choose 2
    have ht : (R+2).choose 2 = (R+1).choose 2+(R+1) := by
      simpa only [Nat.choose_two_right] using Nat.triangle_succ (R+1)
    omega

theorem mobius_tail_bound (q : ℝ) (hq : 2 ≤ q) (R : ℕ) :
    0 ≤ q^(R+1).choose 2 / automorphismProduct q (R+1) ∧
    q^(R+1).choose 2 / automorphismProduct q (R+1) ≤ (q^R)⁻¹ := by
  have hq0 : 0 < q := by linarith
  have hgl := automorphism_product_lower q hq (R+1)
  have hgl0 : 0 < automorphismProduct q (R+1) := lt_of_lt_of_le (pow_pos hq0 _) hgl
  have ht : (R+1).choose 2+(R+1).choose 2 ≤ (R+1)*((R+1)-1) := by
    rw [Nat.choose_two_right]
    omega
  have hpow := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ q) ht
  refine ⟨div_nonneg (pow_nonneg hq0.le _) hgl0.le, ?_⟩
  calc
    q^(R+1).choose 2 / automorphismProduct q (R+1) ≤
        q^(R+1).choose 2 / q^((R+1).choose 2+(R+1).choose 2) :=
      div_le_div_of_nonneg_left (pow_nonneg hq0.le _) (pow_pos hq0 _) (hpow.trans hgl)
    _ = (q^(R+1).choose 2)⁻¹ := by
      rw [pow_add]
      exact div_mul_cancel_left₀ (ne_of_gt (pow_pos hq0 _)) _
    _ ≤ (q^R)⁻¹ := inv_anti₀ (pow_pos hq0 _) (pow_le_pow_right₀ (by linarith) (triangular_ge R))

theorem mobius_tail_limit (q : ℝ) (hq : 2 ≤ q) :
    Tendsto (fun R : ℕ => q^(R+1).choose 2 / automorphismProduct q (R+1)) atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hgeo : Tendsto (fun R : ℕ => (q^R)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_nonneg.mpr hq0.le) (inv_lt_one_of_one_lt₀ (by linarith : 1 < q))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgeo
    (Eventually.of_forall fun R => (mobius_tail_bound q hq R).1)
    (Eventually.of_forall fun R => (mobius_tail_bound q hq R).2)

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityMobius
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction.MRDDensityAnalysis
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
theorem gaussian_symmetry (q n k : ℕ) (hq : 2 ≤ q) (hk : k ≤ n) :
    gaussian q n k = gaussian q n (n-k) := by
  rw [gaussian_eq_polynomial q n k hq hk,
    gaussian_eq_polynomial q n (n-k) hq (Nat.sub_le _ _)]
  unfold gaussValue
  rw [D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_symmetry n k hk]
end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnReduction
