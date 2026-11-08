/- GID: D5/S3/VertexAlgebra/Analysis/OriginalSobolev
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/OriginalSobolev
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Completions of the literal original Hermitian energy norms. -/

import D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
The norm is pulled back from the actual Sugawara power, not from the original
monomial coordinates. OriginalCurrentEnergy identifies the full non-diagonal Hm
with FactorialFockMetric by the invertible real full frame. We reuse that proof.
The algebraic grading and both inverse-Gram laws retain their original meaning.
The completion and projection machinery below is Mathlib (Apache 2.0).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator InnerProductSpace Topology
namespace D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeSugawaraCurrents
open Lattice.OriginalChargedEnergy OriginalGram SourceBPZ.OriginalMatterHermitian
open private originalCore original_positive original_nonnegative normD_sq normD_smul from
  D5.S3.VertexAlgebra.Energy.OriginalCurrentEnergy
open private Hm_grade_orthogonal energy_power_grade energy_bound_of_grades
  stateEnergies_nonneg from
  D5.S3.VertexAlgebra.Energy.OriginalNeutralEnergy
open private negative_grade_eq_zero from D5.S3.VertexAlgebra.Energy.OriginalWordEnergy

/-- The literal original data; the inverse is supplied with both equations. -/
structure Model where
  D : LatticeData
  positive : (gramReal D).PosDef
  inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ
  inverse_left : inverse * gramComplex D = 1
  inverse_right : gramComplex D * inverse = 1

open Model

variable (M : Model)

abbrev Model.energyOperator : Module.End ℂ (Carrier M.D) :=
  1 + sugawaraMode M.D M.inverse 0

private theorem power_coeff (k : ℕ) (v : Carrier M.D) (l : Label M.D) :
    carrierCoeffEquiv M.D ((M.energyOperator ^ k) v) l =
      ((energy M.D l : ℂ) + 1)^k * carrierCoeffEquiv M.D v l := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change carrierCoeffEquiv M.D
      (((1 : Module.End ℂ (Carrier M.D)) + sugawaraMode M.D M.inverse 0)
        ((M.energyOperator ^ k) v)) l = _
    simp only [LinearMap.add_apply, Module.End.one_apply, map_add, Finsupp.add_apply,
      actualL0_coeff M.D M.inverse M.inverse_left M.inverse_right, ih]
    rw [pow_succ']
    ring

private theorem weight_ne_zero (l : Label M.D) : (energy M.D l : ℂ) + 1 ≠ 0 := by
  have hn : 0 ≤ energy M.D l := by
    have := chargeEnergy_nonneg M.D M.positive l.1
    dsimp [energy]
    omega
  have hp : (0 : ℝ) < (energy M.D l : ℝ) + 1 := by
    have : (0 : ℝ) ≤ energy M.D l := by exact_mod_cast hn
    linarith
  intro hz
  have := congrArg Complex.re hz
  simp at this
  linarith

private theorem power_injective (k : ℕ) :
    Function.Injective (M.energyOperator ^ k) := by
  intro v w hvw
  apply (carrierCoeffEquiv M.D).injective
  ext l
  have hh := congrArg (fun u => carrierCoeffEquiv M.D u l) hvw
  rw [power_coeff, power_coeff] at hh
  exact mul_left_cancel₀ (pow_ne_zero k (weight_ne_zero M l)) hh

/-- Only a norm-instance synonym: its underlying elements are literally Carrier D. -/
@[reducible] def Model.Finite (_k : ℕ) := Carrier M.D

instance (k : ℕ) : AddCommGroup (M.Finite k) :=
  inferInstanceAs (AddCommGroup (Carrier M.D))
instance (k : ℕ) : Module ℂ (M.Finite k) :=
  inferInstanceAs (Module ℂ (Carrier M.D))

@[instance_reducible] private def sobolevCore (k : ℕ) : InnerProductSpace.Core ℂ (M.Finite k) where
  inner v w := Hm
    ((M.energyOperator ^ k) v) ((M.energyOperator ^ k) w)
  conj_inner_symm v w := (Hm_hermitian _ _).symm
  re_inner_nonneg v := original_nonnegative M.positive _
  add_left v w u := by rw [map_add, Hm_add_left]
  smul_left v w c := by rw [map_smul, Hm_smul_left]
  definite v hv := by
    have hz : (M.energyOperator ^ k) v = 0 := by
      by_contra hn
      have hp := (original_positive M.positive hn).2
      rw [hv] at hp
      exact (lt_irrefl 0) hp
    exact power_injective M k (hz.trans (map_zero _).symm)

instance (k : ℕ) : InnerProductSpace.Core ℂ (M.Finite k) := sobolevCore M k
instance (k : ℕ) : NormedAddCommGroup (M.Finite k) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
instance (k : ℕ) : InnerProductSpace ℂ (M.Finite k) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (M.Finite k))

/-- Nonnegative Sobolev completion; k=0 is the canonical Hm Hilbert completion. -/
abbrev Model.Sobolev (k : ℕ) := UniformSpace.Completion (M.Finite k)
abbrev Model.Hilbert := M.Sobolev 0

/-- Original finite states, with no change to coefficients or charge sectors. -/
def Model.embed (k : ℕ) : Carrier M.D →ₗ[ℂ] M.Sobolev k :=
  (UniformSpace.Completion.toComplₗᵢ : M.Finite k →ₗᵢ[ℂ] M.Sobolev k).toLinearMap

private theorem embed_norm (k : ℕ) (v : Carrier M.D) :
    ‖M.embed k v‖ = normD ((M.energyOperator ^ k) v) := by
  exact UniformSpace.Completion.norm_coe _

private theorem embed_inner (v w : Carrier M.D) :
    ⟪M.embed 0 v, M.embed 0 w⟫_ℂ = Hm v w := by
  change ⟪((v : M.Finite 0) : M.Sobolev 0), ((w : M.Finite 0) : M.Sobolev 0)⟫_ℂ = _
  rw [UniformSpace.Completion.inner_coe (E := M.Finite 0) (𝕜 := ℂ)]
  rfl

private theorem embed_injective (k : ℕ) : Function.Injective (M.embed k) :=
  UniformSpace.Completion.coe_injective (M.Finite k)

theorem embed_dense (k : ℕ) : DenseRange (M.embed k) :=
  UniformSpace.Completion.denseRange_coe (α := M.Finite k)

/-- Embedded *algebraic* grade. Its closedness is proved, not assumed. -/
def Model.gradeMap (k : ℕ) (n : ℤ) : grade M.D n →ₗ[ℂ] M.Sobolev k :=
  (M.embed k).comp (grade M.D n).subtype

def Model.completedGrade (k : ℕ) (n : ℤ) : Submodule ℂ (M.Sobolev k) :=
  (M.gradeMap k n).range

instance (k : ℕ) (n : ℤ) : FiniteDimensional ℂ (M.completedGrade k n) := by
  letI := grade_finiteDimensional M.D M.positive n
  exact LinearMap.finiteDimensional_range (M.gradeMap k n)

private theorem completedGrade_closed (k : ℕ) (n : ℤ) :
    IsClosed (M.completedGrade k n : Set (M.Sobolev k)) :=
  Submodule.closed_of_finiteDimensional _

instance (k : ℕ) (n : ℤ) : CompleteSpace (M.completedGrade k n) :=
  (completedGrade_closed M k n).completeSpace_coe

/-- Genuine orthogonal projections on the completion. -/
def Model.projection (k : ℕ) (n : ℤ) : M.Sobolev k →L[ℂ] M.Sobolev k :=
  (M.completedGrade k n).starProjection

private theorem projection_grade (k : ℕ) (E n : ℤ) (v : Carrier M.D)
    (hv : v ∈ grade M.D E) :
    M.projection k n (M.embed k v) = if E = n then M.embed k v else 0 := by
  classical
  by_cases hn : E = n
  · subst E
    simp only [if_pos rfl, projection]
    apply Submodule.starProjection_eq_self_iff.mpr
    exact ⟨⟨v, hv⟩, rfl⟩
  · simp only [if_neg hn, projection]
    apply (M.completedGrade k n).eq_starProjection_of_mem_of_inner_eq_zero
      (Submodule.zero_mem _)
    rintro w ⟨u, rfl⟩
    rw [sub_zero]
    change ⟪M.embed k v, M.embed k u⟫_ℂ = 0
    change ⟪((v : M.Finite k) : M.Sobolev k),
      (((u : Carrier M.D) : M.Finite k) : M.Sobolev k)⟫_ℂ = 0
    rw [UniformSpace.Completion.inner_coe (E := M.Finite k) (𝕜 := ℂ)]
    change Hm ((M.energyOperator ^ k) v) ((M.energyOperator ^ k) u) = 0
    rw [energy_power_grade M.inverse M.inverse_left M.inverse_right E v hv k,
      energy_power_grade M.inverse M.inverse_left M.inverse_right n u u.2 k,
      Hm_smul_left, Hm_smul_right,
      Hm_grade_orthogonal M.inverse M.inverse_left M.inverse_right E n hn v u hv u.2,
      mul_zero, mul_zero]

private theorem projection_embed (k : ℕ) (n : ℤ) (v : Carrier M.D) :
    M.projection k n (M.embed k v) = M.embed k (gradeProjection M.D n v) := by
  classical
  have hsum := sum_gradeProjections M.D v
  conv_lhs => rw [← hsum, map_sum, map_sum]
  simp_rw [projection_grade M k _ n _ (gradeProjection_mem M.D _ v)]
  by_cases hn : n ∈ stateEnergies M.D v
  · simp [Finset.sum_ite_eq', hn]
  · have hz : gradeProjection M.D n v = 0 := by
      apply (carrierCoeffEquiv M.D).injective
      ext l
      rw [gradeProjection_coeff]
      split_ifs with hl
      · by_contra h
        apply hn
        exact Finset.mem_image.mpr ⟨l, Finsupp.mem_support_iff.mpr h, hl⟩
      · simp
    simp [Finset.sum_ite_eq', hn, hz]

/-- Every finite energy truncation of a completed vector is genuinely algebraic. -/
def Model.truncation (k : ℕ) (F : Finset ℤ) : M.Sobolev k →L[ℂ] M.Sobolev k :=
  ∑ n ∈ F, M.projection k n

private theorem truncation_algebraic (k : ℕ) (F : Finset ℤ) (x : M.Sobolev k) :
    ∃ v : Carrier M.D, M.truncation k F x = M.embed k v := by
  classical
  have hs (n : ℤ) : ∃ v : grade M.D n,
      M.embed k v = M.projection k n x := by
    exact (M.completedGrade k n).starProjection_apply_mem x
  choose v hv using hs
  refine ⟨∑ n ∈ F, (v n : Carrier M.D), ?_⟩
  simp only [truncation, ContinuousLinearMap.sum_apply, map_sum, hv]

private theorem sobolev_grade_norm (k : ℕ) (E : ℕ) (v : Carrier M.D)
    (hv : v ∈ grade M.D (E : ℤ)) :
    normD ((M.energyOperator ^ k) v) = ((E : ℝ)+1)^k * normD v := by
  rw [energy_power_grade M.inverse M.inverse_left M.inverse_right _ v hv k,
    normD_smul M.positive, norm_pow]
  have he : ((E : ℂ)+1) = ((E+1 : ℕ) : ℂ) := by push_cast; rfl
  norm_cast

private theorem norm_order_mono (j k : ℕ) (hjk : j ≤ k) (v : Carrier M.D) :
    normD ((M.energyOperator ^ j) v) ≤ normD ((M.energyOperator ^ k) v) := by
  apply energy_bound_of_grades M.positive M.inverse M.inverse_left M.inverse_right
    (M.energyOperator ^ j) 0 1 (by norm_num) k ?_ ?_ v |>.trans_eq (one_mul _)
  · intro E u hu
    rw [energy_power_grade M.inverse M.inverse_left M.inverse_right E u hu j]
    simpa using (grade M.D E).smul_mem (((E : ℂ)+1)^j) hu
  · intro E u hu
    rw [sobolev_grade_norm M j E u hu, one_mul]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) E; linarith) hjk

/-- Continuous inclusions, initially defined by identity on the original carrier. -/
def Model.inclusion (j k : ℕ) (hjk : j ≤ k) : M.Sobolev k →L[ℂ] M.Sobolev j :=
  (M.embed j).extendOfNorm (M.embed k)

private theorem inclusion_embed (j k : ℕ) (hjk : j ≤ k) (v : Carrier M.D) :
    M.inclusion j k hjk (M.embed k v) = M.embed j v := by
  apply LinearMap.extendOfNorm_eq (embed_dense M k)
  refine ⟨1, fun u => ?_⟩
  simpa only [embed_norm, one_mul] using norm_order_mono M j k hjk u

private theorem inclusion_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    (M.inclusion i j hij).comp (M.inclusion j k hjk) =
      M.inclusion i k (hij.trans hjk) := by
  apply ContinuousLinearMap.ext
  intro x
  refine (embed_dense M k).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    simp only [ContinuousLinearMap.comp_apply, inclusion_embed]


private theorem projection_total (k : ℕ) (x : M.Sobolev k)
    (hx : ∀ n : ℤ, M.projection k n x = 0) : x = 0 := by
  have hfinite (v : Carrier M.D) : ⟪M.embed k v, x⟫_ℂ = 0 := by
    classical
    conv_lhs => rw [← sum_gradeProjections M.D v, map_sum, sum_inner]
    apply Finset.sum_eq_zero
    intro n hn
    have hp := projection_grade M k n n (gradeProjection M.D n v)
      (gradeProjection_mem M.D n v)
    simp at hp
    rw [← hp]
    change ⟪(M.completedGrade k n).starProjection _, x⟫_ℂ = 0
    rw [Submodule.inner_starProjection_left_eq_right]
    change ⟪M.embed k (gradeProjection M.D n v), M.projection k n x⟫_ℂ = 0
    rw [hx n, inner_zero_right]
  have hall (y : M.Sobolev k) : ⟪y, x⟫_ℂ = 0 := by
    refine (embed_dense M k).induction_on y ?_ ?_
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact hfinite
  exact inner_self_eq_zero.mp (hall x)

private theorem projection_inclusion (j k : ℕ) (hjk : j ≤ k) (n : ℤ)
    (x : M.Sobolev k) :
    M.inclusion j k hjk (M.projection k n x) =
      M.projection j n (M.inclusion j k hjk x) := by
  refine (embed_dense M k).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    simp only [projection_embed, inclusion_embed]

private theorem inclusion_injective (j k : ℕ) (hjk : j ≤ k) :
    Function.Injective (M.inclusion j k hjk) := by
  have hker (x : M.Sobolev k) (hx : M.inclusion j k hjk x = 0) : x = 0 := by
    apply projection_total M k x
    intro n
    obtain ⟨u, hu⟩ := (M.completedGrade k n).starProjection_apply_mem x
    change M.embed k u = M.projection k n x at hu
    have hh := projection_inclusion M j k hjk n x
    rw [← hu, inclusion_embed, hx, map_zero] at hh
    have hz : (u : Carrier M.D) = 0 :=
      embed_injective M j (hh.trans (map_zero _).symm)
    rw [← hu, hz, map_zero]
  intro x y hxy
  exact sub_eq_zero.mp (hker (x-y) (by rw [map_sub, hxy, sub_self]))

private theorem inclusion_self (k : ℕ) :
    M.inclusion k k le_rfl = ContinuousLinearMap.id ℂ (M.Sobolev k) := by
  ext x
  refine (embed_dense M k).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · exact inclusion_embed M k k le_rfl


private theorem projection_comp (k : ℕ) (n l : ℤ) (x : M.Sobolev k) :
    M.projection k n (M.projection k l x) =
      if l = n then M.projection k l x else 0 := by
  classical
  refine (embed_dense M k).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by split_ifs <;> fun_prop)
  · intro v
    rw [projection_embed, projection_grade M k l n _ (gradeProjection_mem M.D l v)]

private theorem projection_truncation (k : ℕ) (F : Finset ℤ) (n : ℤ) (hn : n ∈ F)
    (x : M.Sobolev k) :
    M.projection k n (M.truncation k F x) = M.projection k n x := by
  classical
  simp only [truncation, ContinuousLinearMap.sum_apply, map_sum, projection_comp]
  simp [Finset.sum_ite_eq', hn]

private theorem truncation_grade (k : ℕ) (F : Finset ℤ) (E : ℤ) (v : Carrier M.D)
    (hv : v ∈ grade M.D E) :
    M.truncation k F (M.embed k v) = if E ∈ F then M.embed k v else 0 := by
  classical
  simp only [truncation, ContinuousLinearMap.sum_apply, projection_grade M k E _ v hv]
  simp [Finset.sum_ite_eq]

private theorem truncation_norm (k : ℕ) (F : Finset ℤ) (x : M.Sobolev k) :
    ‖M.truncation k F x‖ ≤ ‖x‖ := by
  classical
  have ho : ⟪M.truncation k F x, x - M.truncation k F x⟫_ℂ = 0 := by
    have heval : M.truncation k F x = ∑ n ∈ F, M.projection k n x := by
      simp only [truncation, ContinuousLinearMap.sum_apply]
    have hsum := congrArg (fun y => ⟪y, x - M.truncation k F x⟫_ℂ) heval
    rw [sum_inner] at hsum
    rw [hsum]
    apply Finset.sum_eq_zero
    intro n hn
    change ⟪(M.completedGrade k n).starProjection x, x - M.truncation k F x⟫_ℂ = 0
    rw [Submodule.inner_starProjection_left_eq_right, map_sub]
    change ⟪x, M.projection k n x - M.projection k n (M.truncation k F x)⟫_ℂ = 0
    rw [projection_truncation M k F n hn, sub_self, inner_zero_right]
  have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (M.truncation k F x) (x - M.truncation k F x) ho
  have he : M.truncation k F x + (x - M.truncation k F x) = x := by abel
  rw [he] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖x - M.truncation k F x‖]

private theorem truncation_embed_of_subset (k : ℕ) (F : Finset ℤ) (v : Carrier M.D)
    (hF : stateEnergies M.D v ⊆ F) :
    M.truncation k F (M.embed k v) = M.embed k v := by
  classical
  conv_lhs => rw [← sum_gradeProjections M.D v, map_sum, map_sum]
  conv_rhs => rw [← sum_gradeProjections M.D v, map_sum]
  apply Finset.sum_congr rfl
  intro E hE
  rw [truncation_grade M k F E _ (gradeProjection_mem M.D E v), if_pos (hF hE)]

/-- These are algebraic finite-energy truncations by closed original grades. -/
private theorem truncation_tendsto (k : ℕ) (x : M.Sobolev k) :
    Filter.Tendsto (fun F : Finset ℤ => M.truncation k F x) Filter.atTop (𝓝 x) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨v,hv⟩ := Metric.denseRange_iff.mp (embed_dense M k) x (ε/3) (by positivity)
  refine ⟨stateEnergies M.D v, fun F hF => ?_⟩
  have he := truncation_embed_of_subset M k F v hF
  calc
    dist (M.truncation k F x) x ≤
        dist (M.truncation k F x) (M.truncation k F (M.embed k v)) +
          dist (M.embed k v) x := by rw [he]; exact dist_triangle _ _ _
    _ ≤ dist x (M.embed k v) + dist (M.embed k v) x := by
      refine add_le_add ?_ le_rfl
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact truncation_norm M k F _
    _ < ε := by rw [dist_comm (M.embed k v) x]; linarith

end D5.S3.VertexAlgebra.Analysis.OriginalSmearing
