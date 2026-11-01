/- GID: D5/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/GaussianExternalBlock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual external Gaussian blocks from finite families of square-summable mixed rows. -/

import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Finite families of square-summable rows define the actual scaled external Gaussian operator. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProductSpace lp ENNReal
open Filter Topology

namespace D5.S3.VertexAlgebra.TwistedGround.GaussianExternalBlock
open InfiniteGaussianFock
universe u v w

/-- Coordinate transpose pairing, complex linear in its argument. The star
inside the Hilbert inner product cancels its conjugate linear first slot. -/
def bilinear {J : Type u} (r : ℓ²(J, ℂ)) : ℓ²(J, ℂ) →L[ℂ] ℂ :=
  innerSL ℂ (star r)

theorem bilinear_eq_tsum {J : Type u} (r z : ℓ²(J, ℂ)) :
    bilinear r z = ∑' j, r j * z j := by
  simp [bilinear, lp.inner_eq_tsum, lp.star_apply, RCLike.inner_apply, mul_comm]

@[simp] theorem bilinear_single {J : Type u} [DecidableEq J]
    (r : ℓ²(J, ℂ)) (j : J) (c : ℂ) :
    bilinear r (lp.single 2 j c) = r j * c := by
  rw [bilinear_eq_tsum]
  simp [lp.single_apply, Pi.single_apply, mul_ite]

/-- Bilinear rank-one operator with actual l2 vectors. -/
def rank {J : Type u} (r s : ℓ²(J, ℂ)) : ℓ²(J, ℂ) →L[ℂ] ℓ²(J, ℂ) :=
  (bilinear s).smulRight r

@[simp] theorem rank_entry {J : Type u} [DecidableEq J]
    (r s : ℓ²(J, ℂ)) (i j : J) :
    rank r s (lp.single 2 j (1 : ℂ)) i = r i * s j := by
  simp [rank, mul_comm]

/-- The adjoint of a coordinate inclusion is actual coordinate restriction. -/
theorem inclusion_adjoint_apply {J : Type u} {K : Type v}
    [DecidableEq J] [DecidableEq K] (e : J → K) (he : Function.Injective e)
    (z : ℓ²(K, ℂ)) (j : J) :
    (coordinateInclusion e he).toContinuousLinearMap.adjoint z j = z (e j) := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (coordinateInclusion e he).toContinuousLinearMap (lp.single 2 j (1 : ℂ)) z
  simpa only [LinearIsometry.coe_toContinuousLinearMap, coordinateInclusion_single,
    lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, one_mul] using h

@[simp] theorem inclusion_apply_image {J : Type u} {K : Type v}
    [DecidableEq J] [DecidableEq K] (e : J → K) (he : Function.Injective e)
    (z : ℓ²(J, ℂ)) (j : J) :
    coordinateInclusion e he z (e j) = z j := by
  have h := (coordinateInclusion e he).inner_map_map (lp.single 2 j (1 : ℂ)) z
  simpa only [coordinateInclusion_single, lp.inner_single_left,
    RCLike.inner_apply, map_one, mul_one, one_mul] using h

@[simp] theorem inclusion_apply_outside {J : Type u} {K : Type v}
    [DecidableEq J] [DecidableEq K] (e : J → K) (he : Function.Injective e)
    (z : ℓ²(J, ℂ)) (k : K) (hk : k ∉ Set.range e) :
    coordinateInclusion e he z k = 0 := by
  have h : (lp.evalCLM ℂ (fun _ : K => ℂ) 2 k).comp
      (coordinateInclusion e he).toContinuousLinearMap = 0 := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro j
    ext c
    have hne : e j ≠ k := fun h => hk ⟨j,h⟩
    simp [ContinuousLinearMap.comp_apply, coordinateInclusion_single,
      lp.evalCLM, lp.single_apply, Pi.single_apply, hne, Ne.symm hne]
  exact DFunLike.congr_fun h z

variable {X : Type u} {I : Type v} [DecidableEq X] [DecidableEq I]

/-- Actual joint kernel with unrestricted finite external block. -/
def kernel (P : Matrix X X ℂ) (A : Data I) (R : X → ℓ²(I, ℂ)) :
    (X ⊕ I) → (X ⊕ I) → ℂ :=
  Matrix.fromBlocks P (fun x i => R x i) (fun i x => R x i) A.kernel

private def inclusion : ℓ²(I, ℂ) →ₗᵢ[ℂ] ℓ²(X ⊕ I, ℂ) :=
  coordinateInclusion Sum.inr Sum.inr_injective

private def base (A : Data I) : ℓ²(X ⊕ I, ℂ) →L[ℂ] ℓ²(X ⊕ I, ℂ) :=
  inclusion.toContinuousLinearMap.comp
    (A.oneParticle.comp inclusion.toContinuousLinearMap.adjoint)

private theorem base_norm (A : Data I) : ‖base (X := X) A‖ ≤ A.q := by
  have hJ : ‖(inclusion (X := X) (I := I)).toContinuousLinearMap‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  have hP : ‖(inclusion (X := X) (I := I)).toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hJ
  calc
    ‖base (X := X) A‖ ≤ ‖inclusion.toContinuousLinearMap‖ *
        ‖A.oneParticle.comp inclusion.toContinuousLinearMap.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (A.q * 1) := mul_le_mul hJ
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul A.opNorm_le hP (norm_nonneg _) A.q_nonneg))
      (norm_nonneg _) (by norm_num)
    _ = A.q := by ring

private theorem base_entry (A : Data I) (i j : X ⊕ I) :
    base (X := X) A (lp.single 2 j (1 : ℂ)) i =
      Matrix.fromBlocks (0 : Matrix X X ℂ) 0 0 A.kernel i j := by
  have hrestrict : inclusion.toContinuousLinearMap.adjoint (lp.single 2 j (1 : ℂ)) =
      (match j with | .inl _ => 0 | .inr k => lp.single 2 k 1) := by
    ext k
    rw [show inclusion.toContinuousLinearMap.adjoint _ k = _ from
      inclusion_adjoint_apply Sum.inr Sum.inr_injective _ k]
    cases j <;> simp [lp.single_apply, Pi.single_apply]
  simp only [base, ContinuousLinearMap.comp_apply, hrestrict]
  cases j with
  | inl x => cases i <;> simp [Matrix.fromBlocks]
  | inr j =>
    cases i with
    | inl x =>
      exact inclusion_apply_outside Sum.inr Sum.inr_injective _ (.inl x) (by simp)
    | inr i => exact inclusion_apply_image Sum.inr Sum.inr_injective _ i

variable [Fintype X]

private def external (P : Matrix X X ℂ) :
    ℓ²(X ⊕ I, ℂ) →L[ℂ] ℓ²(X ⊕ I, ℂ) :=
  ∑ x, ∑ y, P x y • rank (lp.single 2 (.inl x) 1) (lp.single 2 (.inl y) 1)

private def mixed (R : X → ℓ²(I, ℂ)) :
    ℓ²(X ⊕ I, ℂ) →L[ℂ] ℓ²(X ⊕ I, ℂ) :=
  ∑ x, (rank (lp.single 2 (.inl x) 1) (inclusion (R x)) +
    rank (inclusion (R x)) (lp.single 2 (.inl x) 1))

/-- A bounded joint operator, before imposing a small external scale. -/
def operator (P : Matrix X X ℂ) (A : Data I) (R : X → ℓ²(I, ℂ)) (t : ℂ) :
    ℓ²(X ⊕ I, ℂ) →L[ℂ] ℓ²(X ⊕ I, ℂ) :=
  base A + t • mixed R + t ^ 2 • external P

/-- The operator has the true scaled block entries; every transpose is
bilinear, even though adjoints occur inside the coordinate inclusion. -/
theorem operator_entry (P : Matrix X X ℂ) (A : Data I) (R : X → ℓ²(I, ℂ))
    (t : ℂ) (i j : X ⊕ I) :
    operator P A R t (lp.single 2 j (1 : ℂ)) i =
      (Sum.elim (fun _ : X => t) (fun _ : I => 1) i) * kernel P A R i j *
      (Sum.elim (fun _ : X => t) (fun _ : I => 1) j) := by
  have hout (x : X) (r : ℓ²(I, ℂ)) : inclusion r (.inl x) = 0 :=
    inclusion_apply_outside Sum.inr Sum.inr_injective _ _ (by simp)
  have hin (k : I) (r : ℓ²(I, ℂ)) : inclusion (X := X) r (.inr k) = r k :=
    inclusion_apply_image Sum.inr Sum.inr_injective _ _
  simp only [operator, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    base_entry, mixed, external, ContinuousLinearMap.sum_apply, lp.coeFn_sum,
    Finset.sum_apply, rank_entry]
  cases i <;> cases j <;>
    simp [kernel, Matrix.fromBlocks, lp.single_apply, Pi.single_apply, hout, hin,
      mul_ite, ite_mul, Finset.mul_sum, Finset.sum_mul,
      pow_two, mul_assoc, mul_comm, mul_left_comm]

/-- The external scale is chosen from continuity of an actual operator
polynomial at zero, where only the given strict contraction remains. -/
theorem exists_positive_scale (P : Matrix X X ℂ) (A : Data I)
    (R : X → ℓ²(I, ℂ)) :
    ∃ t : ℝ, 0 < t ∧ ‖operator P A R (t : ℂ)‖ < 1 := by
  have hc : Continuous (fun t : ℝ => ‖operator P A R (t : ℂ)‖) := by
    unfold operator
    fun_prop
  have hzero : ‖operator P A R (0 : ℂ)‖ < 1 := by
    simpa [operator] using (base_norm (X := X) A).trans_lt A.q_lt_one
  have he : ∀ᶠ t : ℝ in 𝓝 0, ‖operator P A R (t : ℂ)‖ < 1 :=
    hc.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hzero)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ε / 2, by positivity, hball ?_⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)] using
    half_lt_self hε

/-- The row norm series is obtained directly from the supplied l2 vector. -/
theorem row_square_summable (r : ℓ²(I, ℂ)) : Summable (fun i => ‖r i‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp r).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

/-- The full scaled coordinate matrix has finite HS mass, including both
mixed rectangles. This uses finitely many l2 rows, with no mixed smallness. -/
theorem operator_square_summable (P : Matrix X X ℂ) (A : Data I)
    (R : X → ℓ²(I, ℂ)) (t : ℂ) :
    Summable (fun ij : (X ⊕ I) × (X ⊕ I) =>
      ‖operator P A R t (lp.single 2 ij.2 1) ij.1‖ ^ 2) := by
  let f (ij : (X ⊕ I) × (X ⊕ I)) :=
    ‖operator P A R t (lp.single 2 ij.2 1) ij.1‖ ^ 2
  have hxx : Summable (fun ij : X × X => f (.inl ij.1, .inl ij.2)) :=
    Summable.of_finite
  have hxi : Summable (fun ij : X × I => f (.inl ij.1, .inr ij.2)) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    constructor
    · intro x
      simpa [f, operator_entry, kernel, Matrix.fromBlocks, norm_mul, mul_pow] using
        (row_square_summable (R x)).mul_left (‖t‖ ^ 2)
    · exact Summable.of_finite
  have hix : Summable (fun ij : I × X => f (.inr ij.1, .inl ij.2)) := by
    have hh := hxi.prod_symm
    simpa [f, operator_entry, kernel, Matrix.fromBlocks, norm_mul, mul_pow,
      mul_comm] using hh
  have hii : Summable (fun ij : I × I => f (.inr ij.1, .inr ij.2)) := by
    simpa [f, operator_entry, kernel, Matrix.fromBlocks, Data.kernel] using A.square_summable
  have hleft : Summable (fun ij : X × (X ⊕ I) => f (.inl ij.1, ij.2)) := by
    apply (Equiv.prodSumDistrib X X I).symm.summable_iff.mp
    exact Summable.sum _ hxx hxi
  have hright : Summable (fun ij : I × (X ⊕ I) => f (.inr ij.1, ij.2)) := by
    apply (Equiv.prodSumDistrib I X I).symm.summable_iff.mp
    exact Summable.sum _ hix hii
  apply (Equiv.sumProdDistrib X I (X ⊕ I)).symm.summable_iff.mp
  exact Summable.sum _ hleft hright

/-- The scaled block is actual InfiniteGaussianFock.Data. No Gaussian
summability or sewing conclusion is stored as an input. -/
def data (P : Matrix X X ℂ) (A : Data I) (R : X → ℓ²(I, ℂ))
    (hP : ∀ x y, P x y = P y x) (t : ℂ)
    (ht : ‖operator P A R t‖ < 1) : Data (X ⊕ I) where
  oneParticle := operator P A R t
  q := ‖operator P A R t‖
  massBound := ∑' ij : (X ⊕ I) × (X ⊕ I),
    ‖operator P A R t (lp.single 2 ij.2 1) ij.1‖ ^ 2
  q_nonneg := norm_nonneg _
  q_lt_one := ht
  opNorm_le := le_rfl
  symmetric := by
    intro i j
    simp only [operator_entry]
    have hsym : kernel P A R i j = kernel P A R j i := by
      cases i <;> cases j <;> simp [kernel, Matrix.fromBlocks, Data.kernel, hP, A.symmetric]
    rw [hsym]
    ring
  square_summable := operator_square_summable P A R t
  square_sum_le := le_rfl

end D5.S3.VertexAlgebra.TwistedGround.GaussianExternalBlock
