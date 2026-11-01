/- GID: D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common finite principal blocks construct the actual joint Gaussian l2 vector. -/

import D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
The joint Gaussian coefficients and vector are constructed from finite principal blocks.
The finite estimate is the pinned FactorialFockQuadraticEstimate supplier.
The finite-subsum strategy follows the completed OriginalFullColourSummability
candidate; its source-specific Corr identity is neither imported nor assumed.
Here arbitrary joint blocks stabilize by the actual polynomial killCompl map.
Hilbert inclusions use Mathlib's orthogonal-family isometry, not new synthesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProductSpace lp ENNReal Matrix.Norms.L2Operator
open ComplexConjugate
open Filter Topology

namespace D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock

open MvPolynomial
open FactorialFockMetric (Occupation weight scale)

universe u v

/-- Standard ON coordinates, used for one-particle compressions and orthogonal blocks. -/
def coordinateBasis (J : Type u) : HilbertBasis J ℂ ℓ²(J, ℂ) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem coordinateBasis_apply {J : Type u} [DecidableEq J] (j : J) :
    coordinateBasis J j = lp.single 2 j (1 : ℂ) :=
  (coordinateBasis J).repr_self j

/-- Canonical zero inclusion along an injection. Mathlib supplies the isometry. -/
def coordinateInclusion {A : Type u} {B : Type v}
    (e : A → B) (he : Function.Injective e) : ℓ²(A, ℂ) →ₗᵢ[ℂ] ℓ²(B, ℂ) :=
  ((coordinateBasis B).orthonormal.comp e he).orthogonalFamily.linearIsometry

@[simp] theorem coordinateInclusion_single {A : Type u} {B : Type v}
    [DecidableEq A] [DecidableEq B] (e : A → B) (he : Function.Injective e)
    (a : A) (c : ℂ) :
    coordinateInclusion e he (lp.single 2 a c) = lp.single 2 (e a) c := by
  rw [coordinateInclusion, OrthogonalFamily.linearIsometry_apply_single]
  simp only [LinearIsometry.toSpanSingleton_apply, Function.comp_apply,
    coordinateBasis_apply]
  simpa only [smul_eq_mul, mul_one] using
    (lp.single_smul (E := fun _ : B => ℂ) 2 (e a) c (1 : ℂ)).symm

/-- Only genuine one-particle analytic hypotheses are stored here. The kernel
is derived from a bounded operator's actual ON matrix, rather than certified
by entrywise estimates or by the desired Gaussian conclusion. -/
structure Data (I : Type u) [DecidableEq I] where
  oneParticle : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ)
  q : ℝ
  massBound : ℝ
  q_nonneg : 0 ≤ q
  q_lt_one : q < 1
  opNorm_le : ‖oneParticle‖ ≤ q
  symmetric : ∀ i j, oneParticle (lp.single 2 j (1 : ℂ)) i =
    oneParticle (lp.single 2 i (1 : ℂ)) j
  square_summable : Summable (fun ij : I × I =>
    ‖oneParticle (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2)
  square_sum_le : (∑' ij : I × I,
    ‖oneParticle (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2) ≤ massBound

namespace Data
variable {I : Type u} [DecidableEq I]

def kernel (D : Data I) (i j : I) : ℂ :=
  D.oneParticle (lp.single 2 j (1 : ℂ)) i

def block (D : Data I) (S : Finset I) : Matrix S S ℂ :=
  fun i j => D.kernel i.val j.val

/-- Natural finite orthonormal inclusion, with the Euclidean l2 norm. -/
def finiteInclusion (S : Finset I) : EuclideanSpace ℂ S →ₗᵢ[ℂ] ℓ²(I, ℂ) :=
  (coordinateInclusion (fun i : S => i.val) Subtype.val_injective).comp
    (lpPiLpₗᵢ (fun _ : S => ℂ) ℂ).symm.toLinearIsometry

@[simp] theorem finiteInclusion_single (S : Finset I) (j : S) :
    finiteInclusion S (EuclideanSpace.single j (1 : ℂ)) =
      lp.single 2 j.val (1 : ℂ) := by
  have h : (lpPiLpₗᵢ (fun _ : S => ℂ) ℂ).symm
      (EuclideanSpace.single j (1 : ℂ)) = lp.single 2 j (1 : ℂ) := by
    apply lp.ext
    funext i
    simp [coe_lpPiLpₗᵢ_symm, PiLp.single_apply, lp.single_apply, Pi.single_apply]
  change coordinateInclusion (fun i : S => i.val) Subtype.val_injective
      ((lpPiLpₗᵢ (fun _ : S => ℂ) ℂ).symm (EuclideanSpace.single j (1 : ℂ))) = _
  rw [h]
  exact coordinateInclusion_single (fun i : S => i.val) Subtype.val_injective j (1 : ℂ)

@[simp] theorem finiteInclusion_adjoint_apply (S : Finset I) (x : ℓ²(I, ℂ)) (i : S) :
    ContinuousLinearMap.adjoint (finiteInclusion S).toContinuousLinearMap x i = x i.val := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (finiteInclusion S).toContinuousLinearMap (EuclideanSpace.single i (1 : ℂ)) x
  change ⟪EuclideanSpace.single i (1 : ℂ),
      (ContinuousLinearMap.adjoint (finiteInclusion S).toContinuousLinearMap) x⟫_ℂ =
    ⟪finiteInclusion S (EuclideanSpace.single i (1 : ℂ)), x⟫_ℂ at h
  rw [finiteInclusion_single] at h
  simpa only [EuclideanSpace.inner_single_left, lp.inner_single_left,
    RCLike.inner_apply,
    map_one, mul_one, one_mul] using h

/-- Actual orthogonal principal compression P_S L J_S. -/
def compression (D : Data I) (S : Finset I) :
    EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S :=
  (ContinuousLinearMap.adjoint (finiteInclusion S).toContinuousLinearMap).comp
    (D.oneParticle.comp (finiteInclusion S).toContinuousLinearMap)

theorem compression_eq_matrix (D : Data I) (S : Finset I) :
    D.compression S = Matrix.toEuclideanCLM (𝕜 := ℂ) (D.block S) := by
  have hmatrix (i j : S) :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (D.block S)
        (EuclideanSpace.single j (1 : ℂ)) i = D.block S i j := by
    simp [Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct]
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun S ℂ).toBasis.ext
  intro j
  change D.compression S ((EuclideanSpace.basisFun S ℂ) j) =
    Matrix.toEuclideanCLM (𝕜 := ℂ) (D.block S) ((EuclideanSpace.basisFun S ℂ) j)
  rw [EuclideanSpace.basisFun_apply]
  ext i
  rw [hmatrix]
  change ContinuousLinearMap.adjoint (finiteInclusion S).toContinuousLinearMap
    (D.oneParticle (finiteInclusion S (EuclideanSpace.single j (1 : ℂ)))) i = D.block S i j
  rw [finiteInclusion_adjoint_apply, finiteInclusion_single]
  rfl

/-- The finite operator norm is derived from L and contractive ON maps. -/
theorem block_opNorm_le (D : Data I) (S : Finset I) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (D.block S)‖ ≤ D.q := by
  rw [← D.compression_eq_matrix S]
  have hJ : ‖(finiteInclusion S).toContinuousLinearMap‖ ≤ 1 :=
    (finiteInclusion S).norm_toContinuousLinearMap_le
  have hP : ‖ContinuousLinearMap.adjoint
      (finiteInclusion S).toContinuousLinearMap‖ ≤ 1 := by
    simpa only [(ContinuousLinearMap.adjoint).norm_map] using hJ
  calc
    ‖D.compression S‖ ≤ ‖ContinuousLinearMap.adjoint
        (finiteInclusion S).toContinuousLinearMap‖ *
          ‖D.oneParticle.comp (finiteInclusion S).toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (D.q * 1) := mul_le_mul hP
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul D.opNorm_le hJ (norm_nonneg _) D.q_nonneg))
      (norm_nonneg _) (by norm_num)
    _ = D.q := by ring

/-- No exchange of double series: one finite product embeds in I x I. -/
theorem block_mass_le (D : Data I) (S : Finset I) :
    (∑ i : S, ∑ j : S, ‖D.block S i j‖ ^ 2) ≤ D.massBound := by
  let e : S × S → I × I := fun ij => (ij.1.val, ij.2.val)
  have he : Function.Injective e := by
    intro a b h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))
  have hfinite : (∑ ij : S × S, ‖D.kernel (e ij).1 (e ij).2‖ ^ 2) =
      ∑ ij ∈ Finset.univ.image e, ‖D.kernel ij.1 ij.2‖ ^ 2 := by
    rw [Finset.sum_image he.injOn]
  calc
    _ = ∑ ij : S × S, ‖D.kernel (e ij).1 (e ij).2‖ ^ 2 := by
      simp only [Fintype.sum_prod_type, block, e]
    _ = _ := hfinite
    _ ≤ ∑' ij : I × I, ‖D.kernel ij.1 ij.2‖ ^ 2 :=
      D.square_summable.sum_le_tsum _ (fun _ _ => sq_nonneg _)
    _ ≤ D.massBound := D.square_sum_le

end Data

section Stabilization
variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

/-- Projection sends Q_K to the actual principal Q, including cross terms.
The complex symmetric convention is holomorphic: no conjugation occurs. -/
theorem quadratic_projection (K : Matrix B B ℂ) (e : A → B)
    (he : Function.Injective e) :
    killCompl he (FactorialFockQuadraticEstimate.quadratic K) =
      FactorialFockQuadraticEstimate.quadratic (fun i j => K (e i) (e j)) := by
  let ρ : MvPolynomial B ℂ →ₐ[ℂ] MvPolynomial A ℂ := killCompl he
  have hin (i : A) : ρ (X (e i)) = X i := by
    simpa only [rename_X] using killCompl_rename_app he (X i : MvPolynomial A ℂ)
  have hout (i : B) (hi : i ∉ Set.range e) : ρ (X i) = 0 := by
    have hirange : ∀ x : A, e x ≠ i := fun x hx => hi ⟨x, hx⟩
    simp [ρ, killCompl, hirange]
  simp only [FactorialFockQuadraticEstimate.quadratic, map_smul, map_sum, map_mul]
  congr 1
  symm
  apply Fintype.sum_of_injective e he
    (fun i => ∑ j : A, K (e i) (e j) • (X i * X j))
    (fun i => ∑ j : B, K i j • (ρ (X i) * ρ (X j)))
  · intro i hi
    simp [hout i hi]
  · intro i
    apply Fintype.sum_of_injective e he
      (fun j => K (e i) (e j) • (X i * X j))
      (fun j => K (e i) j • (ρ (X (e i)) * ρ (X j)))
    · intro j hj
      simp [hout j hj]
    · intro j
      rw [hin, hin]

/-- An algebra homomorphism preserves ALL powers and the exact 1/n! factor. -/
theorem gaussianPiece_projection (K : Matrix B B ℂ) (e : A → B)
    (he : Function.Injective e) (n : ℕ) :
    killCompl he (FactorialFockQuadraticEstimate.gaussianPiece K n) =
      FactorialFockQuadraticEstimate.gaussianPiece (fun i j => K (e i) (e j)) n := by
  simp only [FactorialFockQuadraticEstimate.gaussianPiece, map_smul, map_pow,
    quadratic_projection K e he]

/-- Zero occupations on every added mode give exactly the same coefficient.
This is proved from polynomial projection, not supplied as consistency data. -/
theorem gaussianCoefficient_enlarge (K : Matrix B B ℂ) (e : A → B)
    (he : Function.Injective e) (d : A →₀ ℕ) :
    FactorialFockQuadraticEstimate.gaussianCoefficient K (d.mapDomain e) =
      FactorialFockQuadraticEstimate.gaussianCoefficient (fun i j => K (e i) (e j)) d := by
  unfold FactorialFockQuadraticEstimate.gaussianCoefficient
  rw [Finsupp.degree_mapDomain]
  rw [← gaussianPiece_projection K e he, coeff_killCompl]

end Stabilization

section Coefficients
variable {I : Type u} [DecidableEq I]

/-- Restrict all occupation multiplicities, including repeats, to a finite block. -/
def restrictOccupation (S : Finset I) (d : Occupation I) : Occupation S :=
  d.comapDomain (fun i : S => i.val) Subtype.val_injective.injOn

theorem extend_restrict (S : Finset I) (d : Occupation I) (hd : d.support ⊆ S) :
    (restrictOccupation S d).mapDomain (fun i : S => i.val) = d := by
  apply Finsupp.mapDomain_comapDomain (fun i : S => i.val) Subtype.val_injective d
  intro i hi
  exact ⟨⟨i, hd hi⟩, rfl⟩

theorem weight_restrict (S : Finset I) (d : Occupation I) (hd : d.support ⊆ S) :
    weight (restrictOccupation S d) = weight d := by
  have h : weight ((restrictOccupation S d).mapDomain (fun i : S => i.val)) =
      weight (restrictOccupation S d) := Finsupp.prod_mapDomain_index_inj Subtype.val_injective
  rw [extend_restrict S d hd] at h
  exact h.symm

/-- Definition uses the smallest finite support. Independence is proved next. -/
def coefficient (K : I → I → ℂ) (d : Occupation I) : ℂ :=
  FactorialFockQuadraticEstimate.gaussianCoefficient
    (fun i j : d.support => K i.val j.val) (restrictOccupation d.support d)

/-- Any finite containing block computes the SAME actual Gaussian coefficient. -/
theorem coefficient_on_block (K : I → I → ℂ) (S : Finset I) (d : Occupation I)
    (hd : d.support ⊆ S) :
    coefficient K d = FactorialFockQuadraticEstimate.gaussianCoefficient
      (fun i j : S => K i.val j.val) (restrictOccupation S d) := by
  let e : d.support → S := fun i => ⟨i.val, hd i.property⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun x : S => x.val) hij
  have hmap : (restrictOccupation d.support d).mapDomain e = restrictOccupation S d := by
    apply Finsupp.mapDomain_injective (f := fun i : S => i.val) Subtype.val_injective
    rw [← Finsupp.mapDomain_comp]
    change (restrictOccupation d.support d).mapDomain (fun i : d.support => i.val) = _
    rw [extend_restrict _ _ (fun _ h => h), extend_restrict _ _ hd]
  rw [coefficient, ← gaussianCoefficient_enlarge (fun i j : S => K i.val j.val) e he,
    hmap]

/-- ONE block for an entire finite occupation family, not one cutoff per term. -/
def commonBlock (F : Finset (Occupation I)) : Finset I := F.biUnion Finsupp.support

theorem support_subset_commonBlock (F : Finset (Occupation I))
    (d : Occupation I) (hd : d ∈ F) : d.support ⊆ commonBlock F := by
  intro i hi
  exact Finset.mem_biUnion.mpr ⟨d, hd, hi⟩

theorem commonRestriction_injective (F : Finset (Occupation I)) :
    Set.InjOn (restrictOccupation (commonBlock F)) F := by
  intro d hd e he h
  have h' := congrArg (fun a => a.mapDomain (fun i : commonBlock F => i.val)) h
  simpa only [extend_restrict _ d (support_subset_commonBlock F d hd),
    extend_restrict _ e (support_subset_commonBlock F e he)] using h'

end Coefficients

namespace Data
variable {I : Type u} [DecidableEq I]

/-- Bound for the complete squared Fock norm. -/
def bound (D : Data I) : ℝ := Real.exp (D.massBound / (2 * (1 - D.q ^ 2)))

/-- The substantive cofinal finite-subsum estimate. All terms live in the
same block before the native finite_occupation_bound theorem is applied. -/
theorem finite_occupation_bound (D : Data I) (F : Finset (Occupation I)) :
    (∑ d ∈ F, (weight d : ℝ) * ‖coefficient D.kernel d‖ ^ 2) ≤ D.bound := by
  let S := commonBlock F
  let R := F.image (restrictOccupation S)
  have he : (∑ d ∈ F, (weight d : ℝ) * ‖coefficient D.kernel d‖ ^ 2) =
      ∑ d ∈ R, (weight d : ℝ) * ‖FactorialFockQuadraticEstimate.gaussianCoefficient (D.block S) d‖ ^ 2 := by
    dsimp [R]
    rw [Finset.sum_image (commonRestriction_injective F)]
    apply Finset.sum_congr rfl
    intro d hd
    rw [coefficient_on_block D.kernel S d (support_subset_commonBlock F d hd),
      weight_restrict S d (support_subset_commonBlock F d hd)]
    rfl
  have hden : 0 < 2 * (1 - D.q ^ 2) := by
    have := pow_lt_one₀ D.q_nonneg D.q_lt_one (by norm_num : 2 ≠ 0)
    linarith
  rw [he]
  calc
    _ ≤ Real.exp ((∑ i : S, ∑ j : S, ‖D.block S i j‖ ^ 2) /
        (2 * (1 - D.q ^ 2))) :=
      FactorialFockQuadraticEstimate.finite_occupation_bound (D.block S)
        (fun i j => D.symmetric i.val j.val) D.q_nonneg D.q_lt_one (D.block_opNorm_le S) R
    _ ≤ D.bound := Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right (D.block_mass_le S) hden.le)

/-- Whole occupation summability, including mixed/repeated occupations of
arbitrarily many modes. No unproved swap of mode and particle sums occurs. -/
theorem occupation_summable (D : Data I) :
    Summable (fun d : Occupation I => (weight d : ℝ) * ‖coefficient D.kernel d‖ ^ 2) :=
  summable_of_sum_le (fun d => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    D.finite_occupation_bound

theorem occupation_tsum_le (D : Data I) :
    (∑' d : Occupation I, (weight d : ℝ) * ‖coefficient D.kernel d‖ ^ 2) ≤ D.bound :=
  D.occupation_summable.tsum_le_of_sum_le D.finite_occupation_bound

end Data

/-- The factorial scale has exactly the native weight as squared modulus. -/
theorem norm_scale_sq {I : Type u} (d : Occupation I) :
    ‖scale d‖ ^ 2 = (weight d : ℝ) := by
  simp only [scale, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]

namespace Data
variable {I : Type u} [DecidableEq I] [Countable I]

/-- The actual joint Gaussian Fock vector, constructed only AFTER summability. -/
def vector (D : Data I) : FactorialFockMetric.Hilbert I :=
  ⟨fun d => scale d * coefficient D.kernel d, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, mul_pow, norm_scale_sq]
      using D.occupation_summable⟩

@[simp] theorem vector_apply (D : Data I) (d : Occupation I) :
    D.vector d = scale d * coefficient D.kernel d := rfl

theorem vector_norm_sq (D : Data I) :
    ‖D.vector‖ ^ 2 = ∑' d : Occupation I,
      (weight d : ℝ) * ‖coefficient D.kernel d‖ ^ 2 := by
  have h := (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) D.vector).tsum_eq
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, vector_apply, norm_mul, mul_pow,
    norm_scale_sq] using h.symm

theorem vector_norm_sq_le (D : Data I) : ‖D.vector‖ ^ 2 ≤ D.bound := by
  rw [D.vector_norm_sq]
  exact D.occupation_tsum_le

end Data
end D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
