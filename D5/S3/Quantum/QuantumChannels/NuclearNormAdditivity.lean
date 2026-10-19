/- GID: D5/S3/Quantum/QuantumChannels/NuclearNormAdditivity
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/NuclearNormAdditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real rectangular nuclear norm dual certificates and weighted rank-one additivity. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.QuadraticForms.WeightedGramContraction
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Operator.Extend

/-!
Real rectangular matrices use the actual CFC trace norm. The polar contraction
is obtained by descending the norm-preserving correspondence between the ranges
of a matrix and its positive square root, then extending by orthogonal projection.
In a spectral basis of the positive factor, Cauchy--Schwarz bounds every dual
pairing by its trace, and the polar contraction attains that trace. Applying
this attained duality to weighted rank-one sums connects the actual nuclear
norm to the common-contraction criterion for normalized Gram matrices.
-/

noncomputable section

open scoped BigOperators InnerProductSpace MatrixOrder
open Matrix

namespace D5.S3.Quantum.QuantumChannels.NuclearNormAdditivity

open D5.S3.Quantum.Foundation.FiniteTraceDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem contraction_factor_of_norm_eq
    (f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ m)
    (g : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n)
    (hn : ∀ v, ‖f v‖ = ‖g v‖) :
    ∃ Z : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m,
      ‖Z‖ ≤ 1 ∧ ∀ v, Z (g v) = f v := by
  classical
  let I : LinearMap.range g →ₗᵢ[ℝ] EuclideanSpace ℝ m :=
    f.extendOfIsometry g.surjective_rangeRestrict.denseRange hn
  let Z := I.toContinuousLinearMap.comp (LinearMap.range g).orthogonalProjectionOnto
  refine ⟨Z, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound Z (by norm_num : (0 : ℝ) ≤ 1)
    intro v
    change ‖I ((LinearMap.range g).orthogonalProjectionOnto v)‖ ≤ 1 * ‖v‖
    rw [I.norm_map, one_mul]
    exact (LinearMap.range g).norm_orthogonalProjectionOnto_apply_le v
  · intro v
    change I ((LinearMap.range g).orthogonalProjectionOnto
      (⟨g v, LinearMap.mem_range_self g v⟩ : LinearMap.range g)) = f v
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact f.extendOfIsometry_eq g.surjective_rangeRestrict.denseRange hn v

private theorem norm_eq_of_gram_eq (A : Matrix m n ℝ) (P : Matrix n n ℝ)
    (hg : Aᴴ * A = Pᴴ * P) (v : EuclideanSpace ℝ n) :
    ‖A.toEuclideanLin v‖ = ‖P.toEuclideanLin v‖ := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← LinearMap.adjoint_inner_right, ← LinearMap.adjoint_inner_right]
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change ⟪v, (Aᴴ.toEuclideanLin.comp A.toEuclideanLin) v⟫_ℝ =
    ⟪v, (Pᴴ.toEuclideanLin.comp P.toEuclideanLin) v⟫_ℝ
  rw [← toLpLin_mul_same, ← toLpLin_mul_same, hg]

private theorem eigen_apply (P : Matrix n n ℝ) (hP : P.PosSemidef) (i : n) :
    P.toEuclideanLin (hP.isHermitian.eigenvectorBasis i) =
      hP.isHermitian.eigenvalues i • hP.isHermitian.eigenvectorBasis i := by
  apply WithLp.ofLp_injective
  exact hP.isHermitian.mulVec_eigenvectorBasis i

/-- Every real rectangular matrix has a contractive polar factor. Its positive
factor is the CFC square root used in the definition of the actual trace norm. -/
theorem exists_real_rectangular_polar (A : Matrix m n ℝ) :
    ∃ Z : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m,
      ‖Z‖ ≤ 1 ∧
      (∀ v, Z ((CFC.sqrt (Aᴴ * A)).toEuclideanLin v) = A.toEuclideanLin v) ∧
      (∀ v, ‖A.toEuclideanLin v‖ = ‖(CFC.sqrt (Aᴴ * A)).toEuclideanLin v‖) := by
  let P := CFC.sqrt (Aᴴ * A)
  have hp : P.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hg : Aᴴ * A = Pᴴ * P := by
    rw [hp.isHermitian.eq]
    exact (CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self A).nonneg).symm
  have hn := norm_eq_of_gram_eq A P hg
  obtain ⟨Z, hZ, hz⟩ := contraction_factor_of_norm_eq A.toEuclideanLin P.toEuclideanLin hn
  exact ⟨Z, hZ, hz, hn⟩

/-- The real trace pairing with a continuous linear contraction. -/
def dualPairing (Z : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m)
    (A : Matrix m n ℝ) : ℝ :=
  (Z.toLinearMap.adjoint.comp A.toEuclideanLin).trace ℝ (EuclideanSpace ℝ n)

private theorem dualPairing_eq_sum (Z : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m)
    (A : Matrix m n ℝ) (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) :
    dualPairing Z A = ∑ i, ⟪Z (b i), A.toEuclideanLin (b i)⟫_ℝ := by
  unfold dualPairing
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    ContinuousLinearMap.coe_coe]

/-- The actual real rectangular CFC trace norm is attained by a contraction,
and dominates the trace pairing with every contraction. -/
theorem traceNorm_eq_max_dualPairing (A : Matrix m n ℝ) :
    ∃ Z : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m,
      ‖Z‖ ≤ 1 ∧ dualPairing Z A = traceNorm A ∧
      ∀ W : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m,
        ‖W‖ ≤ 1 → dualPairing W A ≤ traceNorm A := by
  let P := CFC.sqrt (Aᴴ * A)
  have hp : P.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  let b := hp.isHermitian.eigenvectorBasis
  let t := hp.isHermitian.eigenvalues
  have ht (i : n) : 0 ≤ t i := hp.eigenvalues_nonneg i
  have hb (i : n) : ‖b i‖ = 1 := b.orthonormal.1 i
  have hep (i : n) : P.toEuclideanLin (b i) = t i • b i := eigen_apply P hp i
  obtain ⟨Z, hZ, hz, hn⟩ := exists_real_rectangular_polar A
  have han (i : n) : ‖A.toEuclideanLin (b i)‖ = t i := by
    rw [hn, hep, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ht i), hb, mul_one]
  have htrace : traceNorm A = ∑ i, t i := by
    change P.trace = _
    exact hp.isHermitian.trace_eq_sum_eigenvalues
  have hbound (W : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m) (hW : ‖W‖ ≤ 1)
      (i : n) : ⟪W (b i), A.toEuclideanLin (b i)⟫_ℝ ≤ t i := by
    calc
      _ ≤ ‖W (b i)‖ * ‖A.toEuclideanLin (b i)‖ := real_inner_le_norm _ _
      _ ≤ (‖W‖ * ‖b i‖) * ‖A.toEuclideanLin (b i)‖ :=
        mul_le_mul_of_nonneg_right (W.le_opNorm _) (norm_nonneg _)
      _ = ‖W‖ * t i := by rw [hb, han, mul_one]
      _ ≤ t i := by simpa using mul_le_mul_of_nonneg_right hW (ht i)
  refine ⟨Z, hZ, ?_, ?_⟩
  · rw [dualPairing_eq_sum Z A b, htrace]
    apply Finset.sum_congr rfl
    intro i _
    have hm : t i • Z (b i) = A.toEuclideanLin (b i) := by
      rw [← map_smul, ← hep]
      exact hz (b i)
    by_cases hi : t i = 0
    · have ha : A.toEuclideanLin (b i) = 0 := norm_eq_zero.mp ((han i).trans hi)
      simp [ha, hi]
    · have hzn : ‖Z (b i)‖ = 1 := by
        have hh := congrArg norm hm
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ht i), han] at hh
        exact (mul_left_cancel₀ hi (hh.trans (mul_one _).symm))
      rw [← hm, real_inner_smul_right, real_inner_self_eq_norm_sq, hzn]
      ring
  · intro W hW
    rw [dualPairing_eq_sum W A b, htrace]
    exact Finset.sum_le_sum (fun i _ => hbound W hW i)

/-- A positively weighted sum of real rectangular rank-one matrices. -/
def weightedOuter {ι : Type*} [Fintype ι]
    (x : ι → EuclideanSpace ℝ m) (y : ι → EuclideanSpace ℝ n) (u : ι → ℝ) :
    Matrix m n ℝ := ∑ k, u k • Matrix.vecMulVec (x k).ofLp (y k).ofLp

private theorem toEuclideanLin_outer (x : EuclideanSpace ℝ m) (y : EuclideanSpace ℝ n) :
    (Matrix.vecMulVec x.ofLp y.ofLp).toEuclideanLin =
      (InnerProductSpace.rankOne ℝ x y).toLinearMap := by
  have h := congrArg Matrix.toEuclideanLin
    (InnerProductSpace.symm_toEuclideanLin_rankOne x y)
  simpa using h.symm

private theorem dualPairing_outer (Z : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m)
    (x : EuclideanSpace ℝ m) (y : EuclideanSpace ℝ n) :
    dualPairing Z (Matrix.vecMulVec x.ofLp y.ofLp) = ⟪x, Z y⟫_ℝ := by
  unfold dualPairing
  rw [toEuclideanLin_outer]
  have hc : Z.toLinearMap.adjoint.comp (InnerProductSpace.rankOne ℝ x y).toLinearMap =
      (InnerProductSpace.rankOne ℝ (Z.toLinearMap.adjoint x) y).toLinearMap := by
    ext v
    simp [InnerProductSpace.rankOne_apply]
  rw [hc, InnerProductSpace.trace_rankOne, LinearMap.adjoint_inner_right, real_inner_comm]
  rfl

private theorem dualPairing_weightedOuter {ι : Type*} [Fintype ι]
    (Z : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m)
    (x : ι → EuclideanSpace ℝ m) (y : ι → EuclideanSpace ℝ n) (u : ι → ℝ) :
    dualPairing Z (weightedOuter x y u) = ∑ k, u k * ⟪x k, Z (y k)⟫_ℝ := by
  change (LinearMap.trace ℝ (EuclideanSpace ℝ n))
    ((LinearMap.compRight ℝ Z.toLinearMap.adjoint)
      (Matrix.toEuclideanLin (∑ k, u k • Matrix.vecMulVec (x k).ofLp (y k).ofLp))) = _
  simp only [map_sum, map_smul, smul_eq_mul, LinearMap.compRight_apply]
  exact Finset.sum_congr rfl (fun k _ => congrArg (u k * ·) (dualPairing_outer Z (x k) (y k)))

omit [DecidableEq n] in
/-- The nuclear norm bound for a weighted rank-one expansion, with real
rectangular ambient spaces and nonnegative weights. -/
theorem traceNorm_weightedOuter_le {ι : Type*} [Fintype ι]
    (x : ι → EuclideanSpace ℝ m) (y : ι → EuclideanSpace ℝ n) (u : ι → ℝ)
    (hu : ∀ k, 0 ≤ u k) :
    traceNorm (weightedOuter x y u) ≤ ∑ k, u k * ‖x k‖ * ‖y k‖ := by
  classical
  obtain ⟨Z, hZ, hz, _⟩ := traceNorm_eq_max_dualPairing (weightedOuter x y u)
  rw [← hz, dualPairing_weightedOuter]
  apply Finset.sum_le_sum
  intro k _
  have hb : ⟪x k, Z (y k)⟫_ℝ ≤ ‖x k‖ * ‖y k‖ := by
    calc
      _ ≤ ‖x k‖ * ‖Z (y k)‖ := real_inner_le_norm _ _
      _ ≤ ‖x k‖ * (‖Z‖ * ‖y k‖) :=
        mul_le_mul_of_nonneg_left (Z.le_opNorm _) (norm_nonneg _)
      _ ≤ ‖x k‖ * (1 * ‖y k‖) := by gcongr
      _ = _ := by ring
  simpa only [← mul_assoc] using mul_le_mul_of_nonneg_left hb (hu k)

omit [DecidableEq n] in
/-- Kopel's nuclear-norm additivity lemma for nonzero real families in
arbitrary, possibly different, finite Euclidean dimensions. The norm on the
left is the CFC square-root trace norm, without an assumed duality principle. -/
theorem traceNorm_weightedOuter_eq_iff_normalized_gram {ι : Type*} [Fintype ι]
    (x : ι → EuclideanSpace ℝ m) (y : ι → EuclideanSpace ℝ n) (u : ι → ℝ)
    (hx : ∀ k, x k ≠ 0) (hy : ∀ k, y k ≠ 0) (hu : ∀ k, 0 < u k) :
    traceNorm (weightedOuter x y u) = ∑ k, u k * ‖x k‖ * ‖y k‖ ↔
      ∀ j k, ⟪‖x j‖⁻¹ • x j, ‖x k‖⁻¹ • x k⟫_ℝ =
        ⟪‖y j‖⁻¹ • y j, ‖y k‖⁻¹ • y k⟫_ℝ := by
  classical
  rw [← D5.S3.QuadraticForms.WeightedGramContraction.weighted_dual_saturation_iff_normalized_gram
    x y u hx hy hu]
  constructor
  · intro he
    obtain ⟨Z, hZ, hz, _⟩ := traceNorm_eq_max_dualPairing (weightedOuter x y u)
    refine ⟨Z, hZ, ?_⟩
    rw [← dualPairing_weightedOuter, hz, he]
  · rintro ⟨Z, hZ, he⟩
    obtain ⟨_, _, _, hbound⟩ := traceNorm_eq_max_dualPairing (weightedOuter x y u)
    apply le_antisymm (traceNorm_weightedOuter_le x y u (fun k => (hu k).le))
    have h := hbound Z hZ
    rwa [dualPairing_weightedOuter, he] at h

end D5.S3.Quantum.QuantumChannels.NuclearNormAdditivity
