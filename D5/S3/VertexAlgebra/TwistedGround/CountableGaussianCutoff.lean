/- GID: D5/S3/VertexAlgebra/TwistedGround/CountableGaussianCutoff
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/CountableGaussianCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native whole-occupation and two-coordinate Gaussian cutoffs. -/

import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
import D5.S3.Quantum.Analysis.TraceClass.Pairing
import D5.S3.Quantum.Analysis.TraceClass.FiniteBlocks
import Mathlib.Analysis.Normed.Group.Tannery

/-! Whole occupation sums and actual two-sided one-particle cutoffs. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace lp ENNReal
open Filter Topology
open HilbertSchmidt

namespace D5.S3.VertexAlgebra.TwistedGround.CountableGaussianCutoff
open InfiniteGaussianFock
open FactorialFockMetric (Occupation weight)
universe u
variable {I : Type u} [DecidableEq I]

/-- The native holomorphic bilinear summand; no conjugation is inserted. -/
def occupationTerm (A B : Data I) (d : Occupation I) : ℂ :=
  (weight d : ℂ) * coefficient A.kernel d * coefficient B.kernel d

/-- Weighted square summability controls the absolute bilinear series. -/
theorem occupation_norm_summable (A B : Data I) :
    Summable (fun d => ‖occupationTerm A B d‖) := by
  have hs := (A.occupation_summable.add B.occupation_summable).div_const 2
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => ?_) hs
  simp only [occupationTerm, norm_mul, Complex.norm_natCast]
  have hw : (0 : ℝ) ≤ (weight d : ℝ) := Nat.cast_nonneg _
  have hh := mul_nonneg hw (sq_nonneg (‖coefficient A.kernel d‖ -
    ‖coefficient B.kernel d‖))
  nlinarith

/-- A finite coordinate set still contains infinitely many occupations. -/
def occupationCutoff (A B : Data I) (F : Finset I) : ℂ :=
  ∑' d : {d : Occupation I // d.support ⊆ F}, occupationTerm A B d.val

/-- Whole support cutoff, with no particle or degree restriction. -/
theorem occupationCutoff_tendsto (A B : Data I) :
    Tendsto (occupationCutoff A B) atTop (𝓝 (∑' d, occupationTerm A B d)) := by
  classical
  let f : Finset I → Occupation I → ℂ := fun F d =>
    if d.support ⊆ F then occupationTerm A B d else 0
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (occupation_norm_summable A B)
    (f := f) (g := occupationTerm A B) ?_ ?_
  · convert h using 1
    funext F
    exact (tsum_subtype (s := {d : Occupation I | d.support ⊆ F})
      (f := occupationTerm A B)).symm
  · intro d
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (commonBlock {d})] with F hF
    have hd : d.support ⊆ F :=
      (support_subset_commonBlock {d} d (Finset.mem_singleton_self d)).trans hF
    simp [f, hd]
  · exact Filter.Eventually.of_forall (fun F d => by
      dsimp [f]
      split_ifs <;> simp)

/-- The omitted mass is indexed by both matrix coordinates. -/
def matrixTailSquare (D : Data I) (F : Finset I) : ℝ :=
  ∑' ij : I × I, if ij.1 ∈ F ∧ ij.2 ∈ F then 0 else ‖D.kernel ij.1 ij.2‖ ^ 2

private theorem matrix_tail_summable (D : Data I) (F : Finset I) :
    Summable (fun ij : I × I =>
      if ij.1 ∈ F ∧ ij.2 ∈ F then (0 : ℝ) else ‖D.kernel ij.1 ij.2‖ ^ 2) := by
  apply Summable.of_nonneg_of_le _ _ D.square_summable
  · intro ij; split_ifs <;> positivity
  · intro ij; split_ifs <;> simp [Data.kernel, sq_nonneg]

/-- Unconditional double-square tails vanish on finite coordinate squares. -/
theorem matrixTailSquare_tendsto (D : Data I) :
    Tendsto (matrixTailSquare D) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) D.square_summable
    (f := fun F : Finset I => fun ij : I × I =>
      if ij.1 ∈ F ∧ ij.2 ∈ F then (0 : ℝ) else ‖D.kernel ij.1 ij.2‖ ^ 2)
    (g := fun _ => (0 : ℝ)) ?_ ?_
  · simpa only [matrixTailSquare, tsum_zero] using h
  · intro ij
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({ij.1, ij.2} : Finset I)] with F hF
    simp [hF (by simp : ij.1 ∈ ({ij.1, ij.2} : Finset I)),
      hF (by simp : ij.2 ∈ ({ij.1, ij.2} : Finset I))]
  · exact Filter.Eventually.of_forall (fun F ij => by
      split_ifs <;> simp [Data.kernel, sq_nonneg])

private theorem inclusion_apply (F : Finset I) (x : EuclideanSpace ℂ F) (i : I) :
    Data.finiteInclusion F x i = if h : i ∈ F then x ⟨i, h⟩ else 0 := by
  conv_lhs => rw [← (EuclideanSpace.basisFun F ℂ).sum_repr x]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, Data.finiteInclusion_single,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, lp.single_apply, Pi.single_apply]
  by_cases hi : i ∈ F
  · rw [dif_pos hi, Fintype.sum_eq_single (⟨i, hi⟩ : F)]
    · simp
    · intro j hj
      have hji : i ≠ j.val := fun h => hj (Subtype.ext h.symm)
      simp [hji]
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    have hji : i ≠ j.val := fun h => hi (h ▸ j.property)
    simp [hji]

/-- The actual orthogonal projection J_F J_F† on the full one-particle space. -/
def coordinateProjection (F : Finset I) : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ) :=
  (Data.finiteInclusion F).toContinuousLinearMap.comp
    (ContinuousLinearMap.adjoint (Data.finiteInclusion F).toContinuousLinearMap)

private theorem projection_apply (F : Finset I) (x : ℓ²(I, ℂ)) (i : I) :
    coordinateProjection F x i = if i ∈ F then x i else 0 := by
  simp only [coordinateProjection, ContinuousLinearMap.comp_apply, inclusion_apply]
  split_ifs <;> simp [Data.finiteInclusion_adjoint_apply]

private theorem projection_norm_le (F : Finset I) : ‖coordinateProjection F‖ ≤ 1 := by
  have hJ := (Data.finiteInclusion F).norm_toContinuousLinearMap_le
  have hP : ‖ContinuousLinearMap.adjoint (Data.finiteInclusion F).toContinuousLinearMap‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hJ
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hJ hP (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))

/-- Two-sided compression of each factor, before multiplying the factors. -/
def compressed (D : Data I) (F : Finset I) : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ) :=
  coordinateProjection F * D.oneParticle * coordinateProjection F

private theorem projection_single (F : Finset I) (j : I) :
    coordinateProjection F (lp.single 2 j (1 : ℂ)) =
      if j ∈ F then lp.single 2 j (1 : ℂ) else 0 := by
  apply lp.ext
  funext i
  simp only [projection_apply, lp.single_apply, Pi.single_apply]
  by_cases hj : j ∈ F <;> by_cases hi : i ∈ F <;> simp [hj, hi]
  all_goals aesop

private theorem compressed_entry (D : Data I) (F : Finset I) (i j : I) :
    compressed D F (lp.single 2 j (1 : ℂ)) i =
      if i ∈ F ∧ j ∈ F then D.kernel i j else 0 := by
  simp only [compressed, ContinuousLinearMap.mul_apply, projection_single]
  by_cases hj : j ∈ F
  · simp [hj, projection_apply, Data.kernel]
  · simp [hj]

private theorem column_square (T : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ)) (j : I) :
    (∑' i, ‖T (lp.single 2 j (1 : ℂ)) i‖ ^ 2) =
      ‖T (lp.single 2 j (1 : ℂ))‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
      (T (lp.single 2 j (1 : ℂ)))) .tsum_eq

private theorem matrix_columns (T : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ))
    (hT : Summable (fun ij : I × I => ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2)) :
    Summable (fun j => ‖T (lp.single 2 j (1 : ℂ))‖ ^ 2) ∧
      (∑' j, ‖T (lp.single 2 j (1 : ℂ))‖ ^ 2) =
        ∑' ij : I × I, ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2 := by
  have hs : Summable (fun ji : I × I =>
      ‖T (lp.single 2 ji.1 (1 : ℂ)) ji.2‖ ^ 2) :=
    (Equiv.prodComm I I).summable_iff.mpr hT
  have hp := (summable_prod_of_nonneg (fun ji => sq_nonneg
    ‖T (lp.single 2 ji.1 (1 : ℂ)) ji.2‖)).mp hs
  constructor
  · simpa only [column_square] using hp.2
  · rw [← (Equiv.prodComm I I).tsum_eq
      (fun ij : I × I => ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2),
      hs.tsum_prod']
    simp only [column_square]

private theorem matrix_isHilbertSchmidt (T : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ))
    (hT : Summable (fun ij : I × I => ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2)) :
    IsHilbertSchmidt T := by
  let b := coordinateBasis I
  let e := Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  refine ⟨Set.range b, TraceClassFiniteBlocks.setBasis b, ?_⟩
  apply e.summable_iff.mp
  simpa only [Function.comp_def, TraceClassFiniteBlocks.setBasis_apply,
    Equiv.ofInjective_apply, b, coordinateBasis_apply] using (matrix_columns T hT).1

/-- Native Hilbert--Schmidt size, computed from the actual coordinate matrix. -/
def hsSize (T : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ)) : ℝ :=
  Real.sqrt (∑' ij : I × I, ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2)

private theorem hs_basis_square (T : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ))
    (hT : Summable (fun ij : I × I => ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2)) :
    (∑' i, ‖T (TraceClassFiniteBlocks.setBasis (coordinateBasis I) i)‖ ^ 2) =
      ∑' ij : I × I, ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2 := by
  let b := coordinateBasis I
  let e := Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  rw [← e.tsum_eq]
  simpa only [TraceClassFiniteBlocks.setBasis_apply, Equiv.ofInjective_apply,
    b, coordinateBasis_apply] using (matrix_columns T hT).2

private theorem compressed_summable (D : Data I) (F : Finset I) :
    Summable (fun ij : I × I =>
      ‖compressed D F (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ D.square_summable
  intro ij
  rw [compressed_entry]
  split_ifs <;> simp [Data.kernel, sq_nonneg]

private theorem error_entry (D : Data I) (F : Finset I) (i j : I) :
    ‖(D.oneParticle - compressed D F) (lp.single 2 j (1 : ℂ)) i‖ ^ 2 =
      if i ∈ F ∧ j ∈ F then 0 else ‖D.kernel i j‖ ^ 2 := by
  simp only [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply, compressed_entry]
  split_ifs <;> simp [Data.kernel]

private theorem error_summable (D : Data I) (F : Finset I) :
    Summable (fun ij : I × I =>
      ‖(D.oneParticle - compressed D F) (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2) := by
  simpa only [error_entry] using matrix_tail_summable D F

/-- The actual HS error is the square root of the omitted double matrix mass. -/
theorem hs_compression_error (D : Data I) (F : Finset I) :
    hsSize (D.oneParticle - compressed D F) = Real.sqrt (matrixTailSquare D F) := by
  simp only [hsSize, error_entry, matrixTailSquare]

private theorem compressed_hs_le (D : Data I) (F : Finset I) :
    hsSize (compressed D F) ≤ hsSize D.oneParticle := by
  apply Real.sqrt_le_sqrt
  apply (compressed_summable D F).tsum_le_tsum _ D.square_summable
  intro ij
  rw [compressed_entry]
  split_ifs <;> simp [Data.kernel, sq_nonneg]

/-- Genuine HS errors converge to zero, including zero-dimensional modes. -/
theorem hs_compression_tendsto (D : Data I) :
    Tendsto (fun F => hsSize (D.oneParticle - compressed D F)) atTop (𝓝 0) := by
  simpa only [hs_compression_error, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp (matrixTailSquare_tendsto D)

private theorem hs_product_bound (R S : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ))
    (hR : Summable (fun ij : I × I => ‖R (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2))
    (hS : Summable (fun ij : I × I => ‖S (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2))
    (hRS : IsTraceClass (R * S)) :
    traceNorm (R * S) hRS ≤ hsSize R * hsSize S := by
  have h := traceNorm_mul_le_of_isHilbertSchmidt
    (matrix_isHilbertSchmidt R hR) (matrix_isHilbertSchmidt S hS) hRS
    (TraceClassFiniteBlocks.setBasis (coordinateBasis I))
  simpa only [hs_basis_square R hR, hs_basis_square S hS, hsSize] using h

/-- Genuine trace-class product of the two original operators. -/
def product (A B : Data I) : TraceClass ℓ²(I, ℂ) :=
  TraceClass.ofOperator (A.oneParticle * B.oneParticle)
    (isTraceClass_mul_of_isHilbertSchmidt
      (matrix_isHilbertSchmidt A.oneParticle A.square_summable)
      (matrix_isHilbertSchmidt B.oneParticle B.square_summable))

/-- This is (P A P)(P B P), rather than P(AB)P. -/
def cutoffProduct (A B : Data I) (F : Finset I) : TraceClass ℓ²(I, ℂ) :=
  TraceClass.ofOperator (compressed A F * compressed B F)
    (isTraceClass_mul_of_isHilbertSchmidt
      (matrix_isHilbertSchmidt _ (compressed_summable A F))
      (matrix_isHilbertSchmidt _ (compressed_summable B F)))

/-- The quantitative error uses the actual two-sided HS tails. -/
def delta (A B : Data I) (F : Finset I) : ℝ :=
  Real.sqrt (matrixTailSquare A F) * hsSize B.oneParticle +
    hsSize A.oneParticle * Real.sqrt (matrixTailSquare B F)

/-- Noncommuting product decomposition followed by the genuine HS ideal bound. -/
theorem product_error_le (A B : Data I) (F : Finset I) :
    ‖product A B - cutoffProduct A B F‖ ≤ delta A B F := by
  let X := A.oneParticle - compressed A F
  let Y := B.oneParticle - compressed B F
  have hX := matrix_isHilbertSchmidt X (error_summable A F)
  have hY := matrix_isHilbertSchmidt Y (error_summable B F)
  let U : TraceClass ℓ²(I, ℂ) := TraceClass.ofOperator (X * B.oneParticle)
    (isTraceClass_mul_of_isHilbertSchmidt hX
      (matrix_isHilbertSchmidt _ B.square_summable))
  let V : TraceClass ℓ²(I, ℂ) := TraceClass.ofOperator (compressed A F * Y)
    (isTraceClass_mul_of_isHilbertSchmidt
      (matrix_isHilbertSchmidt _ (compressed_summable A F)) hY)
  have he : product A B - cutoffProduct A B F = U + V := by
    apply Subtype.ext
    change A.oneParticle * B.oneParticle - compressed A F * compressed B F =
      (A.oneParticle - compressed A F) * B.oneParticle +
        compressed A F * (B.oneParticle - compressed B F)
    noncomm_ring
  have hU : ‖U‖ ≤ hsSize X * hsSize B.oneParticle :=
    hs_product_bound _ _ (error_summable A F) B.square_summable _
  have hV : ‖V‖ ≤ hsSize (compressed A F) * hsSize Y :=
    hs_product_bound _ _ (compressed_summable A F) (error_summable B F) _
  rw [he]
  calc
    ‖U + V‖ ≤ ‖U‖ + ‖V‖ := norm_add_le _ _
    _ ≤ hsSize X * hsSize B.oneParticle + hsSize (compressed A F) * hsSize Y :=
      add_le_add hU hV
    _ ≤ hsSize X * hsSize B.oneParticle + hsSize A.oneParticle * hsSize Y :=
      add_le_add_left (mul_le_mul_of_nonneg_right (compressed_hs_le A F)
        (Real.sqrt_nonneg _)) _
    _ = delta A B F := by simp only [X, Y, hs_compression_error, delta]

private theorem delta_tendsto (A B : Data I) :
    Tendsto (delta A B) atTop (𝓝 0) := by
  have hA := (Real.continuous_sqrt.tendsto 0).comp (matrixTailSquare_tendsto A)
  have hB := (Real.continuous_sqrt.tendsto 0).comp (matrixTailSquare_tendsto B)
  simpa only [delta, Real.sqrt_zero, zero_mul, mul_zero, add_zero] using
    (hA.mul_const (hsSize B.oneParticle)).add (hB.const_mul (hsSize A.oneParticle))

/-- Actual trace-norm convergence of the separately compressed product. -/
theorem cutoffProduct_tendsto (A B : Data I) :
    Tendsto (cutoffProduct A B) atTop (𝓝 (product A B)) := by
  have h := squeeze_zero (fun F => norm_nonneg (product A B - cutoffProduct A B F))
    (product_error_le A B) (delta_tendsto A B)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using h

end D5.S3.VertexAlgebra.TwistedGround.CountableGaussianCutoff
