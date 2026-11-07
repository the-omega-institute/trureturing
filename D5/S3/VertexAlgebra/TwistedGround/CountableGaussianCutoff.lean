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
import D5.S3.Quantum.Analysis.TraceClass.PowerSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-! Whole occupation sums and actual two-sided one-particle cutoffs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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
  let f : Finset I → Occupation I → ℂ := fun F d =>
    if d.support ⊆ F then occupationTerm A B d else 0
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (occupation_norm_summable A B)
    (f := f) (g := occupationTerm A B) ?_ ?_
  · convert h using 1
    funext F
    let S : Set (Occupation I) := {d | d.support ⊆ F}
    change (∑' d : S, occupationTerm A B d.val) = _
    calc
      _ = ∑' d, S.indicator (occupationTerm A B) d := tsum_subtype S _
      _ = _ := by
        apply tsum_congr
        intro d
        by_cases hd : d.support ⊆ F <;> simp [S, f, Set.indicator, hd]
  · intro d
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (commonBlock {d})] with F hF
    have hd : d.support ⊆ F :=
      (support_subset_commonBlock {d} d (Finset.mem_singleton_self d)).trans hF
    simp [f, hd]
  · exact Filter.Eventually.of_forall (fun F d => by
      dsimp [f]
      split_ifs <;> simp)

def occupationEquiv (F : Finset I) :
    {d : Occupation I // d.support ⊆ F} ≃ Occupation F where
  toFun d := restrictOccupation F d.val
  invFun d := ⟨d.mapDomain (fun i : F => i.val), by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hi)
    exact j.property⟩
  left_inv d := Subtype.ext (extend_restrict F d.val d.property)
  right_inv d := Finsupp.comapDomain_mapDomain (fun i : F => i.val) Subtype.val_injective d

private theorem occupationCutoff_eq_block (A B : Data I) (F : Finset I) :
    occupationCutoff A B F = ∑' d : Occupation F, (weight d : ℂ) *
      FactorialFockQuadraticEstimate.gaussianCoefficient (A.block F) d *
      FactorialFockQuadraticEstimate.gaussianCoefficient (B.block F) d := by
  let g : Occupation F → ℂ := fun d => (weight d : ℂ) *
    FactorialFockQuadraticEstimate.gaussianCoefficient (A.block F) d *
    FactorialFockQuadraticEstimate.gaussianCoefficient (B.block F) d
  calc
    occupationCutoff A B F = ∑' d : {d : Occupation I // d.support ⊆ F},
        g (occupationEquiv F d) := by
      apply tsum_congr
      intro d
      dsimp only [occupationTerm, occupationEquiv, g]
      rw [coefficient_on_block A.kernel F d.val d.property,
        coefficient_on_block B.kernel F d.val d.property,
        ← weight_restrict F d.val d.property]
      rfl
    _ = _ := (occupationEquiv F).tsum_eq g

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
  · change Tendsto (fun F => ∑' ij : I × I,
      if ij.1 ∈ F ∧ ij.2 ∈ F then (0 : ℝ) else ‖D.kernel ij.1 ij.2‖ ^ 2) atTop (𝓝 0)
    simpa only [tsum_zero] using h
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
      simp [hji, Ne.symm hji]
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    have hji : i ≠ j.val := fun h => hi (h ▸ j.property)
    simp [hji]

/-- The actual orthogonal projection J_F J_F† on the full one-particle space. -/
def coordinateProjection (F : Finset I) : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ) :=
  (Data.finiteInclusion F).toContinuousLinearMap.comp
    (ContinuousLinearMap.adjoint (Data.finiteInclusion F).toContinuousLinearMap)

theorem projection_apply (F : Finset I) (x : ℓ²(I, ℂ)) (i : I) :
    coordinateProjection F x i = if i ∈ F then x i else 0 := by
  change Data.finiteInclusion F
    (ContinuousLinearMap.adjoint (Data.finiteInclusion F).toContinuousLinearMap x) i = _
  rw [inclusion_apply]
  split_ifs <;> simp [Data.finiteInclusion_adjoint_apply]

theorem projection_norm_le (F : Finset I) : ‖coordinateProjection F‖ ≤ 1 := by
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
  by_cases hij : i = j
  · subst i
    by_cases hj : j ∈ F <;> simp [projection_apply, hj, lp.single_apply]
  · by_cases hi : i ∈ F <;> by_cases hj : j ∈ F <;>
      simp [projection_apply, hi, hj, lp.single_apply, Pi.single_apply, hij, Ne.symm hij]

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
      (T (lp.single 2 j (1 : ℂ)))).tsum_eq

theorem matrix_columns (T : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ))
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
  · calc
      (∑' j, ‖T (lp.single 2 j (1 : ℂ))‖ ^ 2) =
          ∑' ji : I × I, ‖T (lp.single 2 ji.1 (1 : ℂ)) ji.2‖ ^ 2 := by
        simpa only [column_square] using (hs.tsum_prod' hp.1).symm
      _ = ∑' ij : I × I, ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2 :=
        (Equiv.prodComm I I).tsum_eq
          (fun ij : I × I => ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2)

private theorem matrix_isHilbertSchmidt (T : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ))
    (hT : Summable (fun ij : I × I => ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2)) :
    IsHilbertSchmidt T := by
  let b := coordinateBasis I
  let e := Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  refine ⟨Set.range b, TraceClassFiniteBlocks.setBasis b, ?_⟩
  apply e.summable_iff.mp
  simpa only [Function.comp_def, TraceClassFiniteBlocks.setBasis_apply,
    Equiv.ofInjective_apply, e, b, coordinateBasis_apply] using (matrix_columns T hT).1

/-- Native Hilbert--Schmidt size, computed from the actual coordinate matrix. -/
def hsSize (T : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ)) : ℝ :=
  Real.sqrt (∑' ij : I × I, ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2)

theorem hs_basis_square (T : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ))
    (hT : Summable (fun ij : I × I => ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2)) :
    (∑' i, ‖T (TraceClassFiniteBlocks.setBasis (coordinateBasis I) i)‖ ^ 2) =
      ∑' ij : I × I, ‖T (lp.single 2 ij.2 (1 : ℂ)) ij.1‖ ^ 2 := by
  let b := coordinateBasis I
  let e := Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  rw [← e.tsum_eq]
  simpa only [TraceClassFiniteBlocks.setBasis_apply, Equiv.ofInjective_apply,
    e, b, coordinateBasis_apply] using (matrix_columns T hT).2

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

theorem error_summable (D : Data I) (F : Finset I) :
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
  simpa only [hs_compression_error, Real.sqrt_zero, Function.comp_def] using
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
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (compressed_hs_le A F)
        (Real.sqrt_nonneg _))
    _ = delta A B F := by simp only [X, Y, hs_compression_error, delta]

private theorem delta_tendsto (A B : Data I) :
    Tendsto (delta A B) atTop (𝓝 0) := by
  have hA := (Real.continuous_sqrt.tendsto 0).comp (matrixTailSquare_tendsto A)
  have hB := (Real.continuous_sqrt.tendsto 0).comp (matrixTailSquare_tendsto B)
  change Tendsto (fun F => Real.sqrt (matrixTailSquare A F) * hsSize B.oneParticle +
    hsSize A.oneParticle * Real.sqrt (matrixTailSquare B F)) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.sqrt_zero, zero_mul, mul_zero, add_zero] using
    (hA.mul_const (hsSize B.oneParticle)).add (hB.const_mul (hsSize A.oneParticle))

/-- Actual trace-norm convergence of the separately compressed product. -/
theorem cutoffProduct_tendsto (A B : Data I) :
    Tendsto (cutoffProduct A B) atTop (𝓝 (product A B)) := by
  have h := squeeze_zero (fun F => norm_nonneg (product A B - cutoffProduct A B F))
    (product_error_le A B) (delta_tendsto A B)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using h

theorem compressed_norm_le (D : Data I) (F : Finset I) :
    ‖compressed D F‖ ≤ D.q := by
  have hq := D.q_nonneg
  calc
    ‖compressed D F‖ ≤ (‖coordinateProjection F‖ * ‖D.oneParticle‖) *
        ‖coordinateProjection F‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * D.q) * 1 := by
      gcongr
      · exact projection_norm_le F
      · exact D.opNorm_le
      · exact projection_norm_le F
    _ = D.q := by ring

private theorem product_op_norm (A B : Data I) :
    ‖(product A B).val‖ ≤ A.q * B.q :=
  (norm_mul_le _ _).trans
    (mul_le_mul A.opNorm_le B.opNorm_le (norm_nonneg _) A.q_nonneg)

private theorem cutoff_op_norm (A B : Data I) (F : Finset I) :
    ‖(cutoffProduct A B F).val‖ ≤ A.q * B.q :=
  (norm_mul_le _ _).trans
    (mul_le_mul (compressed_norm_le A F) (compressed_norm_le B F)
      (norm_nonneg _) A.q_nonneg)

private theorem product_q_lt_one (A B : Data I) : A.q * B.q < 1 :=
  lt_of_le_of_lt ((mul_le_mul_of_nonneg_left B.q_lt_one.le A.q_nonneg).trans_eq
    (mul_one A.q)) A.q_lt_one

private theorem native_log_error (A B : Data I) (F : Finset I) :
    ‖TraceClassPowerSeries.traceLog (product A B) -
        TraceClassPowerSeries.traceLog (cutoffProduct A B F)‖ ≤
      delta A B F / (2 * (1 - A.q * B.q)) := by
  exact (TraceClassPowerSeries.traceLog_error_le _ _ (mul_nonneg A.q_nonneg B.q_nonneg)
    (product_q_lt_one A B) (product_op_norm A B) (cutoff_op_norm A B F)).trans
    (div_le_div_of_nonneg_right (product_error_le A B F) (by
      have := product_q_lt_one A B
      positivity))

/-- Trace-log cutoffs converge to the genuine original trace series. -/
theorem traceLog_cutoff_tendsto (A B : Data I) :
    Tendsto (fun F => TraceClassPowerSeries.traceLog (cutoffProduct A B F)) atTop
      (𝓝 (TraceClassPowerSeries.traceLog (product A B))) := by
  have hd := (delta_tendsto A B).div_const (2 * (1 - A.q * B.q))
  have h := squeeze_zero (fun F => norm_nonneg
    (TraceClassPowerSeries.traceLog (product A B) -
      TraceClassPowerSeries.traceLog (cutoffProduct A B F))) (native_log_error A B)
    (by simpa only [zero_div] using hd)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using h

def embedded (F : Finset I) (M : Matrix F F ℂ) : ℓ²(I, ℂ) →L[ℂ] ℓ²(I, ℂ) :=
  (Data.finiteInclusion F).toContinuousLinearMap.comp
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) M).comp
      (ContinuousLinearMap.adjoint (Data.finiteInclusion F).toContinuousLinearMap))

theorem compressed_embedded (D : Data I) (F : Finset I) :
    compressed D F = embedded F (D.block F) := by
  rw [embedded, ← D.compression_eq_matrix F]
  simp only [compressed, coordinateProjection, Data.compression,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

theorem embedded_mul (F : Finset I) (M N : Matrix F F ℂ) :
    embedded F (M * N) = embedded F M * embedded F N := by
  rw [embedded, map_mul]
  simp only [embedded, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc
    (ContinuousLinearMap.adjoint (Data.finiteInclusion F).toContinuousLinearMap)
    (Data.finiteInclusion F).toContinuousLinearMap,
    (Data.finiteInclusion F).adjoint_comp_self]
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

private theorem cutoff_power_embedded (A B : Data I) (F : Finset I) (m : ℕ) :
    (cutoffProduct A B F).val ^ (m + 1) =
      embedded F ((A.block F * B.block F) ^ (m + 1)) := by
  have hb : (cutoffProduct A B F).val = embedded F (A.block F * B.block F) := by
    rw [embedded_mul, ← compressed_embedded, ← compressed_embedded]
    rfl
  rw [hb]
  induction m with
  | zero => simp only [zero_add, pow_one]
  | succ m ih =>
      calc
        embedded F (A.block F * B.block F) ^ (m + 1 + 1) =
            embedded F (A.block F * B.block F) ^ (m + 1) *
              embedded F (A.block F * B.block F) := pow_succ _ _
        _ = embedded F ((A.block F * B.block F) ^ (m + 1)) *
              embedded F (A.block F * B.block F) := by rw [ih]
        _ = embedded F ((A.block F * B.block F) ^ (m + 1) *
              (A.block F * B.block F)) := (embedded_mul _ _ _).symm
        _ = _ := by rw [← pow_succ]

private theorem embedded_diagonal (F : Finset I) (M : Matrix F F ℂ) (i : I) :
    ⟪coordinateBasis I i, embedded F M (coordinateBasis I i)⟫_ℂ =
      if h : i ∈ F then M ⟨i, h⟩ ⟨i, h⟩ else 0 := by
  simp only [coordinateBasis_apply, lp.inner_single_left, RCLike.inner_apply,
    map_one, mul_one, embedded, ContinuousLinearMap.comp_apply]
  change Data.finiteInclusion F ((Matrix.toEuclideanCLM (𝕜 := ℂ) M)
    (ContinuousLinearMap.adjoint (Data.finiteInclusion F).toContinuousLinearMap
      (lp.single 2 i (1 : ℂ)))) i = _
  rw [inclusion_apply]
  by_cases hi : i ∈ F
  · rw [dite_eq_left hi, dite_eq_left hi]
    simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
      Data.finiteInclusion_adjoint_apply, lp.single_apply, Pi.single_apply]
    rw [Fintype.sum_eq_single (⟨i, hi⟩ : F)]
    · simp
    · intro j hj
      have hji : i ≠ j.val := fun h => hj (Subtype.ext h.symm)
      simp [hji, Ne.symm hji]
  · simp only [dite_eq_right hi]

private theorem embedded_trace (F : Finset I) (M : Matrix F F ℂ)
    (hM : IsTraceClass (embedded F M)) : trace (embedded F M) hM = Matrix.trace M := by
  rw [TraceClassFiniteBlocks.trace_on_basis (coordinateBasis I) hM]
  simp only [embedded_diagonal]
  have he : (∑' i : I, if h : i ∈ F then M ⟨i, h⟩ ⟨i, h⟩ else 0) =
      ∑' i : F, M i i := by
    let f : I → ℂ := fun i => if h : i ∈ F then M ⟨i, h⟩ ⟨i, h⟩ else 0
    calc
      _ = ∑' i, (F : Set I).indicator f i := by
        apply tsum_congr
        intro i
        by_cases hi : i ∈ F <;> simp [f, Set.indicator, hi]
      _ = ∑' i : F, f i := (tsum_subtype (F : Set I) f).symm
      _ = ∑' i : F, M i i := by
        apply tsum_congr
        intro i
        simp [f, i.property]
  rw [he, tsum_fintype]
  rfl

/-- Every positive power of the real compressed product has exactly the finite block trace. -/
theorem cutoff_power_trace (A B : Data I) (F : Finset I) (m : ℕ) :
    TraceClassPowerSeries.powerTrace (cutoffProduct A B F) m =
      Matrix.trace ((A.block F * B.block F) ^ (m + 1)) := by
  have he : (TraceClassPowerSeries.positivePower (cutoffProduct A B F) m).val =
      embedded F ((A.block F * B.block F) ^ (m + 1)) := by
    change (cutoffProduct A B F).val ^ m * (cutoffProduct A B F).val = _
    rw [← pow_succ, cutoff_power_embedded]
  exact (TraceClass.trace_transport he _).trans (embedded_trace _ _ _)

/-- The joint analytical bridge for the same two native data. No finite vacuum identity is a premise. -/
theorem native_cutoff_bridge (A B : Data I) :
    Summable (fun d => ‖occupationTerm A B d‖) ∧
    Tendsto (occupationCutoff A B) atTop (𝓝 (∑' d, occupationTerm A B d)) ∧
    Tendsto (fun F => hsSize (A.oneParticle - compressed A F)) atTop (𝓝 0) ∧
    Tendsto (fun F => hsSize (B.oneParticle - compressed B F)) atTop (𝓝 0) ∧
    (∀ F, ‖product A B - cutoffProduct A B F‖ ≤ delta A B F) ∧
    Tendsto (cutoffProduct A B) atTop (𝓝 (product A B)) ∧
    Summable (fun m => ‖TraceClassPowerSeries.logTerm (product A B) m‖) ∧
    (∀ F, Summable (fun m => ‖TraceClassPowerSeries.logTerm (cutoffProduct A B F) m‖)) ∧
    (∀ F m, ‖TraceClassPowerSeries.powerTrace (product A B) m -
        TraceClassPowerSeries.powerTrace (cutoffProduct A B F) m‖ ≤
      (m + 1 : ℝ) * (A.q * B.q) ^ m * delta A B F) ∧
    (∀ F, ‖TraceClassPowerSeries.traceLog (product A B) -
        TraceClassPowerSeries.traceLog (cutoffProduct A B F)‖ ≤
      delta A B F / (2 * (1 - A.q * B.q))) ∧
    Tendsto (fun F => TraceClassPowerSeries.traceLog (cutoffProduct A B F)) atTop
      (𝓝 (TraceClassPowerSeries.traceLog (product A B))) ∧
    (∀ F m, TraceClassPowerSeries.powerTrace (cutoffProduct A B F) m =
      Matrix.trace ((A.block F * B.block F) ^ (m + 1))) ∧
    (∀ F, occupationCutoff A B F = ∑' d : Occupation F, (weight d : ℂ) *
      FactorialFockQuadraticEstimate.gaussianCoefficient (A.block F) d *
      FactorialFockQuadraticEstimate.gaussianCoefficient (B.block F) d) := by
  refine ⟨occupation_norm_summable A B, occupationCutoff_tendsto A B,
    hs_compression_tendsto A, hs_compression_tendsto B, product_error_le A B,
    cutoffProduct_tendsto A B, ?_, ?_, ?_, native_log_error A B,
    traceLog_cutoff_tendsto A B, cutoff_power_trace A B, occupationCutoff_eq_block A B⟩
  · exact TraceClassPowerSeries.logTerm_norm_summable _ (mul_nonneg A.q_nonneg B.q_nonneg)
      (product_q_lt_one A B) (product_op_norm A B)
  · intro F
    exact TraceClassPowerSeries.logTerm_norm_summable _ (mul_nonneg A.q_nonneg B.q_nonneg)
      (product_q_lt_one A B) (cutoff_op_norm A B F)
  · intro F m
    exact (TraceClassPowerSeries.powerTrace_error_le _ _ (mul_nonneg A.q_nonneg B.q_nonneg)
      (product_op_norm A B) (cutoff_op_norm A B F) m).trans
      (mul_le_mul_of_nonneg_left (product_error_le A B F)
        (mul_nonneg (by positivity) (pow_nonneg (mul_nonneg A.q_nonneg B.q_nonneg) _)))

end D5.S3.VertexAlgebra.TwistedGround.CountableGaussianCutoff
