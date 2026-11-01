/- GID: D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/GaussianCoefficientOperator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The joint Gaussian vector gives a bounded source-to-output coefficient operator. -/

import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
import D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis

/-!
Synthesis uses the existing same-space ColumnSynthesis theorem.
Its basis-range reindexing is reused from FockAttenuator.CoefficientOperator.
That supplier retains the Physlib attribution and licence notices carried by
TraceClass.HilbertSchmidt, adopted from Tom Ole Diem's Physlib at
`b9043cc548ef6d63a28454cf3a57fb12a0c2e142` under Apache-2.0; see
`docs/reports/quantum-hs-suppliers/physlib-LICENSE.txt`.
The ambient space is the orthogonal sum of source and output Fock coordinates.
The resulting actual source-to-output map is P_out A J_src.
This module does not identify that map with a native field Y.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProductSpace lp ENNReal
open ComplexConjugate
open Filter Topology

namespace D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientOperator

open InfiniteGaussianFock
open FactorialFockMetric (Occupation weight scale Hilbert embedding hilbertBasis)

universe u v w
variable {S : Type u} {T : Type v}

/-- The exact occupation splitting bijection, including zero and repeated modes. -/
abbrev splitOccupation : Occupation (S ⊕ T) ≃ Occupation S × Occupation T :=
  Finsupp.sumFinsuppEquivProdFinsupp

def joinOccupation (d : Occupation S) (h : Occupation T) : Occupation (S ⊕ T) :=
  splitOccupation.symm (d, h)

theorem weight_join (d : Occupation S) (h : Occupation T) :
    weight (joinOccupation d h) = weight d * weight h := by
  exact Finsupp.prod_sumElim d h (fun _ n => n.factorial)

theorem scale_join (d : Occupation S) (h : Occupation T) :
    scale (joinOccupation d h) = scale d * scale h := by
  unfold scale
  rw [weight_join, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

variable [DecidableEq S] [DecidableEq T]

/-- Output row h, source column d. The holomorphic K has no conjugated transpose. -/
def matrixCoefficient (D : Data (S ⊕ T)) (h : Occupation T) (d : Occupation S) : ℂ :=
  scale d * scale h * coefficient D.kernel (joinOccupation d h)

theorem matrixCoefficient_eq_vector (D : Data (S ⊕ T))
    (d : Occupation S) (h : Occupation T) :
    matrixCoefficient D h d = D.vector (joinOccupation d h) := by
  change scale d * scale h * coefficient D.kernel (joinOccupation d h) =
    scale (joinOccupation d h) * coefficient D.kernel (joinOccupation d h)
  rw [scale_join]

theorem matrixCoefficient_square (D : Data (S ⊕ T))
    (d : Occupation S) (h : Occupation T) :
    ‖matrixCoefficient D h d‖ ^ 2 = (weight (joinOccupation d h) : ℝ) *
      ‖coefficient D.kernel (joinOccupation d h)‖ ^ 2 := by
  rw [matrixCoefficient_eq_vector]
  change ‖scale (joinOccupation d h) * coefficient D.kernel (joinOccupation d h)‖ ^ 2 = _
  rw [norm_mul, mul_pow, norm_scale_sq]

/-- Reindex the proved WHOLE joint sum through an actual bijection. -/
theorem matrix_square_summable (D : Data (S ⊕ T)) :
    Summable (fun p : Occupation S × Occupation T => ‖matrixCoefficient D p.2 p.1‖ ^ 2) := by
  have h := (splitOccupation.symm :
    Occupation S × Occupation T ≃ Occupation (S ⊕ T)).summable_iff.mpr D.occupation_summable
  simpa only [matrixCoefficient_square, joinOccupation, Function.comp_def, Prod.mk.eta] using h

theorem matrix_square_sum (D : Data (S ⊕ T)) :
    (∑' p : Occupation S × Occupation T, ‖matrixCoefficient D p.2 p.1‖ ^ 2) =
      ‖D.vector‖ ^ 2 := by
  have hv := (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) D.vector).tsum_eq
  have he : (∑' p : Occupation S × Occupation T, ‖matrixCoefficient D p.2 p.1‖ ^ 2) =
      ∑' a : Occupation (S ⊕ T), ‖D.vector a‖ ^ 2 := by
    simpa only [matrixCoefficient_eq_vector, joinOccupation, Function.comp_def, Prod.mk.eta]
      using (splitOccupation.symm : Occupation S × Occupation T ≃ Occupation (S ⊕ T)).tsum_eq
        (fun a => ‖D.vector a‖ ^ 2)
  exact he.trans (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hv)

/-- A genuine output l2 vector for each source occupation. -/
def column (D : Data (S ⊕ T)) (d : Occupation S) : Hilbert T :=
  ⟨fun h => matrixCoefficient D h d, by
    apply memℓp_gen
    have h := (summable_prod_of_nonneg
      (fun p : Occupation S × Occupation T => sq_nonneg ‖matrixCoefficient D p.2 p.1‖)).mp
        (matrix_square_summable D)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.1 d⟩

@[simp] theorem column_apply (D : Data (S ⊕ T)) (d : Occupation S) (h : Occupation T) :
    column D d h = matrixCoefficient D h d := rfl

theorem column_norm_sq (D : Data (S ⊕ T)) (d : Occupation S) :
    ‖column D d‖ ^ 2 = ∑' h : Occupation T, ‖matrixCoefficient D h d‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, column_apply] using
    (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (column D d)).tsum_eq.symm

theorem column_square_summable (D : Data (S ⊕ T)) :
    Summable (fun d : Occupation S => ‖column D d‖ ^ 2) := by
  simp_rw [column_norm_sq]
  exact ((summable_prod_of_nonneg (fun p : Occupation S × Occupation T =>
    sq_nonneg ‖matrixCoefficient D p.2 p.1‖)).mp (matrix_square_summable D)).2

theorem column_square_sum (D : Data (S ⊕ T)) :
    (∑' d : Occupation S, ‖column D d‖ ^ 2) = ‖D.vector‖ ^ 2 := by
  simp_rw [column_norm_sq]
  rw [← (matrix_square_summable D).tsum_prod]
  exact (matrix_square_sum D)

/-- Natural orthogonal sum of source and output occupation coordinates. -/
abbrev Ambient (S : Type u) (T : Type v) := ℓ²(Occupation S ⊕ Occupation T, ℂ)

def sourceInclusion : Hilbert S →ₗᵢ[ℂ] Ambient S T :=
  coordinateInclusion Sum.inl Sum.inl_injective

def outputInclusion : Hilbert T →ₗᵢ[ℂ] Ambient S T :=
  coordinateInclusion Sum.inr Sum.inr_injective

def blockColumn (D : Data (S ⊕ T)) : Occupation S ⊕ Occupation T → Ambient S T :=
  Sum.elim (fun d => outputInclusion (column D d)) (fun _ => 0)

/-- Only source columns are nonzero; their mass is exactly the joint mass. -/
theorem blockColumn_hasSum (D : Data (S ⊕ T)) :
    HasSum (fun a : Occupation S ⊕ Occupation T => ‖blockColumn D a‖ ^ 2)
      (‖D.vector‖ ^ 2) := by
  have h₁ : HasSum (fun d : Occupation S =>
      ‖blockColumn D (Sum.inl d)‖ ^ 2) (‖D.vector‖ ^ 2) := by
    simpa only [blockColumn, Sum.elim_inl, LinearIsometry.norm_map, (column_square_sum D)]
      using (column_square_summable D).hasSum
  have h₂ : HasSum (fun h : Occupation T =>
      ‖blockColumn D (Sum.inr h)‖ ^ 2) 0 := by
    simp only [blockColumn, Sum.elim_inr, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact hasSum_zero
  simpa only [add_zero] using
    (HasSum.sum (f := fun a : Occupation S ⊕ Occupation T => ‖blockColumn D a‖ ^ 2) h₁ h₂)

/-- The canonical SAME-SPACE supplier is applied after the precise basis-range
reindexing used in CoefficientOperator. This is not a heterogeneous invocation. -/
theorem exists_block_operator (D : Data (S ⊕ T)) :
    ∃ A : Ambient S T →L[ℂ] Ambient S T,
      (∀ a, A (coordinateBasis (Occupation S ⊕ Occupation T) a) = blockColumn D a) ∧
      HilbertSchmidt.IsHilbertSchmidt A ∧
      (∑' a : Occupation S ⊕ Occupation T,
        ‖A (coordinateBasis (Occupation S ⊕ Occupation T) a)‖ ^ 2) = ‖D.vector‖ ^ 2 ∧
      ‖A‖ ≤ Real.sqrt (‖D.vector‖ ^ 2) := by
  let b := coordinateBasis (Occupation S ⊕ Occupation T)
  let w : Set (Ambient S T) := Set.range b
  let e : (Occupation S ⊕ Occupation T) ≃ w :=
    Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  have hw : Orthonormal ℂ (Subtype.val : w → Ambient S T) :=
    b.orthonormal.toSubtypeRange
  have hspan : (Submodule.span ℂ (Set.range
      (Subtype.val : w → Ambient S T))).topologicalClosure = ⊤ := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, w] using b.dense_span
  let bw : HilbertBasis w ℂ (Ambient S T) := HilbertBasis.mk hw hspan.ge
  have hbw (i : w) : bw i = (i : Ambient S T) :=
    congrFun (HilbertBasis.coe_mk hw hspan.ge) i
  have hre : Summable (fun i : w => ‖blockColumn D (e.symm i)‖ ^ 2) :=
    e.symm.summable_iff.mpr (blockColumn_hasSum D).summable
  obtain ⟨A, hA, hhs, _, hnorm⟩ :=
    HilbertSchmidt.exists_hilbertSchmidt_of_square_summable_columns bw
      (fun i => blockColumn D (e.symm i)) hre
  have hcol (a : Occupation S ⊕ Occupation T) : A (b a) = blockColumn D a := by
    have h := hA (e a)
    rw [hbw, e.symm_apply_apply] at h
    exact h
  have hmass : (∑' i : w, ‖blockColumn D (e.symm i)‖ ^ 2) = ‖D.vector‖ ^ 2 :=
    (e.symm.tsum_eq (fun a => ‖blockColumn D a‖ ^ 2)).trans (blockColumn_hasSum D).tsum_eq
  refine ⟨A, hcol, hhs, ?_, ?_⟩
  · change (∑' a, ‖A (b a)‖ ^ 2) = ‖D.vector‖ ^ 2
    simpa only [hcol] using (blockColumn_hasSum D).tsum_eq
  · simpa only [hmass] using hnorm

def blockOperator (D : Data (S ⊕ T)) : Ambient S T →L[ℂ] Ambient S T :=
  (exists_block_operator D).choose

theorem blockOperator_column (D : Data (S ⊕ T)) (a : Occupation S ⊕ Occupation T) :
    blockOperator D (coordinateBasis (Occupation S ⊕ Occupation T) a) = blockColumn D a :=
  (exists_block_operator D).choose_spec.1 a

theorem blockOperator_hilbertSchmidt (D : Data (S ⊕ T)) :
    HilbertSchmidt.IsHilbertSchmidt (blockOperator D) :=
  (exists_block_operator D).choose_spec.2.1

/-- Restrict the source block and project the output block. Domain and codomain
are the actual, generally different, occupation Hilbert spaces. -/
def coefficientOperator (D : Data (S ⊕ T)) : Hilbert S →L[ℂ] Hilbert T :=
  (ContinuousLinearMap.adjoint (outputInclusion (S := S) (T := T)).toContinuousLinearMap).comp
    ((blockOperator D).comp (sourceInclusion (S := S) (T := T)).toContinuousLinearMap)

@[simp] theorem coefficientOperator_column (D : Data (S ⊕ T)) (d : Occupation S) :
    coefficientOperator D (hilbertBasis S d) = column D d := by
  have hsrc : sourceInclusion (S := S) (T := T) (hilbertBasis S d) =
      coordinateBasis (Occupation S ⊕ Occupation T) (Sum.inl d) := by
    have hb : hilbertBasis S d = lp.single 2 d (1 : ℂ) := (hilbertBasis S).repr_self d
    rw [hb]
    change coordinateInclusion Sum.inl Sum.inl_injective (lp.single 2 d (1 : ℂ)) = _
    rw [coordinateInclusion_single, coordinateBasis_apply]
  change ContinuousLinearMap.adjoint
    (outputInclusion (S := S) (T := T)).toContinuousLinearMap
      (blockOperator D (sourceInclusion (S := S) (T := T) (hilbertBasis S d))) = _
  rw [hsrc, blockOperator_column]
  change ((outputInclusion (S := S) (T := T)).toContinuousLinearMap.adjoint ∘L
    (outputInclusion (S := S) (T := T)).toContinuousLinearMap) (column D d) = _
  rw [LinearIsometry.adjoint_comp_self]
  rfl

/-- Exact ON matrix entries of the genuine source-to-output operator. -/
theorem coefficientOperator_matrix (D : Data (S ⊕ T))
    (d : Occupation S) (h : Occupation T) :
    inner ℂ (hilbertBasis T h) (coefficientOperator D (hilbertBasis S d)) =
      scale d * scale h * coefficient D.kernel (joinOccupation d h) := by
  rw [coefficientOperator_column]
  exact ((hilbertBasis T).repr_apply_apply (column D d) h).symm

theorem coefficientOperator_single (D : Data (S ⊕ T)) (d : Occupation S) (c : ℂ) :
    coefficientOperator D (lp.single 2 d c) = c • column D d := by
  have hb : hilbertBasis S d = lp.single 2 d (1 : ℂ) :=
    (hilbertBasis S).repr_self d
  have hs : (lp.single 2 d c : Hilbert S) = c • hilbertBasis S d := by
    rw [hb]
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : Occupation S => ℂ) 2 d c (1 : ℂ))
  rw [hs, map_smul, coefficientOperator_column]

/-- Exact square sum, not an assumed Hilbert-Schmidt norm certificate. -/
theorem coefficientOperator_square_sum (D : Data (S ⊕ T)) :
    (∑' d : Occupation S, ‖coefficientOperator D (hilbertBasis S d)‖ ^ 2) = ‖D.vector‖ ^ 2 := by
  simp_rw [coefficientOperator_column]
  exact (column_square_sum D)

/-- Bound on the whole squared Hilbert-Schmidt mass, over every source occupation. -/
theorem coefficientOperator_square_sum_le (D : Data (S ⊕ T)) :
    (∑' d : Occupation S, ‖coefficientOperator D (hilbertBasis S d)‖ ^ 2) ≤
      Real.exp (D.massBound / (2 * (1 - D.q ^ 2))) := by
  rw [coefficientOperator_square_sum, ← matrix_square_sum]
  simp_rw [matrixCoefficient_square]
  exact ((splitOccupation.symm : Occupation S × Occupation T ≃ Occupation (S ⊕ T)).tsum_eq
    (fun a => (weight a : ℝ) * ‖coefficient D.kernel a‖ ^ 2)).trans_le D.occupation_tsum_le

/-- The natural zero extension of the actual coefficient operator is precisely
the synthesized Hilbert-Schmidt endomorphism (both extra blocks vanish). -/
theorem coefficientOperator_zero_extension (D : Data (S ⊕ T)) :
    (outputInclusion (S := S) (T := T)).toContinuousLinearMap.comp
      ((coefficientOperator D).comp
        (ContinuousLinearMap.adjoint (sourceInclusion (S := S) (T := T)).toContinuousLinearMap)) =
      blockOperator D := by
  have hprojection (x : Ambient S T) (d : Occupation S) :
      ContinuousLinearMap.adjoint
        (sourceInclusion (S := S) (T := T)).toContinuousLinearMap x d =
        x (Sum.inl d) := by
    have h := ContinuousLinearMap.adjoint_inner_right
      (sourceInclusion (S := S) (T := T)).toContinuousLinearMap
      (lp.single 2 d (1 : ℂ)) x
    change ⟪lp.single 2 d (1 : ℂ),
        ContinuousLinearMap.adjoint
          (sourceInclusion (S := S) (T := T)).toContinuousLinearMap x⟫_ℂ =
      ⟪coordinateInclusion Sum.inl Sum.inl_injective (lp.single 2 d (1 : ℂ)), x⟫_ℂ at h
    rw [coordinateInclusion_single] at h
    simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using h
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro a
  apply ContinuousLinearMap.ext
  intro c
  cases a with
  | inl d =>
    have hs : (lp.single 2 (Sum.inl d) c : Ambient S T) =
        c • coordinateBasis (Occupation S ⊕ Occupation T) (Sum.inl d) := by
      rw [coordinateBasis_apply]
      simpa only [smul_eq_mul, mul_one] using
        (lp.single_smul (E := fun _ : Occupation S ⊕ Occupation T => ℂ)
          2 (Sum.inl d) c (1 : ℂ))
    have hp : ContinuousLinearMap.adjoint
        (sourceInclusion (S := S) (T := T)).toContinuousLinearMap
        (lp.single 2 (Sum.inl d) c) = lp.single 2 d c := by
      apply lp.ext
      funext e
      simp [hprojection, lp.single_apply, Pi.single_apply]
    change outputInclusion ((coefficientOperator D)
      (ContinuousLinearMap.adjoint (sourceInclusion (S := S) (T := T)).toContinuousLinearMap
        (lp.single 2 (Sum.inl d) c))) = blockOperator D (lp.single 2 (Sum.inl d) c)
    rw [hp, coefficientOperator_single, hs]
    simp only [map_smul, blockOperator_column, blockColumn, Sum.elim_inl]
  | inr h =>
    have hp : ContinuousLinearMap.adjoint
        (sourceInclusion (S := S) (T := T)).toContinuousLinearMap
        (lp.single 2 (Sum.inr h) c) = 0 := by
      apply lp.ext
      funext d
      simp [hprojection, lp.single_apply, Pi.single_apply]
    have hs : (lp.single 2 (Sum.inr h) c : Ambient S T) =
        c • coordinateBasis (Occupation S ⊕ Occupation T) (Sum.inr h) := by
      rw [coordinateBasis_apply]
      simpa only [smul_eq_mul, mul_one] using
        (lp.single_smul (E := fun _ : Occupation S ⊕ Occupation T => ℂ)
          2 (Sum.inr h) c (1 : ℂ))
    change outputInclusion ((coefficientOperator D)
      (ContinuousLinearMap.adjoint (sourceInclusion (S := S) (T := T)).toContinuousLinearMap
        (lp.single 2 (Sum.inr h) c))) = blockOperator D (lp.single 2 (Sum.inr h) c)
    rw [hp, map_zero, map_zero, hs]
    simp only [map_smul, blockOperator_column, blockColumn, Sum.elim_inr, smul_zero]

/-- This is the Hilbert-Schmidt assertion in the existing same-space API.
Together with the exact column square sum it describes the heterogeneous map. -/
theorem coefficientOperator_hilbertSchmidt_extension (D : Data (S ⊕ T)) :
    HilbertSchmidt.IsHilbertSchmidt
      ((outputInclusion (S := S) (T := T)).toContinuousLinearMap.comp
        ((coefficientOperator D).comp
          (ContinuousLinearMap.adjoint
            (sourceInclusion (S := S) (T := T)).toContinuousLinearMap))) := by
  rw [coefficientOperator_zero_extension]
  exact (blockOperator_hilbertSchmidt D)

theorem coefficientOperator_norm_le (D : Data (S ⊕ T)) :
    ‖coefficientOperator D‖ ≤ Real.exp (D.massBound / (4 * (1 - D.q ^ 2))) := by
  have hJ := (sourceInclusion (S := S) (T := T)).norm_toContinuousLinearMap_le
  have hP : ‖ContinuousLinearMap.adjoint
      (outputInclusion (S := S) (T := T)).toContinuousLinearMap‖ ≤ 1 := by
    simpa only [(ContinuousLinearMap.adjoint).norm_map] using
      (outputInclusion (S := S) (T := T)).norm_toContinuousLinearMap_le
  have hA := (exists_block_operator D).choose_spec.2.2.2
  have hb : ‖coefficientOperator D‖ ≤ Real.sqrt (‖D.vector‖ ^ 2) := by
    calc
      _ ≤ ‖ContinuousLinearMap.adjoint
          (outputInclusion (S := S) (T := T)).toContinuousLinearMap‖ *
          ‖(blockOperator D).comp (sourceInclusion (S := S) (T := T)).toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (Real.sqrt (‖D.vector‖ ^ 2) * 1) :=
        mul_le_mul hP ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hA hJ (norm_nonneg _) (Real.sqrt_nonneg _)))
          (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  apply hb.trans
  calc
    Real.sqrt (‖D.vector‖ ^ 2) ≤ Real.sqrt D.bound := by
      apply Real.sqrt_le_sqrt
      rw [← coefficientOperator_square_sum]
      exact coefficientOperator_square_sum_le D
    _ = Real.exp (D.massBound / (4 * (1 - D.q ^ 2))) := by
      rw [Data.bound, ← Real.exp_half]
      congr 1
      rw [div_div]
      congr 1
      ring

/-- Exact polynomial action in the existing factorial Hilbert embedding. -/
theorem coefficientOperator_polynomial (D : Data (S ⊕ T)) (p : MvPolynomial S ℂ) :
    coefficientOperator D (embedding S p) =
      ∑ d ∈ p.support, (scale d * p.coeff d) • column D d := by
  nth_rw 1 [p.as_sum]
  simp only [map_sum, FactorialFockMetric.embedding_monomial, map_smul,
    coefficientOperator_column]

/-- Unique extension from the dense Finsupp/ON polynomial subspace. -/
theorem coefficientOperator_unique (D : Data (S ⊕ T))
    (C : Hilbert S →L[ℂ] Hilbert T) (hC : ∀ d, C (hilbertBasis S d) = column D d) :
    C = coefficientOperator D := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro d
  apply ContinuousLinearMap.ext
  intro c
  have hs : (lp.single 2 d c : Hilbert S) = c • hilbertBasis S d := by
    have hb : hilbertBasis S d = lp.single 2 d (1 : ℂ) := (hilbertBasis S).repr_self d
    rw [hb]
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : Occupation S => ℂ) 2 d c (1 : ℂ))
  change C (lp.single 2 d c) = coefficientOperator D (lp.single 2 d c)
  rw [coefficientOperator_single, hs, map_smul, hC]

theorem coefficientOperator_unique_on_polynomials (D : Data (S ⊕ T))
    (C : Hilbert S →L[ℂ] Hilbert T)
    (hC : ∀ p : MvPolynomial S ℂ,
      C (embedding S p) = ∑ d ∈ p.support, (scale d * p.coeff d) • column D d) :
    C = coefficientOperator D := by
  apply coefficientOperator_unique D C
  intro d
  have h := hC (MvPolynomial.monomial d (scale d)⁻¹)
  have hscale := FactorialFockMetric.scale_ne_zero d
  have he : embedding S (MvPolynomial.monomial d (scale d)⁻¹) = hilbertBasis S d := by
    rw [FactorialFockMetric.embedding_monomial, mul_inv_cancel₀ hscale, one_smul]
  rw [he] at h
  simpa [MvPolynomial.support_monomial, inv_ne_zero hscale, MvPolynomial.coeff_monomial,
    mul_inv_cancel₀ hscale] using h

/-- Convergence for the actual columns and arbitrary completed source input. -/
theorem coefficientOperator_hasSum (D : Data (S ⊕ T)) (x : Hilbert S) :
    HasSum (fun d : Occupation S => x d • column D d) (coefficientOperator D x) := by
  have h := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).mapL
    (coefficientOperator D)
  simpa only [coefficientOperator_single] using h

/-- In a triple-leg application BOTH source and target-input occupations are
the domain. The output occupation is the only row index. -/
theorem triple_matrix_coefficient {U : Type w} [DecidableEq U]
    (D : Data ((S ⊕ T) ⊕ U)) (d : Occupation S) (e : Occupation T) (h : Occupation U) :
    inner ℂ (hilbertBasis U h)
      (coefficientOperator D (hilbertBasis (S ⊕ T) (joinOccupation d e))) =
      scale d * scale e * scale h *
        coefficient D.kernel (joinOccupation (joinOccupation d e) h) := by
  rw [coefficientOperator_matrix, scale_join]

/- Native Y consumption remains external: match full normal+Corr polynomial
inputs, perform Gram whitening, positive-frequency damping and same-term
exponent regrouping. For a tensor with two domain legs, tensor-to-matrix
identification conjugates BOTH domain coefficients: conj(a_d)*conj(b_e).
It never changes holomorphic K_{ij}=K_{ji} into a Hermitian convention. -/

end D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientOperator
