/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hilbert-Schmidt synthesis of actual two-mode columns and the physical reduced operator. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.BargmannKernel
import D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance
import D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis

/-! The actual completed coefficient operator and its Hilbert adjoint realize the partial trace. -/

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal
open Filter Topology

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
open BeamSplitter DisplacementCovariance

/-- Algebraic dimension of the actual operator range, including infinite cardinals. -/
def rangeRank (T : Fock →L[ℂ] Fock) : Cardinal :=
  Module.rank ℂ (LinearMap.range T.toLinearMap)

private def occupationBasis : HilbertBasis ℕ ℂ Fock :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fock)

private theorem single_eq_smul_basis (j : ℕ) (c : ℂ) :
    (lp.single 2 j c : Fock) = c • lp.single 2 j (1 : ℂ) := by
  simpa only [smul_eq_mul, mul_one] using
    (lp.single_smul (E := fun _ : ℕ => ℂ) 2 j c (1 : ℂ))

/-- The existing Hilbert-Schmidt synthesis supplier is applied after a genuine reindexing
of the occupation Hilbert basis onto its range as a set of Hilbert vectors. -/
theorem exists_coefficient_operator (V : TwoMode) :
    ∃ C : Fock →L[ℂ] Fock,
      (∀ j, C (lp.single 2 j (1 : ℂ)) = V j) ∧
      HilbertSchmidt.IsHilbertSchmidt C ∧
      (∑' j : ℕ, ‖C (lp.single 2 j (1 : ℂ))‖ ^ 2) = ‖V‖ ^ 2 := by
  classical
  let b := occupationBasis
  let w : Set Fock := Set.range b
  let e : ℕ ≃ w := Equiv.ofInjective b b.orthonormal.linearIndependent.injective
  have hw : Orthonormal ℂ (Subtype.val : w → Fock) := b.orthonormal.toSubtypeRange
  have hspan : (Submodule.span ℂ (Set.range (Subtype.val : w → Fock))).topologicalClosure = ⊤ := by
    simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq, w] using b.dense_span
  let bw : HilbertBasis w ℂ Fock := HilbertBasis.mk hw hspan.ge
  have hbw (i : w) : bw i = (i : Fock) := congrFun (HilbertBasis.coe_mk hw hspan.ge) i
  have hv : HasSum (fun j : ℕ => ‖V j‖ ^ 2) (‖V‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) V
  have hre : Summable (fun i : w => ‖V (e.symm i)‖ ^ 2) := e.symm.summable_iff.mpr hv.summable
  obtain ⟨C, hC, hhs, _, _⟩ :=
    HilbertSchmidt.exists_hilbertSchmidt_of_square_summable_columns bw
      (fun i => V (e.symm i)) hre
  have hcol (j : ℕ) : C (lp.single 2 j (1 : ℂ)) = V j := by
    have h := hC (e j)
    rw [hbw, e.symm_apply_apply] at h
    have heq : (e j : Fock) = b j := rfl
    have hb : b j = lp.single 2 j (1 : ℂ) := by
      simpa only [b, occupationBasis, LinearIsometryEquiv.coe_refl, id_eq] using b.repr_self j
    rw [heq, hb] at h
    exact h
  exact ⟨C, hcol, hhs, by simpa only [hcol] using hv.tsum_eq⟩

/-- The unique column operator synthesized from the actual two-mode vector. -/
def coefficientOperator (V : TwoMode) : Fock →L[ℂ] Fock :=
  (exists_coefficient_operator V).choose

theorem coefficient_operator_column (V : TwoMode) (j : ℕ) :
    coefficientOperator V (lp.single 2 j (1 : ℂ)) = V j :=
  (exists_coefficient_operator V).choose_spec.1 j

theorem coefficient_operator_hilbert_schmidt (V : TwoMode) :
    HilbertSchmidt.IsHilbertSchmidt (coefficientOperator V) :=
  (exists_coefficient_operator V).choose_spec.2.1

theorem coefficient_operator_square_sum (V : TwoMode) :
    (∑' j : ℕ, ‖coefficientOperator V (lp.single 2 j (1 : ℂ))‖ ^ 2) = ‖V‖ ^ 2 :=
  (exists_coefficient_operator V).choose_spec.2.2

theorem coefficient_operator_single (V : TwoMode) (j : ℕ) (c : ℂ) :
    coefficientOperator V (lp.single 2 j c) = c • V j := by
  rw [single_eq_smul_basis, map_smul, coefficient_operator_column]

theorem coefficient_operator_unique (V : TwoMode) (C : Fock →L[ℂ] Fock)
    (hC : ∀ j, C (lp.single 2 j (1 : ℂ)) = V j) : C = coefficientOperator V := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro j
  apply ContinuousLinearMap.ext
  intro c
  change C (lp.single 2 j c) = coefficientOperator V (lp.single 2 j c)
  rw [coefficient_operator_single, single_eq_smul_basis, map_smul, hC]

theorem adjoint_coefficient (V : TwoMode) (y : Fock) (j : ℕ) :
    (ContinuousLinearMap.adjoint (coefficientOperator V) y) j = inner ℂ (V j) y := by
  have h := ContinuousLinearMap.adjoint_inner_right (coefficientOperator V)
    (lp.single 2 j (1 : ℂ)) y
  simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, one_mul, mul_one,
    coefficient_operator_column] using h

/-- The owner's reduced operator is exactly the Hilbert-Schmidt coefficient operator times
its adjoint. This identity concerns the existing physical partial trace on the completion. -/
theorem pure_partial_trace_eq (V : TwoMode) :
    purePartialTrace V = coefficientOperator V * star (coefficientOperator V) := by
  have hv : Summable (fun j : ℕ => ‖V j‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) V).summable
  have hrank : Summable (fun j : ℕ => InnerProductSpace.rankOne ℂ (V j) (V j)) := by
    apply Summable.of_norm
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using hv
  apply ContinuousLinearMap.ext
  intro y
  have hleft := hrank.hasSum.mapL (ContinuousLinearMap.apply ℂ Fock y)
  have hright := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (ContinuousLinearMap.adjoint (coefficientOperator V) y)).mapL (coefficientOperator V)
  change HasSum _ (purePartialTrace V y) at hleft
  change purePartialTrace V y =
    coefficientOperator V (ContinuousLinearMap.adjoint (coefficientOperator V) y)
  apply hleft.unique
  convert hright using 1
  apply funext
  intro j
  change InnerProductSpace.rankOne ℂ (V j) (V j) y =
    coefficientOperator V (lp.single 2 j ((ContinuousLinearMap.adjoint (coefficientOperator V) y) j))
  simp only [InnerProductSpace.rankOne_apply, coefficient_operator_single, adjoint_coefficient]

/-- The full completed column-synthesis contract: uniqueness, the actual
Hilbert-Schmidt property, Parseval square sum, and the existing partial trace.
The uniqueness assertion is over continuous complex-linear operators. -/
theorem exists_unique_completed_coefficient_operator (V : TwoMode) :
    ∃! C : Fock →L[ℂ] Fock,
      (∀ j, C (lp.single 2 j (1 : ℂ)) = V j) ∧
      HilbertSchmidt.IsHilbertSchmidt C ∧
      (∑' j : ℕ, ‖C (lp.single 2 j (1 : ℂ))‖ ^ 2) = ‖V‖ ^ 2 ∧
      purePartialTrace V = C * star C := by
  refine ⟨coefficientOperator V, ⟨coefficient_operator_column V,
    coefficient_operator_hilbert_schmidt V, coefficient_operator_square_sum V,
    pure_partial_trace_eq V⟩, ?_⟩
  intro C hC
  exact coefficient_operator_unique V C hC.1

theorem coefficient_operator_exponential (V : TwoMode) (w : ℂ) :
    coefficientOperator V (exponentialVector w) = discardedSection V w := by
  have h := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (exponentialVector w)).mapL (coefficientOperator V)
  apply h.unique
  simpa only [coefficient_operator_single, exponentialVector, discardedSection] using
    (summable_contraction V w).hasSum

/-- Evaluation sections of the completed kernel are transforms of actual operator images. -/
theorem kernel_eq_coefficient_operator (V : TwoMode) (z w : ℂ) :
    kernel V z w = transform (coefficientOperator V (exponentialVector w)) z := by
  rw [coefficient_operator_exponential, kernel_eq_transform_discarded_section]

#print axioms exists_coefficient_operator
#print axioms pure_partial_trace_eq
#print axioms exists_unique_completed_coefficient_operator
#print axioms kernel_eq_coefficient_operator

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
