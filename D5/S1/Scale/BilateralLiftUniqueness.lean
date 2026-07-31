/- GID: D5/S1/Scale/BilateralLiftUniqueness
   generality: I
   mirror-B: D5/B/S1/Scale/BilateralLiftUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fibonacci solutions split into two golden eigenlines, with a minimal cyclic carrier. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace D5.S1.Scale

abbrev Seq := ℕ → ℝ

/-- Forward shift on real sequences. -/
def shift : Seq →ₗ[ℝ] Seq where
  toFun u k := u (k + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Fibonacci weights indexed from `F_1 = 1`. -/
def fibonacciWeight : Seq := fun k => Nat.fib (k + 1)

/-- Expanding golden eigensequence, indexed compatibly with `fibonacciWeight`. -/
noncomputable def expandingSequence : Seq := fun k => Real.goldenRatio ^ (k + 1)

/-- Contracting golden eigensequence, indexed compatibly with `fibonacciWeight`. -/
noncomputable def contractingSequence : Seq := fun k => Real.goldenConj ^ (k + 1)

/-- The Fibonacci recurrence solution space is exactly the span of the two golden eigensequences. -/
theorem fibonacci_solution_space_eq_span :
    (Real.fibRec : LinearRecurrence ℝ).solSpace =
      Submodule.span ℝ {expandingSequence, contractingSequence} := by
  classical
  symm
  letI : FiniteDimensional ℝ (Real.fibRec : LinearRecurrence ℝ).solSpace :=
    (Real.fibRec : LinearRecurrence ℝ).basis.finiteDimensional_of_finite
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro u (rfl | hu)
    · have h := (Real.fibRec : LinearRecurrence ℝ).solSpace.smul_mem
          Real.goldenRatio Real.geom_goldenRatio_isSol_fibRec
      have heq : expandingSequence = Real.goldenRatio • (Real.goldenRatio ^ ·) := by
        ext k
        simp [expandingSequence, pow_succ, mul_comm]
      exact heq ▸ h
    · rw [Set.mem_singleton_iff] at hu
      subst u
      have h := (Real.fibRec : LinearRecurrence ℝ).solSpace.smul_mem
          Real.goldenConj Real.geom_goldenConj_isSol_fibRec
      have heq : contractingSequence = Real.goldenConj • (Real.goldenConj ^ ·) := by
        ext k
        simp [contractingSequence, pow_succ, mul_comm]
      exact heq ▸ h
  · have hexp : expandingSequence ≠ 0 := by
      intro h
      have h0 := congr_fun h 0
      norm_num [expandingSequence] at h0
      have hsqrt : 0 < √5 := Real.sqrt_pos.2 (by norm_num)
      nlinarith
    have hlin : LinearIndepOn ℝ id ({expandingSequence, contractingSequence} : Set Seq) := by
      apply linearIndepOn_id_pair hexp
      intro a h
      have h0 := congr_fun h 0
      have h1 := congr_fun h 1
      norm_num [expandingSequence, contractingSequence, pow_two] at h0 h1
      have ha : a = 1 := by nlinarith [h0, h1]
      have heq : Real.goldenRatio = Real.goldenConj := by
        subst a
        simpa using h0
      have hsqrt : 0 < √5 := Real.sqrt_pos.2 (by norm_num)
      nlinarith [Real.goldenRatio_sub_goldenConj]
    have hne : expandingSequence ≠ contractingSequence := by
      intro h
      have h0 := congr_fun h 0
      norm_num [expandingSequence, contractingSequence] at h0
      have hsqrt : 0 < √5 := Real.sqrt_pos.2 (by norm_num)
      nlinarith
    rw [finrank_span_set_eq_card hlin,
      Module.finrank_eq_card_basis (Real.fibRec : LinearRecurrence ℝ).basis]
    simp [Real.fibRec, hne]
    rw [Fintype.card_fin]

/-- Forward shift acts diagonally on the two golden eigensequences. -/
theorem shift_golden_eigenvectors :
    shift expandingSequence = Real.goldenRatio • expandingSequence ∧
      shift contractingSequence = Real.goldenConj • contractingSequence := by
  constructor <;> ext k <;>
    simp [shift, expandingSequence, contractingSequence, pow_succ, mul_comm]

/-- Binet's formula in the indexing used by the weight sequence. -/
theorem fibonacci_weight_binet (k : ℕ) :
    fibonacciWeight k = (expandingSequence k - contractingSequence k) / √5 := by
  exact Real.coe_fib_eq (k + 1)

/-- The span of the golden eigensequences is the least shift-invariant submodule containing `F`. -/
theorem fibonacci_cyclic_span_minimal :
    fibonacciWeight ∈ Submodule.span ℝ {expandingSequence, contractingSequence} ∧
      (∀ u ∈ Submodule.span ℝ {expandingSequence, contractingSequence},
        shift u ∈ Submodule.span ℝ {expandingSequence, contractingSequence}) ∧
      ∀ W : Submodule ℝ Seq, fibonacciWeight ∈ W →
        (∀ u ∈ W, shift u ∈ W) →
        Submodule.span ℝ {expandingSequence, contractingSequence} ≤ W := by
  have hF : fibonacciWeight ∈
      Submodule.span ℝ {expandingSequence, contractingSequence} := by
    rw [Submodule.mem_span_pair]
    refine ⟨(√5)⁻¹, -(√5)⁻¹, ?_⟩
    ext k
    rw [fibonacci_weight_binet]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨hF, ?_, ?_⟩
  · intro u hu
    rw [Submodule.mem_span_pair] at hu ⊢
    obtain ⟨a, b, rfl⟩ := hu
    refine ⟨a * Real.goldenRatio, b * Real.goldenConj, ?_⟩
    rw [map_add, map_smul, map_smul, shift_golden_eigenvectors.1,
      shift_golden_eigenvectors.2]
    simp only [smul_smul]
  · intro W hFW hW
    have hshiftF : shift fibonacciWeight ∈ W := hW fibonacciWeight hFW
    have hexp : expandingSequence ∈ W := by
      have h := W.sub_mem hshiftF (W.smul_mem Real.goldenConj hFW)
      convert h using 1
      ext k
      simp only [shift, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, fibonacciWeight, expandingSequence]
      exact (Real.fib_succ_sub_goldenConj_mul_fib (k + 1)).symm
    have hcon : contractingSequence ∈ W := by
      have h := W.sub_mem hshiftF (W.smul_mem Real.goldenRatio hFW)
      convert h using 1
      ext k
      simp only [shift, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, fibonacciWeight, contractingSequence]
      exact (Real.fib_succ_sub_goldenRatio_mul_fib (k + 1)).symm
    rw [Submodule.span_le]
    rintro u (rfl | hu)
    · exact hexp
    · simpa only [Set.mem_singleton_iff] using hu ▸ hcon

/-- Removing the expanding Fibonacci component leaves the contracting eigensequence exactly. -/
theorem fibonacci_weight_residual (k : ℕ) :
    fibonacciWeight (k + 1) - Real.goldenRatio * fibonacciWeight k =
      Real.goldenConj ^ (k + 1) := by
  exact Real.fib_succ_sub_goldenRatio_mul_fib (k + 1)

end D5.S1.Scale
