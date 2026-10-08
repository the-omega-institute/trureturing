/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207LeftNormalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207LeftNormalization
   mirror-E: none(waiver:formal-left-kernel-boundary)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Laurent]
   utility: none
   digest: The substituted left boundary has twice the Laurent-exponent valuation bound. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Catalytic
import Mathlib.Algebra.Polynomial.Laurent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftNormalization

open InversionSeq207Endpoints InversionSeq207Catalytic
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def leftKernelArgument : PowerSeries (LaurentPolynomial ℚ) :=
  PowerSeries.mk fun degree =>
    LaurentPolynomial.C (if degree = 0 then 1 else 2 * (degree : ℚ)) -
      (degree : ℚ) • (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))

noncomputable def leftKernelBoundary : PowerSeries (LaurentPolynomial ℚ) :=
  let alternating := PowerSeries.map LaurentPolynomial.C
    (PowerSeries.mk fun degree => (-1 : ℚ) ^ degree)
  PowerSeries.mk fun degree =>
    ∑ depth ∈ Finset.range (degree + 1),
      (walkEndpoints true depth).sum fun label weight =>
        (weight : ℚ) • PowerSeries.coeff degree
          (PowerSeries.X ^ depth * alternating ^ (2 * depth) * leftKernelArgument ^ label.1)

theorem left_boundary_normalization :
    (∀ degree : ℕ, ∀ index : ℤ, (degree : ℤ) < 2 * |index| →
      (PowerSeries.coeff degree leftKernelBoundary).coeff index = 0) ∧
    (letI : UniformSpace (LaurentPolynomial ℚ) := ⊥
     letI : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
     let alternating := PowerSeries.map LaurentPolynomial.C
       (PowerSeries.mk fun degree => (-1 : ℚ) ^ degree)
     PowerSeries.eval₂ (RingHom.id (PowerSeries (LaurentPolynomial ℚ)))
       (PowerSeries.X * alternating ^ 2) (forwardSeries true leftKernelArgument 1) =
         leftKernelBoundary) ∧
    (1 - PowerSeries.X) ^ 2 * leftKernelArgument =
      1 + PowerSeries.X ^ 2 - PowerSeries.X *
        PowerSeries.C (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ∧
    PowerSeries.map (LaurentPolynomial.invert.toRingHom) leftKernelBoundary =
      leftKernelBoundary := by
  classical
  let alternating := PowerSeries.map LaurentPolynomial.C
    (PowerSeries.mk fun degree => (-1 : ℚ) ^ degree)
  have hmul (left right : LaurentPolynomial ℚ) (leftWidth rightWidth : ℤ)
      (hleft : ∀ index : ℤ, leftWidth < |index| → left.coeff index = 0)
      (hright : ∀ index : ℤ, rightWidth < |index| → right.coeff index = 0) :
      ∀ index : ℤ, leftWidth + rightWidth < |index| → (left * right).coeff index = 0 := by
    intro index hindex
    rw [AddMonoidAlgebra.coeff_mul_apply_left]
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro first _
    dsimp only
    by_cases hfirst : leftWidth < |first|
    · rw [hleft first hfirst, zero_mul]
    · rw [hright (-first + index) (by
        have htriangle : |index| ≤ |first| + |-first + index| := by
          simpa using abs_add_le first (-first + index)
        omega), mul_zero]
  have hproduct (left right : PowerSeries (LaurentPolynomial ℚ))
      (leftWidth rightWidth width : ℕ → ℤ)
      (hwidth : ∀ first second, leftWidth first + rightWidth second ≤ width (first + second))
      (hleft : ∀ degree index, leftWidth degree < |index| →
        (PowerSeries.coeff degree left).coeff index = 0)
      (hright : ∀ degree index, rightWidth degree < |index| →
        (PowerSeries.coeff degree right).coeff index = 0) :
      ∀ degree index, width degree < |index| →
        (PowerSeries.coeff degree (left * right)).coeff index = 0 := by
    intro degree index hindex
    simp only [PowerSeries.coeff_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro pair hpair
    apply hmul _ _ _ _ (hleft pair.1) (hright pair.2) index
    have hpairDegree := Finset.mem_antidiagonal.mp hpair
    have hbound := hwidth pair.1 pair.2
    rw [hpairDegree] at hbound
    omega
  have hargument :
      (∀ (degree : ℕ) (index : ℤ), (1 : ℤ) < |index| →
        (PowerSeries.coeff degree leftKernelArgument).coeff index = 0) ∧
      (∀ (degree : ℕ) (index : ℤ), (degree : ℤ) < |index| →
        (PowerSeries.coeff degree leftKernelArgument).coeff index = 0) := by
    have hfixed (degree : ℕ) (index : ℤ) (hlarge : 1 < |index|) :
        (PowerSeries.coeff degree leftKernelArgument).coeff index = 0 := by
      have hzero : index ≠ 0 := by rintro rfl; norm_num at hlarge
      have hpos : (1 : ℤ) ≠ index := by rintro rfl; norm_num at hlarge
      have hneg : (-1 : ℤ) ≠ index := by rintro rfl; norm_num at hlarge
      simp [leftKernelArgument, LaurentPolynomial.C_apply, LaurentPolynomial.T_apply,
        hzero, hpos, hneg]
    refine ⟨hfixed, ?_⟩
    intro degree index hlarge
    cases degree with
    | zero =>
        have hzero : index ≠ 0 := by rintro rfl; norm_num at hlarge
        simp only [leftKernelArgument, PowerSeries.coeff_mk, Nat.cast_zero, ite_true,
          zero_smul, sub_zero, map_one]
        rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
          Finsupp.single_apply, if_neg (Ne.symm hzero)]
    | succ degree => exact hfixed _ _ (by omega)
  have hpower (power : ℕ) :
      (∀ (degree : ℕ) (index : ℤ), (power : ℤ) < |index| →
        (PowerSeries.coeff degree (leftKernelArgument ^ power)).coeff index = 0) ∧
      (∀ (degree : ℕ) (index : ℤ), (degree : ℤ) < |index| →
        (PowerSeries.coeff degree (leftKernelArgument ^ power)).coeff index = 0) := by
    induction power with
    | zero =>
        constructor <;> intro degree index hlarge
        all_goals
          have hzero : index ≠ 0 := by
            rintro rfl
            simp only [abs_zero] at hlarge
            omega
          simp only [pow_zero, PowerSeries.coeff_one]
          split_ifs
          · simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
              Finsupp.single_apply, if_neg (Ne.symm hzero)]
          · rfl
    | succ power ih =>
        rw [pow_succ]
        constructor
        · exact hproduct _ _ (fun _ => power) (fun _ => 1) (fun _ => power + 1)
            (by intros; omega) ih.1 hargument.1
        · exact hproduct _ _ (fun degree => degree) (fun degree => degree)
            (fun degree => degree) (by intros; simp) ih.2 hargument.2
  have hscalar (power degree : ℕ) (index : ℤ) (hlarge : 0 < |index|) :
      (PowerSeries.coeff degree (alternating ^ power)).coeff index = 0 := by
    have hzero : index ≠ 0 := by rintro rfl; norm_num at hlarge
    dsimp only [alternating]
    rw [← map_pow, PowerSeries.coeff_map]
    simp [LaurentPolynomial.C_apply, hzero]
  have hterm (degree depth power : ℕ) (index : ℤ) (hpowerDepth : power ≤ depth)
      (hlarge : (degree : ℤ) < 2 * |index|) :
      (PowerSeries.coeff degree
        (PowerSeries.X ^ depth * alternating ^ (2 * depth) *
          leftKernelArgument ^ power)).coeff index = 0 := by
    rw [mul_assoc, PowerSeries.coeff_X_pow_mul']
    split_ifs with hdepth
    · by_cases hfixed : (power : ℤ) < |index|
      · exact hproduct _ _ (fun _ => 0) (fun _ => power) (fun _ => power)
          (by intros; omega) (hscalar (2 * depth)) (hpower power).1 _ _ hfixed
      · apply hproduct _ _ (fun _ => 0) (fun degree => degree) (fun degree => degree)
          (by intros; omega) (hscalar (2 * depth)) (hpower power).2
        omega
    · simp
  have hdenominator : (1 - PowerSeries.X) ^ 2 * leftKernelArgument =
      1 + PowerSeries.X ^ 2 - PowerSeries.X *
        PowerSeries.C (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) := by
    have hexpand : (1 - PowerSeries.X) ^ 2 * leftKernelArgument =
        leftKernelArgument - PowerSeries.X ^ 1 * leftKernelArgument -
          PowerSeries.X ^ 1 * leftKernelArgument +
          PowerSeries.X ^ 2 * leftKernelArgument := by ring
    rw [hexpand]
    apply PowerSeries.ext
    intro degree
    rcases degree with _ | (_ | (_ | degree))
    all_goals
      simp [leftKernelArgument, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow,
        PowerSeries.coeff_C, LaurentPolynomial.smul_eq_C_mul, Nat.cast_succ,
        map_add, map_mul, map_ofNat]
    all_goals ring
  have hreflection : PowerSeries.map (LaurentPolynomial.invert.toRingHom)
      leftKernelBoundary = leftKernelBoundary := by
    have hargumentReflected : PowerSeries.map (LaurentPolynomial.invert.toRingHom)
        leftKernelArgument = leftKernelArgument := by
      apply PowerSeries.ext
      intro degree
      rw [PowerSeries.coeff_map]
      change LaurentPolynomial.invert (PowerSeries.coeff degree leftKernelArgument) = _
      simp [leftKernelArgument, map_sub, map_smul, map_add, add_comm]
    have halternatingReflected : PowerSeries.map (LaurentPolynomial.invert.toRingHom)
        alternating = alternating := by
      apply PowerSeries.ext
      intro degree
      simp [alternating, PowerSeries.coeff_map]
    apply PowerSeries.ext
    intro degree
    rw [PowerSeries.coeff_map]
    change LaurentPolynomial.invert (PowerSeries.coeff degree leftKernelBoundary) = _
    simp only [leftKernelBoundary, PowerSeries.coeff_mk]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro depth _
    unfold Finsupp.sum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro label _
    rw [map_smul]
    apply congrArg (fun value : LaurentPolynomial ℚ =>
      ((walkEndpoints true depth) label : ℚ) • value)
    have hseries : PowerSeries.map (LaurentPolynomial.invert.toRingHom)
        (PowerSeries.X ^ depth * alternating ^ (2 * depth) * leftKernelArgument ^ label.1) =
        PowerSeries.X ^ depth * alternating ^ (2 * depth) * leftKernelArgument ^ label.1 := by
      simp only [map_mul, map_pow, PowerSeries.map_X, halternatingReflected, hargumentReflected]
    have hcoefficient := congrArg (PowerSeries.coeff degree) hseries
    rw [PowerSeries.coeff_map] at hcoefficient
    change LaurentPolynomial.invert (PowerSeries.coeff degree
      (PowerSeries.X ^ depth * alternating ^ (2 * depth) * leftKernelArgument ^ label.1)) =
        PowerSeries.coeff degree
          (PowerSeries.X ^ depth * alternating ^ (2 * depth) * leftKernelArgument ^ label.1)
      at hcoefficient
    simpa only [alternating] using hcoefficient
  refine ⟨?_, ?_, hdenominator, hreflection⟩
  · intro degree index hlarge
    simp only [leftKernelBoundary, PowerSeries.coeff_mk, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro depth _
    unfold Finsupp.sum
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply]
    apply Finset.sum_eq_zero
    intro label hlabel
    have hsupport := (forward_series_equations (R := ℚ) true depth).1.2.1 label
      (Finsupp.mem_support_iff.mp hlabel)
    rw [hterm degree depth label.1 index (by omega) hlarge, smul_zero]
  · let : UniformSpace (LaurentPolynomial ℚ) := ⊥
    let : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
    let parameter := PowerSeries.X * alternating ^ 2
    have hexpand (degree depth : ℕ) :
        PowerSeries.coeff degree
          (PowerSeries.coeff depth (forwardSeries true leftKernelArgument 1) *
            parameter ^ depth) =
        (walkEndpoints true depth).sum fun label weight =>
          (weight : ℚ) • PowerSeries.coeff degree
            (PowerSeries.X ^ depth * alternating ^ (2 * depth) *
              leftKernelArgument ^ label.1) := by
      simp only [forwardSeries, PowerSeries.coeff_mk, Finsupp.linearCombination_apply,
        Finsupp.sum, one_pow, mul_one, Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro label _
      simp only [smul_mul_assoc, map_zsmul]
      rw [← Int.cast_smul_eq_zsmul ℚ (M := LaurentPolynomial ℚ)]
      apply congrArg (fun value : LaurentPolynomial ℚ =>
        ((walkEndpoints true depth) label : ℚ) • value)
      apply congrArg (PowerSeries.coeff degree)
      dsimp only [parameter]
      simp only [mul_pow, pow_mul]
      ring
    have hparameter : PowerSeries.HasEval parameter :=
      PowerSeries.HasEval.mul_right (alternating ^ 2) PowerSeries.HasEval.X
    have hsum := PowerSeries.hasSum_eval₂
      (φ := RingHom.id (PowerSeries (LaurentPolynomial ℚ))) continuous_id hparameter
      (forwardSeries true leftKernelArgument 1)
    simp only [RingHom.id_apply] at hsum
    apply hsum.unique
    apply (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (LaurentPolynomial ℚ)).mpr
    intro degree
    have hzero (depth : ℕ) (hdepth : depth ∉ Finset.range (degree + 1)) :
        PowerSeries.coeff degree
          (PowerSeries.coeff depth (forwardSeries true leftKernelArgument 1) *
            parameter ^ depth) = 0 := by
      have hdiv : (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) ^ depth ∣
          PowerSeries.coeff depth (forwardSeries true leftKernelArgument 1) *
            parameter ^ depth := by
        refine ⟨PowerSeries.coeff depth (forwardSeries true leftKernelArgument 1) *
          (alternating ^ 2) ^ depth, ?_⟩
        dsimp only [parameter]
        ring
      exact PowerSeries.X_pow_dvd_iff.mp hdiv degree (by
        simp only [Finset.mem_range, not_lt] at hdepth
        omega)
    have hfinite : HasSum (fun depth => PowerSeries.coeff degree
        (PowerSeries.coeff depth (forwardSeries true leftKernelArgument 1) * parameter ^ depth))
        (∑ depth ∈ Finset.range (degree + 1), PowerSeries.coeff degree
          (PowerSeries.coeff depth (forwardSeries true leftKernelArgument 1) *
            parameter ^ depth)) := hasSum_sum_of_ne_finset_zero hzero
    have hequality : PowerSeries.coeff degree leftKernelBoundary =
        ∑ depth ∈ Finset.range (degree + 1), PowerSeries.coeff degree
          (PowerSeries.coeff depth (forwardSeries true leftKernelArgument 1) *
            parameter ^ depth) := by
      simp only [leftKernelBoundary, PowerSeries.coeff_mk]
      apply Finset.sum_congr rfl
      intro depth _
      exact (hexpand degree depth).symm
    rw [hequality]
    exact hfinite

end D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftNormalization
