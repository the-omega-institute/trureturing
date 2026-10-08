/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207LeftDiagonal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207LeftDiagonal
   mirror-E: none(waiver:formal-left-diagonal-reflection)
   anchors: [mathlib/module/Mathlib.RingTheory.LaurentSeries]
   utility: none
   digest: Finite endpoint expansions justify the kernel's shifted diagonal reflection. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftNormalization
import Mathlib.RingTheory.LaurentSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftDiagonal

open InversionSeq207Endpoints InversionSeq207Catalytic InversionSeq207LeftNormalization
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def leftDiagonalArgument : PowerSeries (LaurentPolynomial ℚ) :=
  PowerSeries.map LaurentPolynomial.C
      (PowerSeries.invOfUnit ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X)) 1) *
    (1 + PowerSeries.X ^ 3 - PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 1) -
      PowerSeries.X * PowerSeries.C (LaurentPolynomial.T (-1)))

noncomputable def leftDiagonalBoundary : PowerSeries (LaurentPolynomial ℚ) :=
  let alternating := PowerSeries.map LaurentPolynomial.C
    (PowerSeries.mk fun degree => (-1 : ℚ) ^ degree)
  PowerSeries.mk fun degree =>
    ∑ depth ∈ Finset.range (degree + 1),
      (walkEndpoints true depth).sum fun label weight =>
        (weight : ℚ) • PowerSeries.coeff degree
          (PowerSeries.X ^ depth * alternating ^ (2 * depth) *
            leftDiagonalArgument ^ (label.1 + label.2))

set_option maxHeartbeats 800000 in
theorem left_diagonal_reflection :
    (∀ degree : ℕ, ∀ index : ℤ, (degree : ℤ) < 2 * |index| →
      (PowerSeries.coeff degree leftDiagonalBoundary).coeff index = 0) ∧
    (∀ index : ℤ,
      let column (exponent : ℤ) : LaurentSeries ℚ :=
        (PowerSeries.mk fun degree =>
          (PowerSeries.coeff degree leftDiagonalBoundary).coeff exponent : PowerSeries ℚ)
      column index = HahnSeries.single index 1 * column (-index)) ∧
    (letI : UniformSpace (LaurentPolynomial ℚ) := ⊥
     letI : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
     let alternating := PowerSeries.map LaurentPolynomial.C
       (PowerSeries.mk fun degree => (-1 : ℚ) ^ degree)
     PowerSeries.eval₂ (RingHom.id (PowerSeries (LaurentPolynomial ℚ)))
       (PowerSeries.X * alternating ^ 2)
       (forwardSeries true leftDiagonalArgument leftDiagonalArgument) =
         leftDiagonalBoundary) ∧
    (letI : UniformSpace (LaurentPolynomial ℚ) := ⊥
     letI : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
     let q : PowerSeries (LaurentPolynomial ℚ) := PowerSeries.X
     let t := PowerSeries.C (LaurentPolynomial.T 1 : LaurentPolynomial ℚ)
     let alternating := PowerSeries.map LaurentPolynomial.C
       (PowerSeries.mk fun degree => (-1 : ℚ) ^ degree)
     let parameter := q * alternating ^ 2
     let residual := 1 - parameter * PowerSeries.eval₂
       (RingHom.id (PowerSeries (LaurentPolynomial ℚ))) parameter (forwardSeries true 1 1)
     (q - 1) ^ 2 * (q ^ 2 * t - 1) * leftDiagonalBoundary =
       (q - t) * (1 + q * PowerSeries.C (LaurentPolynomial.T (-1) - 2) +
         q ^ 2 * PowerSeries.C (LaurentPolynomial.T 1 - 2) + q ^ 3) * leftKernelBoundary +
           (q ^ 2 - 1) ^ 2 * (t - 1) * residual) := by
  classical
  let scalar : PowerSeries ℚ :=
    PowerSeries.invOfUnit ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X)) 1
  let alternating : PowerSeries ℚ := PowerSeries.mk fun degree => (-1 : ℚ) ^ degree
  let numerator : LaurentPolynomial (PowerSeries ℚ) :=
    LaurentPolynomial.C (1 + PowerSeries.X ^ 3) -
      LaurentPolynomial.C (PowerSeries.X ^ 2) * LaurentPolynomial.T 1 -
      LaurentPolynomial.C PowerSeries.X * LaurentPolynomial.T (-1)
  let expandMonomial : Multiplicative ℤ →* PowerSeries (LaurentPolynomial ℚ) :=
    { toFun := fun exponent => PowerSeries.C (LaurentPolynomial.T exponent.toAdd)
      map_one' := by simp
      map_mul' := by
        intro first second
        change PowerSeries.C (LaurentPolynomial.T (first.toAdd + second.toAdd)) = _
        rw [LaurentPolynomial.T_add, map_mul] }
  let expand : LaurentPolynomial (PowerSeries ℚ) →+*
      PowerSeries (LaurentPolynomial ℚ) :=
    AddMonoidAlgebra.liftNCRingHom (PowerSeries.map LaurentPolynomial.C)
      expandMonomial (fun _ _ => Commute.all _ _)
  have hexpandMonomial (value : PowerSeries ℚ) (exponent : ℤ) :
      expand (LaurentPolynomial.C value * LaurentPolynomial.T exponent) =
        PowerSeries.map LaurentPolynomial.C value *
          PowerSeries.C (LaurentPolynomial.T exponent) := by
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    exact AddMonoidAlgebra.liftNCRingHom_single _ _ _ _ _
  have hexpandCoeff (polynomial : LaurentPolynomial (PowerSeries ℚ))
      (degree : ℕ) (exponent : ℤ) :
      (PowerSeries.coeff degree (expand polynomial)).coeff exponent =
        PowerSeries.coeff degree (polynomial.coeff exponent) := by
    induction polynomial using LaurentPolynomial.induction_on' with
    | add first second hfirst hsecond =>
        simp only [map_add, AddMonoidAlgebra.coeff_add,
          Finsupp.coe_add, Pi.add_apply, hfirst, hsecond]
    | C_mul_T location value =>
        rw [hexpandMonomial, PowerSeries.coeff_mul_C, PowerSeries.coeff_map]
        rw [← LaurentPolynomial.single_eq_C_mul_T,
          ← LaurentPolynomial.single_eq_C_mul_T]
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
        split_ifs <;> simp only [map_zero]
  let promoteMonomial : Multiplicative ℤ →* LaurentPolynomial (LaurentSeries ℚ) :=
    { toFun := fun exponent => LaurentPolynomial.T exponent.toAdd
      map_one' := by simp
      map_mul' := by
        intro first second
        change LaurentPolynomial.T (first.toAdd + second.toAdd) = _
        rw [LaurentPolynomial.T_add] }
  let promote : LaurentPolynomial (PowerSeries ℚ) →+*
      LaurentPolynomial (LaurentSeries ℚ) :=
    AddMonoidAlgebra.liftNCRingHom
      (LaurentPolynomial.C.comp (HahnSeries.ofPowerSeries ℤ ℚ))
      promoteMonomial (fun _ _ => Commute.all _ _)
  have hpromoteMonomial (value : PowerSeries ℚ) (exponent : ℤ) :
      promote (LaurentPolynomial.C value * LaurentPolynomial.T exponent) =
        LaurentPolynomial.C (value : LaurentSeries ℚ) * LaurentPolynomial.T exponent := by
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    exact AddMonoidAlgebra.liftNCRingHom_single _ _ _ _ _
  have hpromoteCoeff (polynomial : LaurentPolynomial (PowerSeries ℚ)) (exponent : ℤ) :
      (promote polynomial).coeff exponent = (polynomial.coeff exponent : LaurentSeries ℚ) := by
    induction polynomial using LaurentPolynomial.induction_on' with
    | add first second hfirst hsecond =>
        simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.coe_add,
          Pi.add_apply, hfirst, hsecond]
    | C_mul_T location value =>
        rw [hpromoteMonomial, ← LaurentPolynomial.single_eq_C_mul_T,
          ← LaurentPolynomial.single_eq_C_mul_T]
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
        split_ifs <;> simp
  let reflectionMonomial : Multiplicative ℤ →* LaurentPolynomial (LaurentSeries ℚ) :=
    { toFun := fun exponent =>
        LaurentPolynomial.C (HahnSeries.single (-exponent.toAdd) 1) *
          LaurentPolynomial.T (-exponent.toAdd)
      map_one' := by simp [← HahnSeries.C_apply]
      map_mul' := by
        intro first second
        change LaurentPolynomial.C (HahnSeries.single (-(first.toAdd + second.toAdd)) 1) *
          LaurentPolynomial.T (-(first.toAdd + second.toAdd)) = _
        rw [neg_add, LaurentPolynomial.T_add]
        rw [show HahnSeries.single (-first.toAdd + -second.toAdd) (1 : ℚ) =
          HahnSeries.single (-first.toAdd) 1 * HahnSeries.single (-second.toAdd) 1 by
            rw [HahnSeries.single_mul_single, one_mul]]
        rw [map_mul]
        ring }
  let reflect : LaurentPolynomial (LaurentSeries ℚ) →+*
      LaurentPolynomial (LaurentSeries ℚ) :=
    AddMonoidAlgebra.liftNCRingHom LaurentPolynomial.C
      reflectionMonomial (fun _ _ => Commute.all _ _)
  have hreflectMonomial (value : LaurentSeries ℚ) (exponent : ℤ) :
      reflect (LaurentPolynomial.C value * LaurentPolynomial.T exponent) =
        LaurentPolynomial.C (value * HahnSeries.single (-exponent) 1) *
          LaurentPolynomial.T (-exponent) := by
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    simp only [reflect, AddMonoidAlgebra.liftNCRingHom_single, reflectionMonomial]
    change LaurentPolynomial.C value *
      (LaurentPolynomial.C (HahnSeries.single (-exponent) 1) * LaurentPolynomial.T (-exponent)) = _
    rw [← mul_assoc, ← map_mul]
  have hreflectConstant (value : LaurentSeries ℚ) :
      reflect (LaurentPolynomial.C value) = LaurentPolynomial.C value := by
    simpa only [LaurentPolynomial.T_zero, mul_one, neg_zero, ← HahnSeries.C_apply,
      map_one] using hreflectMonomial value 0
  have hreflectCoeff (polynomial : LaurentPolynomial (LaurentSeries ℚ)) (exponent : ℤ) :
      (reflect polynomial).coeff exponent =
        HahnSeries.single exponent 1 * polynomial.coeff (-exponent) := by
    induction polynomial using LaurentPolynomial.induction_on' with
    | add first second hfirst hsecond =>
        simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply,
          mul_add, hfirst, hsecond]
    | C_mul_T location value =>
        rw [hreflectMonomial, ← LaurentPolynomial.single_eq_C_mul_T,
          ← LaurentPolynomial.single_eq_C_mul_T]
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
        by_cases hequal : -location = exponent
        · have hlocation : location = -exponent := by omega
          simp only [if_pos hlocation, hequal, if_true, mul_comm]
        · have hlocation : location ≠ -exponent := by omega
          simp only [if_neg hequal, if_neg hlocation, mul_zero]
  have hpromoteNumerator :
      promote numerator = LaurentPolynomial.C (1 + HahnSeries.single 3 1) -
        LaurentPolynomial.C (HahnSeries.single 2 1) * LaurentPolynomial.T 1 -
        LaurentPolynomial.C (HahnSeries.single 1 1) * LaurentPolynomial.T (-1) := by
    simp only [numerator, map_sub, hpromoteMonomial,
      show ∀ value : PowerSeries ℚ, promote (LaurentPolynomial.C value) =
        LaurentPolynomial.C (value : LaurentSeries ℚ) from fun value => by
          simpa using hpromoteMonomial value 0,
      PowerSeries.coe_add, PowerSeries.coe_one, PowerSeries.coe_X]
    rw [PowerSeries.coe_pow, PowerSeries.coe_X, HahnSeries.single_pow,
      PowerSeries.coe_pow, PowerSeries.coe_X, HahnSeries.single_pow]
    norm_num
  have hinvariantNumerator : reflect (promote numerator) = promote numerator := by
    rw [hpromoteNumerator]
    simp only [map_sub, hreflectConstant, hreflectMonomial,
      HahnSeries.single_mul_single, one_mul]
    norm_num
    ring
  have hexpandNumerator : expand numerator =
      1 + PowerSeries.X ^ 3 - PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 1) -
        PowerSeries.X * PowerSeries.C (LaurentPolynomial.T (-1)) := by
    change expand (_ - _ - _) = _
    rw [map_sub, map_sub, hexpandMonomial, hexpandMonomial,
      show expand (LaurentPolynomial.C (1 + PowerSeries.X ^ 3)) =
        PowerSeries.map LaurentPolynomial.C (1 + PowerSeries.X ^ 3) from by
          simpa only [LaurentPolynomial.T_zero, mul_one, map_one] using
            hexpandMonomial (1 + PowerSeries.X ^ 3) 0]
    simp only [map_add, map_one, map_pow, PowerSeries.map_X]
  let term (depth power : ℕ) : LaurentPolynomial (PowerSeries ℚ) :=
    LaurentPolynomial.C (PowerSeries.X ^ depth * alternating ^ (2 * depth) * scalar ^ power) *
      numerator ^ power
  have hexpandTerm (depth power : ℕ) : expand (term depth power) =
      PowerSeries.X ^ depth * (PowerSeries.map LaurentPolynomial.C alternating) ^ (2 * depth) *
        leftDiagonalArgument ^ power := by
    have hconstant (value : PowerSeries ℚ) : expand (LaurentPolynomial.C value) =
        PowerSeries.map LaurentPolynomial.C value := by
      simpa using hexpandMonomial value 0
    change expand (LaurentPolynomial.C _ * numerator ^ power) = _
    rw [map_mul, hconstant, map_pow, hexpandNumerator]
    simp only [map_mul, map_pow, PowerSeries.map_X]
    dsimp only [leftDiagonalArgument, scalar]
    rw [mul_pow]
    ring
  have hinvariantTerm (depth power : ℕ) :
      reflect (promote (term depth power)) = promote (term depth power) := by
    have hconstant (value : PowerSeries ℚ) : promote (LaurentPolynomial.C value) =
        LaurentPolynomial.C (value : LaurentSeries ℚ) := by
      simpa using hpromoteMonomial value 0
    simp only [term, map_mul, map_pow, hconstant, hreflectConstant, hinvariantNumerator]
  have htermReflection (depth power : ℕ) (exponent : ℤ) :
      ((term depth power).coeff exponent : LaurentSeries ℚ) =
        HahnSeries.single exponent 1 *
          ((term depth power).coeff (-exponent) : LaurentSeries ℚ) := by
    have hequality := congrArg (fun polynomial : LaurentPolynomial (LaurentSeries ℚ) =>
      polynomial.coeff exponent) (hinvariantTerm depth power)
    rw [hreflectCoeff, hpromoteCoeff, hpromoteCoeff] at hequality
    exact hequality.symm
  have htermZero (depth power degree : ℕ) (exponent : ℤ) (hdepth : degree < depth) :
      PowerSeries.coeff degree ((term depth power).coeff exponent) = 0 := by
    rw [← hexpandCoeff, hexpandTerm, mul_assoc, PowerSeries.coeff_X_pow_mul']
    simp only [if_neg (not_le.mpr hdepth), AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply]
  have hreflection (exponent : ℤ) :
      ((PowerSeries.mk fun degree =>
        (PowerSeries.coeff degree leftDiagonalBoundary).coeff exponent : PowerSeries ℚ) :
          LaurentSeries ℚ) = HahnSeries.single exponent 1 *
        ((PowerSeries.mk fun degree =>
          (PowerSeries.coeff degree leftDiagonalBoundary).coeff (-exponent) : PowerSeries ℚ) :
            LaurentSeries ℚ) := by
    apply HahnSeries.ext
    funext degree
    rw [HahnSeries.coeff_single_mul, one_mul]
    simp only [PowerSeries.coeff_coe, PowerSeries.coeff_mk]
    have hcoefficient (degree : ℕ) (exponent : ℤ) :
        (PowerSeries.coeff degree leftDiagonalBoundary).coeff exponent =
          ∑ depth ∈ Finset.range (degree + 1),
            (walkEndpoints true depth).sum fun label weight =>
              (weight : ℚ) * PowerSeries.coeff degree
                ((term depth (label.1 + label.2)).coeff exponent) := by
      simp only [leftDiagonalBoundary, PowerSeries.coeff_mk, AddMonoidAlgebra.coeff_sum,
        Finsupp.finsetSum_apply, Finsupp.sum, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
        smul_eq_mul]
      apply Finset.sum_congr rfl
      intro depth _
      apply Finset.sum_congr rfl
      intro label _
      rw [← hexpandTerm, hexpandCoeff]
    have htermCoeff (depth power : ℕ) :
        (if degree < 0 then 0 else
          PowerSeries.coeff degree.natAbs ((term depth power).coeff exponent)) =
        (if degree - exponent < 0 then 0 else
          PowerSeries.coeff (degree - exponent).natAbs ((term depth power).coeff (-exponent))) := by
      have hequality := congrArg (fun series : LaurentSeries ℚ => series.coeff degree)
        (htermReflection depth power exponent)
      simpa only [HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe] using hequality
    by_cases hnegative : degree < 0
    · rw [if_pos hnegative]
      by_cases hshiftNegative : degree - exponent < 0
      · rw [if_pos hshiftNegative]
      · rw [if_neg hshiftNegative, hcoefficient]
        apply Eq.symm
        apply Finset.sum_eq_zero
        intro depth _
        unfold Finsupp.sum
        apply Finset.sum_eq_zero
        intro label _
        dsimp only
        have hzero := htermCoeff depth (label.1 + label.2)
        rw [if_pos hnegative, if_neg hshiftNegative] at hzero
        rw [← hzero, mul_zero]
    · rw [if_neg hnegative]
      by_cases hshiftNegative : degree - exponent < 0
      · rw [if_pos hshiftNegative, hcoefficient]
        apply Finset.sum_eq_zero
        intro depth _
        unfold Finsupp.sum
        apply Finset.sum_eq_zero
        intro label _
        dsimp only
        have hzero := htermCoeff depth (label.1 + label.2)
        rw [if_neg hnegative, if_pos hshiftNegative] at hzero
        rw [hzero, mul_zero]
      · rw [if_neg hshiftNegative, hcoefficient, hcoefficient]
        let cutoff := max degree.natAbs (degree - exponent).natAbs + 1
        have hpad (bound : ℕ) (exponent : ℤ) (hbound : bound < cutoff) :
            (∑ depth ∈ Finset.range (bound + 1),
              (walkEndpoints true depth).sum fun label weight =>
                (weight : ℚ) * PowerSeries.coeff bound
                  ((term depth (label.1 + label.2)).coeff exponent)) =
            ∑ depth ∈ Finset.range cutoff,
              (walkEndpoints true depth).sum fun label weight =>
                (weight : ℚ) * PowerSeries.coeff bound
                  ((term depth (label.1 + label.2)).coeff exponent) := by
          apply Finset.sum_subset (by
            intro depth hdepth
            simp only [Finset.mem_range] at *
            omega)
          intro depth _ hlarge
          unfold Finsupp.sum
          apply Finset.sum_eq_zero
          intro label _
          dsimp only
          rw [htermZero depth (label.1 + label.2) bound exponent (by
            simp only [Finset.mem_range, not_lt] at hlarge
            omega), mul_zero]
        rw [hpad _ _ (by dsimp [cutoff]; omega), hpad _ _ (by dsimp [cutoff]; omega)]
        apply Finset.sum_congr rfl
        intro depth _
        unfold Finsupp.sum
        apply Finset.sum_congr rfl
        intro label _
        apply congrArg ((↑((walkEndpoints true depth) label) : ℚ) * ·)
        simpa only [if_neg hnegative, if_neg hshiftNegative] using
          htermCoeff depth (label.1 + label.2)
  have hevaluation :
      (letI : UniformSpace (LaurentPolynomial ℚ) := ⊥
       letI : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
       PowerSeries.eval₂ (RingHom.id (PowerSeries (LaurentPolynomial ℚ)))
         (PowerSeries.X * (PowerSeries.map LaurentPolynomial.C alternating) ^ 2)
         (forwardSeries true leftDiagonalArgument leftDiagonalArgument) =
           leftDiagonalBoundary) := by
    let : UniformSpace (LaurentPolynomial ℚ) := ⊥
    let : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
    let mapped := PowerSeries.map LaurentPolynomial.C alternating
    let parameter := PowerSeries.X * mapped ^ 2
    have hexpansion (degree depth : ℕ) :
        PowerSeries.coeff degree
          (PowerSeries.coeff depth
              (forwardSeries true leftDiagonalArgument leftDiagonalArgument) * parameter ^ depth) =
        (walkEndpoints true depth).sum fun label weight =>
          (weight : ℚ) • PowerSeries.coeff degree
            (PowerSeries.X ^ depth * mapped ^ (2 * depth) *
              leftDiagonalArgument ^ (label.1 + label.2)) := by
      simp only [forwardSeries, PowerSeries.coeff_mk, Finsupp.linearCombination_apply,
        Finsupp.sum, Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro label _
      simp only [smul_mul_assoc, map_zsmul]
      rw [← Int.cast_smul_eq_zsmul ℚ (M := LaurentPolynomial ℚ)]
      apply congrArg (fun value : LaurentPolynomial ℚ =>
        ((walkEndpoints true depth) label : ℚ) • value)
      apply congrArg (PowerSeries.coeff degree)
      dsimp only [parameter]
      simp only [mul_pow, pow_mul, pow_add]
      ring
    have hparameter : PowerSeries.HasEval parameter :=
      PowerSeries.HasEval.mul_right (mapped ^ 2) PowerSeries.HasEval.X
    have hsum := PowerSeries.hasSum_eval₂
      (φ := RingHom.id (PowerSeries (LaurentPolynomial ℚ))) continuous_id hparameter
      (forwardSeries true leftDiagonalArgument leftDiagonalArgument)
    simp only [RingHom.id_apply] at hsum
    apply hsum.unique
    apply (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (LaurentPolynomial ℚ)).mpr
    intro degree
    have hzero (depth : ℕ) (hdepth : depth ∉ Finset.range (degree + 1)) :
        PowerSeries.coeff degree
          (PowerSeries.coeff depth
              (forwardSeries true leftDiagonalArgument leftDiagonalArgument) * parameter ^ depth) =
            0 := by
      have hdiv : (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) ^ depth ∣
          PowerSeries.coeff depth
              (forwardSeries true leftDiagonalArgument leftDiagonalArgument) *
                parameter ^ depth := by
        refine ⟨PowerSeries.coeff depth
          (forwardSeries true leftDiagonalArgument leftDiagonalArgument) *
            (mapped ^ 2) ^ depth, ?_⟩
        dsimp only [parameter]
        ring
      exact PowerSeries.X_pow_dvd_iff.mp hdiv degree (by
        simp only [Finset.mem_range, not_lt] at hdepth
        omega)
    have hfinite : HasSum (fun depth => PowerSeries.coeff degree
        (PowerSeries.coeff depth
            (forwardSeries true leftDiagonalArgument leftDiagonalArgument) * parameter ^ depth))
        (∑ depth ∈ Finset.range (degree + 1), PowerSeries.coeff degree
          (PowerSeries.coeff depth
              (forwardSeries true leftDiagonalArgument leftDiagonalArgument) *
                parameter ^ depth)) :=
      hasSum_sum_of_ne_finset_zero hzero
    have hequality : PowerSeries.coeff degree leftDiagonalBoundary =
        ∑ depth ∈ Finset.range (degree + 1), PowerSeries.coeff degree
          (PowerSeries.coeff depth
              (forwardSeries true leftDiagonalArgument leftDiagonalArgument) *
                parameter ^ depth) := by
      simp only [leftDiagonalBoundary, PowerSeries.coeff_mk]
      apply Finset.sum_congr rfl
      intro depth _
      exact (hexpansion degree depth).symm
    rw [hequality]
    exact hfinite
  have hkernel :
      (letI : UniformSpace (LaurentPolynomial ℚ) := ⊥
       letI : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
       let q : PowerSeries (LaurentPolynomial ℚ) := PowerSeries.X
       let t := PowerSeries.C (LaurentPolynomial.T 1 : LaurentPolynomial ℚ)
       let parameter := q * (PowerSeries.map LaurentPolynomial.C alternating) ^ 2
       let residual := 1 - parameter * PowerSeries.eval₂
         (RingHom.id (PowerSeries (LaurentPolynomial ℚ))) parameter (forwardSeries true 1 1)
       (q - 1) ^ 2 * (q ^ 2 * t - 1) * leftDiagonalBoundary =
         (q - t) * (1 + q * PowerSeries.C (LaurentPolynomial.T (-1) - 2) +
           q ^ 2 * PowerSeries.C (LaurentPolynomial.T 1 - 2) + q ^ 3) * leftKernelBoundary +
             (q ^ 2 - 1) ^ 2 * (t - 1) * residual) := by
    let : UniformSpace (LaurentPolynomial ℚ) := ⊥
    let : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
    let mapped := PowerSeries.map LaurentPolynomial.C alternating
    let parameter := PowerSeries.X * mapped ^ 2
    let collapse := PowerSeries.eval₂Hom (φ := RingHom.id
      (PowerSeries (LaurentPolynomial ℚ))) continuous_id
      (PowerSeries.HasEval.mul_right (mapped ^ 2) PowerSeries.HasEval.X)
    let embedding := algebraMap (PowerSeries (LaurentPolynomial ℚ))
      (FractionRing (PowerSeries (LaurentPolynomial ℚ)))
    have hinjective := IsFractionRing.injective (PowerSeries (LaurentPolynomial ℚ))
      (FractionRing (PowerSeries (LaurentPolynomial ℚ)))
    let qValue := embedding PowerSeries.X
    let tValue := embedding (PowerSeries.C (LaurentPolynomial.T 1))
    let xValue := embedding leftKernelArgument
    let yValue := embedding leftDiagonalArgument
    let zValue := embedding parameter
    let boundary := embedding leftKernelBoundary
    let diagonal := embedding leftDiagonalBoundary
    let full := embedding (collapse (forwardSeries true leftKernelArgument leftDiagonalArgument))
    let root := embedding (collapse (forwardSeries true 1 1))
    have hnonzero (series : PowerSeries (LaurentPolynomial ℚ))
        (hconstant : PowerSeries.constantCoeff series ≠ 0) : embedding series ≠ 0 := by
      intro hequal
      have hzero := hinjective (hequal.trans (map_zero embedding).symm)
      exact hconstant (by rw [hzero, map_zero])
    have hq : qValue ≠ 0 := by
      intro hequal
      exact PowerSeries.X_ne_zero (hinjective (hequal.trans (map_zero embedding).symm))
    have hplus : 1 + qValue ≠ 0 := by
      have hsource := hnonzero (1 + PowerSeries.X) (by
        simp only [map_add, map_one, PowerSeries.constantCoeff_X, add_zero]
        exact one_ne_zero)
      rw [map_add, map_one] at hsource
      exact hsource
    have hminus : 1 - qValue ≠ 0 := by
      have hsource := hnonzero (1 - PowerSeries.X) (by
        simp only [map_sub, map_one, PowerSeries.constantCoeff_X, sub_zero]
        exact one_ne_zero)
      rw [map_sub, map_one] at hsource
      exact hsource
    have hmonomial : (LaurentPolynomial.T 1 : LaurentPolynomial ℚ) ≠ 0 := by
      intro hequal
      have hcoeff := congrArg (fun polynomial : LaurentPolynomial ℚ => polynomial.coeff 1) hequal
      simp only [LaurentPolynomial.T_apply, if_true, AddMonoidAlgebra.coeff_zero,
        Finsupp.coe_zero, Pi.zero_apply] at hcoeff
      exact one_ne_zero hcoeff
    have ht : tValue ≠ 0 := hnonzero _ (by
      rw [PowerSeries.constantCoeff_C]
      exact hmonomial)
    have htone : tValue - 1 ≠ 0 := by
      have hsource := hnonzero (PowerSeries.C (LaurentPolynomial.T 1) - 1) (by
          simp only [map_sub, PowerSeries.constantCoeff_C, map_one]
          intro hequal
          have hcoeff := congrArg (fun polynomial : LaurentPolynomial ℚ =>
            polynomial.coeff 1) hequal
          rw [show (1 : LaurentPolynomial ℚ) = LaurentPolynomial.T 0 by rfl] at hcoeff
          norm_num only [AddMonoidAlgebra.coeff_sub, Finsupp.coe_sub, Pi.sub_apply,
            LaurentPolynomial.T_apply, AddMonoidAlgebra.coeff_zero,
            Finsupp.coe_zero, Pi.zero_apply] at hcoeff
          simp only [if_true, if_false, sub_zero] at hcoeff
          exact one_ne_zero hcoeff)
      rw [map_sub, map_one] at hsource
      exact hsource
    have hqt : qValue - tValue ≠ 0 := by
      have hsource := hnonzero (PowerSeries.X - PowerSeries.C (LaurentPolynomial.T 1)) (by
          simp only [map_sub, PowerSeries.constantCoeff_X,
            PowerSeries.constantCoeff_C, zero_sub, neg_ne_zero]
          exact hmonomial)
      rw [map_sub] at hsource
      exact hsource
    have hqtone : qValue * tValue - 1 ≠ 0 := by
      have hsource := hnonzero
        (PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 1) - 1) (by
          simp only [map_sub, map_mul, PowerSeries.constantCoeff_X,
            PowerSeries.constantCoeff_C, map_one, zero_mul, zero_sub, neg_ne_zero]
          exact one_ne_zero)
      rw [map_sub, map_mul, map_one] at hsource
      exact hsource
    have hinverseT : embedding (PowerSeries.C (LaurentPolynomial.T (-1))) = tValue⁻¹ := by
      apply mul_left_cancel₀ ht
      rw [mul_inv_cancel₀ ht]
      change embedding (PowerSeries.C (LaurentPolynomial.T 1)) *
        embedding (PowerSeries.C (LaurentPolynomial.T (-1))) = 1
      rw [← map_mul, ← map_mul, ← LaurentPolynomial.T_add]
      norm_num only
      rw [LaurentPolynomial.T_zero, map_one, map_one]
    have hx : xValue = (1 + qValue ^ 2 - qValue * (tValue + tValue⁻¹)) /
        (1 - qValue) ^ 2 := by
      apply (eq_div_iff (pow_ne_zero 2 hminus)).mpr
      have hdenominator := left_boundary_normalization.2.2.1
      rw [map_add PowerSeries.C] at hdenominator
      have hequal := congrArg embedding hdenominator
      simp only [map_mul, map_pow, map_sub, map_add, map_one, hinverseT] at hequal
      simpa only [mul_comm] using hequal
    have hy : yValue = (1 + qValue ^ 3 - qValue ^ 2 * tValue - qValue * tValue⁻¹) /
        ((1 - qValue) ^ 2 * (1 + qValue)) := by
      apply (eq_div_iff (mul_ne_zero (pow_ne_zero 2 hminus) hplus)).mpr
      have hscalarInverse := PowerSeries.mul_invOfUnit
        ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) : PowerSeries ℚ) 1 (by
          simp only [map_mul, map_pow, map_sub, map_add,
            PowerSeries.constantCoeff_X, map_one]
          norm_num)
      have hmapped := congrArg (PowerSeries.map LaurentPolynomial.C) hscalarInverse
      simp only [map_mul, map_pow, map_sub, map_add, map_one, PowerSeries.map_X] at hmapped
      have hcleared : (1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) * leftDiagonalArgument =
          1 + PowerSeries.X ^ 3 - PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 1) -
            PowerSeries.X * PowerSeries.C (LaurentPolynomial.T (-1)) := by
        change _ * (PowerSeries.map LaurentPolynomial.C scalar * _) = _
        rw [← mul_assoc, hmapped, one_mul]
      have hequal := congrArg embedding hcleared
      simp only [map_mul, map_pow, map_sub, map_add, map_one, hinverseT] at hequal
      simpa only [mul_comm] using hequal
    have halternating : (1 + PowerSeries.X) * mapped = 1 := by
      have hscalarAlternating : (1 + PowerSeries.X) * alternating = 1 := by
        apply PowerSeries.ext
        intro degree
        cases degree with
        | zero => simp only [add_mul, one_mul, map_add, PowerSeries.coeff_zero_X_mul,
            alternating, PowerSeries.coeff_mk, pow_zero, add_zero, PowerSeries.coeff_one,
            if_true]
        | succ degree =>
            simp only [add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul,
              alternating, PowerSeries.coeff_mk, PowerSeries.coeff_one,
              Nat.succ_ne_zero, if_false, pow_succ]
            ring
      have hequal := congrArg (PowerSeries.map LaurentPolynomial.C) hscalarAlternating
      simpa only [map_mul, map_add, map_one, PowerSeries.map_X] using hequal
    have hz : zValue = qValue / (1 + qValue) ^ 2 := by
      have hequal := congrArg embedding halternating
      simp only [map_mul, map_add, map_one] at hequal
      have hinverse : embedding mapped = (1 + qValue)⁻¹ := by
        apply mul_left_cancel₀ hplus
        rw [mul_inv_cancel₀ hplus]
        exact hequal
      dsimp only [zValue, parameter]
      rw [map_mul, map_pow, hinverse]
      simp only [div_eq_mul_inv, inv_pow]
      rfl
    have hC (value : PowerSeries (LaurentPolynomial ℚ)) :
        collapse (PowerSeries.C value) = value := by
      simp only [collapse, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C, RingHom.id_apply]
    have hX : collapse PowerSeries.X = parameter := by
      simp only [collapse, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]
      rfl
    have hboundary : collapse (forwardSeries true leftKernelArgument 1) =
        leftKernelBoundary := by
      simpa only [collapse, PowerSeries.coe_eval₂Hom, parameter, mapped, alternating] using
        left_boundary_normalization.2.1
    have hdiagonal : collapse (forwardSeries true leftDiagonalArgument leftDiagonalArgument) =
        leftDiagonalBoundary := by
      simpa only [collapse, PowerSeries.coe_eval₂Hom, parameter, mapped] using hevaluation
    have hforward := (forward_series_equations (R := PowerSeries (LaurentPolynomial ℚ))
      true 0).1.2.2.2.1 leftKernelArgument leftDiagonalArgument
    dsimp only at hforward
    have hforwardMapped := congrArg embedding (congrArg collapse hforward)
    simp only [map_mul, map_sub, map_add, map_one, hC, hX,
      hboundary, hdiagonal] at hforwardMapped
    change (1 - yValue) * (xValue - yValue) * (full - 1) = zValue *
      (xValue * (xValue - yValue) * (boundary - full) +
        (1 - yValue) * (xValue * full - yValue * diagonal) +
          (1 - yValue) * (xValue - yValue) * (xValue * boundary - root)) at hforwardMapped
    have hvanishing : (1 - yValue) * (xValue - yValue) -
        zValue * xValue * (1 - xValue) = 0 := by
      rw [hx, hy, hz]
      field_simp
      ring
    have hzero : (1 - yValue) * (xValue - yValue) * (1 - zValue * root) +
        zValue * xValue * (xValue - yValue) * (2 - yValue) * boundary -
          zValue * yValue * (1 - yValue) * diagonal = 0 := by
      linear_combination full * hvanishing - hforwardMapped
    have hfactor : (1 - yValue) * (xValue - yValue) * (1 - zValue * root) +
        zValue * xValue * (xValue - yValue) * (2 - yValue) * boundary -
          zValue * yValue * (1 - yValue) * diagonal =
        qValue ^ 2 * (tValue - 1) * (qValue * tValue - 1) * (qValue - tValue) /
          (tValue ^ 2 * (1 - qValue) ^ 6 * (1 + qValue) ^ 4) *
            ((qValue ^ 2 - 1) ^ 2 * (tValue - 1) * (1 - zValue * root) +
              (qValue - tValue) *
                (1 + qValue * (tValue⁻¹ - 2) + qValue ^ 2 * (tValue - 2) + qValue ^ 3) *
                  boundary - (qValue - 1) ^ 2 * (qValue ^ 2 * tValue - 1) * diagonal) := by
      rw [hx, hy, hz]
      field_simp
      ring
    rw [hfactor] at hzero
    have hfactorNonzero : qValue ^ 2 * (tValue - 1) * (qValue * tValue - 1) *
        (qValue - tValue) / (tValue ^ 2 * (1 - qValue) ^ 6 * (1 + qValue) ^ 4) ≠ 0 :=
      div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq) htone)
        hqtone) hqt) (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ht)
          (pow_ne_zero 6 hminus)) (pow_ne_zero 4 hplus))
    have hbracket := (mul_eq_zero.mp hzero).resolve_left hfactorNonzero
    have hfinal : (qValue - 1) ^ 2 * (qValue ^ 2 * tValue - 1) * diagonal =
      (qValue - tValue) *
        (1 + qValue * (tValue⁻¹ - 2) + qValue ^ 2 * (tValue - 2) + qValue ^ 3) * boundary +
          (qValue ^ 2 - 1) ^ 2 * (tValue - 1) * (1 - zValue * root) := by
      linear_combination -hbracket
    apply hinjective
    change embedding _ = embedding _
    simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hinverseT]
    simpa only [qValue, tValue, boundary, diagonal, zValue, root, collapse,
      PowerSeries.coe_eval₂Hom, parameter, map_mul, map_pow] using hfinal
  refine ⟨?_, hreflection, hevaluation, hkernel⟩
  intro degree index hlarge
  have hpolyProduct (left right : LaurentPolynomial ℚ) (leftWidth rightWidth : ℤ)
      (hleft : ∀ index, leftWidth < |index| → left.coeff index = 0)
      (hright : ∀ index, rightWidth < |index| → right.coeff index = 0) :
      ∀ index, leftWidth + rightWidth < |index| → (left * right).coeff index = 0 := by
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
    apply hpolyProduct _ _ _ _ (hleft pair.1) (hright pair.2) index
    have hpairDegree := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
    have hbound := hwidth pair.1 pair.2
    rw [hpairDegree] at hbound
    omega
  have hcentral (value : PowerSeries ℚ) (degree : ℕ) (index : ℤ) (hlarge : 0 < |index|) :
      (PowerSeries.coeff degree (PowerSeries.map LaurentPolynomial.C value)).coeff index = 0 := by
    have hzero : index ≠ 0 := by rintro rfl; norm_num at hlarge
    rw [PowerSeries.coeff_map]
    simp [LaurentPolynomial.C_apply, hzero]
  have hnumeratorFixed (degree : ℕ) (index : ℤ) (hlarge : 1 < |index|) :
      (PowerSeries.coeff degree (expand numerator)).coeff index = 0 := by
    have hzero : index ≠ 0 := by rintro rfl; norm_num at hlarge
    have hpos : (1 : ℤ) ≠ index := by rintro rfl; norm_num at hlarge
    have hneg : (-1 : ℤ) ≠ index := by rintro rfl; norm_num at hlarge
    have hone : (1 : LaurentPolynomial ℚ).coeff index = 0 := by
      change (Finsupp.single 0 (1 : ℚ)) index = 0
      simp only [Finsupp.single_apply, if_neg (Ne.symm hzero)]
    rw [hexpandNumerator]
    simp only [map_sub, map_add, PowerSeries.coeff_one,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_X,
      AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.coe_sub,
      Finsupp.coe_add, Pi.sub_apply, Pi.add_apply]
    split_ifs <;> simp only [one_mul, zero_mul,
      LaurentPolynomial.T_apply, if_neg hpos, if_neg hneg, hone,
      AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
      add_zero, sub_zero]
  have hnumeratorVariable (degree : ℕ) (index : ℤ) (hlarge : (degree : ℤ) < |index|) :
      (PowerSeries.coeff degree (expand numerator)).coeff index = 0 := by
    cases degree with
    | zero =>
        have hzero : index ≠ 0 := by rintro rfl; norm_num at hlarge
        rw [hexpandNumerator]
        simp only [map_sub, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow,
          PowerSeries.coeff_mul_C, PowerSeries.coeff_X]
        norm_num only
        simp only [if_true, if_false, zero_mul, add_zero, sub_zero, AddMonoidAlgebra.one_def,
          AddMonoidAlgebra.coeff_single,
          Finsupp.single_apply, if_neg (Ne.symm hzero)]
    | succ degree => exact hnumeratorFixed _ _ (by omega)
  have hargument :
      (∀ (degree : ℕ) (index : ℤ), (1 : ℤ) < |index| →
        (PowerSeries.coeff degree leftDiagonalArgument).coeff index = 0) ∧
      (∀ (degree : ℕ) (index : ℤ), (degree : ℤ) < |index| →
        (PowerSeries.coeff degree leftDiagonalArgument).coeff index = 0) := by
    have hargumentExpand : leftDiagonalArgument =
        PowerSeries.map LaurentPolynomial.C scalar * expand numerator := by
      rw [hexpandNumerator]
      rfl
    rw [hargumentExpand]
    constructor
    · exact hproduct _ _ (fun _ => 0) (fun _ => 1) (fun _ => 1)
        (by intros; omega) (hcentral scalar) hnumeratorFixed
    · exact hproduct _ _ (fun _ => 0) (fun degree => degree) (fun degree => degree)
        (by intros; omega) (hcentral scalar) hnumeratorVariable
  have hpower (power : ℕ) :
      (∀ (degree : ℕ) (index : ℤ), (power : ℤ) < |index| →
        (PowerSeries.coeff degree (leftDiagonalArgument ^ power)).coeff index = 0) ∧
      (∀ (degree : ℕ) (index : ℤ), (degree : ℤ) < |index| →
        (PowerSeries.coeff degree (leftDiagonalArgument ^ power)).coeff index = 0) := by
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
            (fun degree => degree) (by intros; omega) ih.2 hargument.2
  simp only [leftDiagonalBoundary, PowerSeries.coeff_mk, AddMonoidAlgebra.coeff_sum,
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
  have hzero : (PowerSeries.coeff degree
      (PowerSeries.X ^ depth * (PowerSeries.map LaurentPolynomial.C alternating) ^ (2 * depth) *
        leftDiagonalArgument ^ (label.1 + label.2))).coeff index = 0 := by
    rw [mul_assoc, PowerSeries.coeff_X_pow_mul']
    split_ifs with hdepth
    · by_cases hfixed : ((label.1 + label.2 : ℕ) : ℤ) < |index|
      · exact hproduct _ _ (fun _ => 0) (fun _ => label.1 + label.2)
          (fun _ => label.1 + label.2) (by intros; omega)
          (by simpa only [← map_pow] using hcentral (alternating ^ (2 * depth)))
          (hpower (label.1 + label.2)).1 _ _ hfixed
      · exact hproduct _ _ (fun _ => 0) (fun degree => degree) (fun degree => degree)
          (by intros; omega)
          (by simpa only [← map_pow] using hcentral (alternating ^ (2 * depth)))
          (hpower (label.1 + label.2)).2 _ _ (by omega)
    · rfl
  rw [hzero, smul_zero]

end D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftDiagonal
