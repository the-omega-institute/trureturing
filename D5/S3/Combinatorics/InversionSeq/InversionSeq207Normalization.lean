/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Normalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Normalization
   mirror-E: none(waiver:formal-right-kernel-normalization)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: The normalized right tree has triangular support and a formal kernel recurrence. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207NormalizationDefs
import Mathlib.RingTheory.PowerSeries.WellKnown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Normalization

open InversionSeq207Endpoints InversionSeq207Catalytic InversionSeq207Tridiagonal
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

set_option maxHeartbeats 1200000 in
theorem right_normalization :
    (∀ degree index : ℕ, degree < index →
      (PowerSeries.coeff degree rightNormalized).coeff index = 0) ∧
    (PowerSeries.map (Polynomial.evalRingHom (1 : ℚ)) rightNormalized *
      (1 - PowerSeries.X) = 1) ∧
    (letI : UniformSpace (Polynomial ℚ) := ⊥
     letI : DiscreteUniformity (Polynomial ℚ) := ⟨rfl⟩
     let alternating : PowerSeries (Polynomial ℚ) :=
       PowerSeries.mk fun degree => (-1) ^ degree
     let geometric : PowerSeries (Polynomial ℚ) :=
       PowerSeries.mk fun degree => Polynomial.X ^ degree
     let parameter := PowerSeries.X * alternating ^ 2
     let image := (1 + PowerSeries.X) * PowerSeries.C (1 - Polynomial.X) * geometric
     let collapse := PowerSeries.eval₂
       (RingHom.id (PowerSeries (Polynomial ℚ))) parameter
     let residual := PowerSeries.map (Polynomial.evalRingHom (0 : ℚ))
       (1 - parameter * collapse (forwardSeries false 1 1))
     let column (index : ℕ) : PowerSeries ℚ := PowerSeries.mk fun degree =>
       (PowerSeries.coeff degree rightNormalized).coeff index
     PowerSeries.eval₂ (RingHom.id (PowerSeries (Polynomial ℚ))) parameter
       (forwardSeries false image 1) * geometric = rightNormalized ∧
     (∀ index : ℕ,
       column index = residual * tridiagonalSeries index) ∧
     residual * rightScalarSeries = 1 ∧
     PowerSeries.constantCoeff rightScalarSeries = 1) := by
  classical
  let alternating : PowerSeries (Polynomial ℚ) := PowerSeries.mk fun degree => (-1) ^ degree
  let geometric : PowerSeries (Polynomial ℚ) :=
    PowerSeries.mk fun degree => Polynomial.X ^ degree
  have hdegreeMul (left right : PowerSeries (Polynomial ℚ)) (leftExtra rightExtra : ℕ)
      (hleft : ∀ degree, (PowerSeries.coeff degree left).natDegree ≤ degree + leftExtra)
      (hright : ∀ degree, (PowerSeries.coeff degree right).natDegree ≤ degree + rightExtra) :
      ∀ degree, (PowerSeries.coeff degree (left * right)).natDegree ≤
        degree + (leftExtra + rightExtra) := by
    intro degree
    rw [PowerSeries.coeff_mul]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro pair hpair
    have hsum := Finset.mem_antidiagonal.mp hpair
    have hmul := Polynomial.natDegree_mul_le
      (p := PowerSeries.coeff pair.1 left) (q := PowerSeries.coeff pair.2 right)
    have hfirst := hleft pair.1
    have hsecond := hright pair.2
    omega
  have hdegreePow (series : PowerSeries (Polynomial ℚ))
      (hseries : ∀ degree, (PowerSeries.coeff degree series).natDegree ≤ degree) :
      ∀ exponent degree, (PowerSeries.coeff degree (series ^ exponent)).natDegree ≤ degree := by
    intro exponent
    induction exponent with
    | zero =>
        intro degree
        simp only [pow_zero, PowerSeries.coeff_one]
        split_ifs <;> simp
    | succ exponent ih =>
        rw [pow_succ]
        simpa using hdegreeMul (series ^ exponent) series 0 0
          (by simpa using ih) (by simpa using hseries)
  have halternating : ∀ degree,
      (PowerSeries.coeff degree alternating).natDegree ≤ degree := by
    intro degree
    simp [alternating]
  have hgeometric : ∀ degree,
      (PowerSeries.coeff degree geometric).natDegree ≤ degree := by
    intro degree
    simp [geometric]
  have hone : ∀ degree,
      (PowerSeries.coeff degree (1 + PowerSeries.X :
        PowerSeries (Polynomial ℚ))).natDegree ≤ degree := by
    intro degree
    by_cases hzero : degree = 0
    · subst degree; simp
    · by_cases hone : degree = 1
      · subst degree; simp
      · simp [PowerSeries.coeff_X, hzero, hone]
  have hterm (depth degree first : ℕ) (hfirst : first ≤ depth) :
      (PowerSeries.coeff degree
        (PowerSeries.X ^ depth * alternating ^ (2 * depth) *
          (1 + PowerSeries.X) ^ first *
          PowerSeries.C ((1 - Polynomial.X) ^ first) * geometric ^ (first + 1))).natDegree ≤
        degree := by
    have hconstant : ∀ index,
        (PowerSeries.coeff index (PowerSeries.C ((1 - Polynomial.X) ^ first) :
          PowerSeries (Polynomial ℚ))).natDegree ≤ index + first := by
      intro index
      by_cases hzero : index = 0
      · subst index
        simp only [PowerSeries.coeff_zero_C, zero_add]
        calc
          ((1 - Polynomial.X : Polynomial ℚ) ^ first).natDegree ≤
              first * (1 - Polynomial.X : Polynomial ℚ).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ first := by
            have hbound := Polynomial.natDegree_sub_le
              (1 : Polynomial ℚ) Polynomial.X
            simp only [Polynomial.natDegree_one, Polynomial.natDegree_X, max_eq_right
              (by decide : 0 ≤ 1)] at hbound
            simpa using Nat.mul_le_mul_left first hbound
      · rw [PowerSeries.coeff_C, if_neg hzero]
        simp
    have hbase := hdegreeMul (alternating ^ (2 * depth))
      ((1 + PowerSeries.X) ^ first) 0 0
      (by simpa using hdegreePow alternating halternating (2 * depth))
      (by simpa using hdegreePow (1 + PowerSeries.X) hone first)
    have hmiddle := hdegreeMul
      (alternating ^ (2 * depth) * (1 + PowerSeries.X) ^ first)
      (PowerSeries.C ((1 - Polynomial.X) ^ first)) 0 first hbase hconstant
    have hfull := hdegreeMul
      (alternating ^ (2 * depth) * (1 + PowerSeries.X) ^ first *
        PowerSeries.C ((1 - Polynomial.X) ^ first))
      (geometric ^ (first + 1)) first 0 (by simpa using hmiddle)
      (by simpa using hdegreePow geometric hgeometric (first + 1))
    simp only [mul_assoc]
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with hlarge
    · simpa only [← mul_assoc] using (hfull (degree - depth)).trans (by omega)
    · simp
  have hsupport (degree index : ℕ) (hlarge : degree < index) :
      (PowerSeries.coeff degree rightNormalized).coeff index = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt _ hlarge
    simp only [rightNormalized, PowerSeries.coeff_mk]
    change (∑ depth ∈ Finset.range (degree + 1),
      (walkEndpoints false depth).sum fun label weight =>
        (weight : ℚ) • PowerSeries.coeff degree
          (PowerSeries.X ^ depth * alternating ^ (2 * depth) *
            (1 + PowerSeries.X) ^ label.1 *
            PowerSeries.C ((1 - Polynomial.X) ^ label.1) *
            geometric ^ (label.1 + 1))).natDegree ≤ degree
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro depth _
    unfold Finsupp.sum
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro label hlabel
    apply (Polynomial.natDegree_smul_le _ _).trans
    have hsupport :=
      (forward_series_equations (R := ℚ) false depth).1.2.1 label
        (Finsupp.mem_support_iff.mp hlabel)
    exact hterm depth degree label.1 (by omega)
  have hboundary :
      PowerSeries.map (Polynomial.evalRingHom (1 : ℚ)) rightNormalized =
        PowerSeries.mk (fun _ => (1 : ℚ)) := by
    apply PowerSeries.ext
    intro degree
    simp only [PowerSeries.coeff_map, rightNormalized, PowerSeries.coeff_mk]
    change (Polynomial.evalRingHom (1 : ℚ))
      (∑ depth ∈ Finset.range (degree + 1),
        (walkEndpoints false depth).sum fun label weight =>
          (weight : ℚ) • PowerSeries.coeff degree
            (PowerSeries.X ^ depth * alternating ^ (2 * depth) *
              (1 + PowerSeries.X) ^ label.1 *
              PowerSeries.C ((1 - Polynomial.X) ^ label.1) *
              geometric ^ (label.1 + 1))) = 1
    rw [map_sum]
    rw [Finset.sum_eq_single 0]
    · simp [walkEndpoints, geometric]
    · intro depth _ hdepth
      unfold Finsupp.sum
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro label hlabel
      have hpositive :=
        (forward_series_equations (R := ℚ) false depth).1.2.2.1 rfl hdepth label
          (Finsupp.mem_support_iff.mp hlabel)
      have hmap : PowerSeries.map (Polynomial.evalRingHom (1 : ℚ))
          (PowerSeries.X ^ depth * alternating ^ (2 * depth) *
            (1 + PowerSeries.X) ^ label.1 *
            PowerSeries.C ((1 - Polynomial.X) ^ label.1) *
            geometric ^ (label.1 + 1)) = 0 := by
        simp [map_mul, map_pow, PowerSeries.map_C, Polynomial.evalRingHom,
          ne_of_gt hpositive]
      change Polynomial.eval 1 (_ • _) = 0
      rw [Polynomial.eval_smul]
      have hzero := congrArg (PowerSeries.coeff degree) hmap
      simp only [PowerSeries.coeff_map, map_zero] at hzero
      change Polynomial.eval 1 _ = 0 at hzero
      rw [hzero, smul_zero]
    · simp
  refine ⟨hsupport, ?_, ?_⟩
  · rw [hboundary]
    exact PowerSeries.mk_one_mul_one_sub_eq_one ℚ
  · let : UniformSpace (Polynomial ℚ) := ⊥
    let : DiscreteUniformity (Polynomial ℚ) := ⟨rfl⟩
    let parameter := PowerSeries.X * alternating ^ 2
    let image := (1 + PowerSeries.X) * PowerSeries.C (1 - Polynomial.X) * geometric
    let nextGeometric := PowerSeries.invOfUnit
      (1 - PowerSeries.X ^ 2 * PowerSeries.C (Polynomial.X : Polynomial ℚ)) 1
    let nextImage := (1 + PowerSeries.X) *
      (1 - PowerSeries.X * PowerSeries.C (Polynomial.X : Polynomial ℚ)) * nextGeometric
    have hexpand (degree depth : ℕ) :
        PowerSeries.coeff degree
          (PowerSeries.coeff depth (forwardSeries false image 1) *
            parameter ^ depth * geometric) =
        (walkEndpoints false depth).sum fun label weight =>
          (weight : ℚ) • PowerSeries.coeff degree
            (PowerSeries.X ^ depth * alternating ^ (2 * depth) *
              (1 + PowerSeries.X) ^ label.1 *
              PowerSeries.C ((1 - Polynomial.X) ^ label.1) *
              geometric ^ (label.1 + 1)) := by
      simp only [forwardSeries, PowerSeries.coeff_mk,
        Finsupp.linearCombination_apply, Finsupp.sum, one_pow, mul_one,
        Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro label _
      simp only [smul_mul_assoc, map_zsmul]
      rw [← Int.cast_smul_eq_zsmul ℚ (M := Polynomial ℚ)]
      apply congrArg (fun value : Polynomial ℚ =>
        ((walkEndpoints false depth) label : ℚ) • value)
      apply congrArg (PowerSeries.coeff degree)
      dsimp only [image, parameter]
      simp only [mul_pow, pow_mul, ← map_pow, pow_succ]
      ring
    have hparameter : PowerSeries.HasEval parameter :=
      PowerSeries.HasEval.mul_right (alternating ^ 2) PowerSeries.HasEval.X
    have hsum := (PowerSeries.hasSum_eval₂
      (φ := RingHom.id (PowerSeries (Polynomial ℚ))) continuous_id hparameter
      (forwardSeries false image 1)).mul_right geometric
    simp only [RingHom.id_apply] at hsum
    have hevaluation :
        PowerSeries.eval₂ (RingHom.id (PowerSeries (Polynomial ℚ))) parameter
          (forwardSeries false image 1) * geometric = rightNormalized := by
      apply hsum.unique
      apply (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (Polynomial ℚ)).mpr
      intro degree
      have hzero (depth : ℕ) (hdepth : depth ∉ Finset.range (degree + 1)) :
          PowerSeries.coeff degree
            (PowerSeries.coeff depth (forwardSeries false image 1) *
              parameter ^ depth * geometric) = 0 := by
        have hdiv : (PowerSeries.X : PowerSeries (Polynomial ℚ)) ^ depth ∣
            PowerSeries.coeff depth (forwardSeries false image 1) *
              parameter ^ depth * geometric := by
          refine ⟨PowerSeries.coeff depth (forwardSeries false image 1) *
            (alternating ^ 2) ^ depth * geometric, ?_⟩
          dsimp only [parameter]
          ring
        exact PowerSeries.X_pow_dvd_iff.mp hdiv degree (by
          simp only [Finset.mem_range, not_lt] at hdepth
          omega)
      convert hasSum_sum_of_ne_finset_zero hzero using 1
      · simp only [rightNormalized, PowerSeries.coeff_mk]
        apply Finset.sum_congr rfl
        intro depth _
        exact (hexpand degree depth).symm
      · infer_instance
    refine ⟨hevaluation, ?_⟩
    let collapse : PowerSeries (PowerSeries (Polynomial ℚ)) →+*
        PowerSeries (Polynomial ℚ) :=
      PowerSeries.eval₂Hom (φ := RingHom.id _) continuous_id hparameter
    let coordinate : PowerSeries (Polynomial ℚ) := PowerSeries.C Polynomial.X
    have hC (value : PowerSeries (Polynomial ℚ)) :
        collapse (PowerSeries.C value) = value := by
      simp [collapse, PowerSeries.coe_eval₂Hom]
    have hX : collapse PowerSeries.X = parameter := by
      simp [collapse, PowerSeries.coe_eval₂Hom]
    have halternatingInverse : (1 + PowerSeries.X) * alternating = 1 := by
      apply PowerSeries.ext
      intro degree
      cases degree with
      | zero => simp [alternating]
      | succ degree =>
          simp only [add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul,
            alternating, PowerSeries.coeff_mk, PowerSeries.coeff_one,
            Nat.succ_ne_zero, if_false, pow_succ]
          ring
    have hgeometricInverse : (1 - PowerSeries.X * coordinate) * geometric = 1 := by
      apply PowerSeries.ext
      intro degree
      cases degree with
      | zero => simp [geometric, coordinate]
      | succ degree =>
          simp only [sub_mul, one_mul, mul_assoc, map_sub,
            PowerSeries.coeff_succ_X_mul, coordinate, PowerSeries.coeff_C_mul,
            geometric, PowerSeries.coeff_mk, PowerSeries.coeff_one,
            Nat.succ_ne_zero, if_false, pow_succ]
          ring
    have hnextInverse :
        (1 - PowerSeries.X ^ 2 * coordinate) * nextGeometric = 1 :=
      PowerSeries.mul_invOfUnit _ 1 (by simp [coordinate])
    have hkernelInverse : (1 - parameter * image) * nextImage = 1 := by
      have hproduct : parameter * image * nextImage =
          PowerSeries.X * PowerSeries.C (1 - Polynomial.X) * nextGeometric := by
        calc
          parameter * image * nextImage =
              PowerSeries.X * PowerSeries.C (1 - Polynomial.X) * nextGeometric *
                ((1 + PowerSeries.X) * alternating) ^ 2 *
                ((1 - PowerSeries.X * coordinate) * geometric) := by
                  dsimp only [parameter, image, nextImage, coordinate]
                  ring
          _ = _ := by rw [halternatingInverse, hgeometricInverse]; ring
      rw [sub_mul, one_mul, hproduct]
      dsimp only [nextImage]
      simp only [map_sub, map_one]
      convert hnextInverse using 1
      ring
    have hforward :=
      (forward_series_equations (R := PowerSeries (Polynomial ℚ)) false 0).1.2.2.2.1
        image nextImage
    dsimp only at hforward
    have hcollapsed := congrArg collapse hforward
    simp only [map_mul, map_add, map_sub, map_one, hC, hX] at hcollapsed
    have hdifference := congrArg collapse
      ((forward_series_equations (R := PowerSeries (Polynomial ℚ)) false 0).1.2.2.2.2.2
        rfl image)
    simp only [map_mul, map_add, map_sub, map_one, hC, hX] at hdifference
    have hproduct : (1 - nextImage) * image *
        (parameter * nextImage * collapse (forwardSeries false nextImage 1) -
          (1 - image + parameter * image + parameter * image ^ 2) *
            collapse (forwardSeries false image 1) -
          (image - nextImage) *
            (1 - parameter * collapse (forwardSeries false 1 1))) = 0 := by
      linear_combination hcollapsed +
        ((image - nextImage) * collapse (forwardSeries false image nextImage) +
          nextImage * (1 - image) * collapse (forwardSeries false image 1)) *
            hkernelInverse + (1 - nextImage) * (image - nextImage) * hdifference
    have himageNonzero : image ≠ 0 := by
      intro hzero
      have hconstant := congrArg PowerSeries.constantCoeff hzero
      simp only [image, map_mul, map_add, map_one, PowerSeries.constantCoeff_X,
        add_zero, one_mul, PowerSeries.constantCoeff_C, geometric,
        PowerSeries.constantCoeff_mk, pow_zero, mul_one, map_zero] at hconstant
      have hcoefficient := congrArg (fun poly : Polynomial ℚ => poly.coeff 0) hconstant
      norm_num at hcoefficient
    have halternatingNonzero : alternating ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at halternatingInverse
      exact zero_ne_one halternatingInverse
    have hparameterNonzero : parameter ≠ 0 :=
      mul_ne_zero PowerSeries.X_ne_zero (pow_ne_zero _ halternatingNonzero)
    have hnextNontrivial : 1 - nextImage ≠ 0 := by
      intro hzero
      have hone : nextImage = 1 := by linear_combination -hzero
      rw [hone, mul_one] at hkernelInverse
      have hvanish : parameter * image = 0 := by linear_combination -hkernelInverse
      exact mul_ne_zero hparameterNonzero himageNonzero hvanish
    have hkernel := (mul_eq_zero.mp hproduct).resolve_left
      (mul_ne_zero hnextNontrivial himageNonzero)
    have hnormalized : collapse (forwardSeries false image 1) * geometric =
        rightNormalized := by
      simpa only [collapse, PowerSeries.coe_eval₂Hom] using hevaluation
    have hleftFactor :
        (1 + PowerSeries.X) * (1 - PowerSeries.X * coordinate) *
            (parameter * nextImage) =
          PowerSeries.X * (1 - PowerSeries.X * coordinate) ^ 2 * nextGeometric := by
      calc
        _ = PowerSeries.X * (1 - PowerSeries.X * coordinate) ^ 2 * nextGeometric *
            ((1 + PowerSeries.X) * alternating) ^ 2 := by
              dsimp only [parameter, nextImage, coordinate]
              ring
        _ = _ := by rw [halternatingInverse]; ring
    have hdiagonalFactor :
        (1 + PowerSeries.X) * (1 - PowerSeries.X * coordinate) ^ 2 *
          (1 - image + parameter * image + parameter * image ^ 2) =
        PowerSeries.X +
          (1 - 2 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) *
            coordinate + PowerSeries.X ^ 2 * coordinate ^ 2 := by
      have hgeometricSquare :
          ((1 - PowerSeries.X * coordinate) * geometric) ^ 2 = 1 := by
        rw [hgeometricInverse]; ring
      have halternatingSquare : ((1 + PowerSeries.X) * alternating) ^ 2 = 1 := by
        rw [halternatingInverse]; ring
      dsimp only [image, parameter]
      simp only [map_sub, map_one]
      linear_combination
        (-(1 + PowerSeries.X) ^ 2 * (1 - coordinate) *
            (1 - PowerSeries.X * coordinate) +
          PowerSeries.X * (1 - coordinate) * (1 - PowerSeries.X * coordinate)) *
          hgeometricInverse +
        PowerSeries.X * (1 + PowerSeries.X) * (1 - coordinate) ^ 2 *
          hgeometricSquare +
        (PowerSeries.X * (1 - coordinate) * (1 - PowerSeries.X * coordinate) ^ 2 *
            geometric +
          PowerSeries.X * (1 + PowerSeries.X) * (1 - coordinate) ^ 2 *
            (1 - PowerSeries.X * coordinate) ^ 2 * geometric ^ 2) * halternatingSquare
    have hboundaryFactor :
        (1 + PowerSeries.X) * (1 - PowerSeries.X * coordinate) *
            (image - nextImage) =
          -(1 - PowerSeries.X ^ 2) ^ 2 * coordinate * nextGeometric := by
      dsimp only [image, nextImage]
      simp only [map_sub, map_one]
      linear_combination
        (1 + PowerSeries.X) ^ 2 * (1 - coordinate) * hgeometricInverse -
        (1 + PowerSeries.X) ^ 2 * (1 - coordinate) * hnextInverse
    have hactual : collapse (forwardSeries false image 1) =
        (1 - PowerSeries.X * coordinate) * rightNormalized := by
      rw [← hnormalized]
      linear_combination -collapse (forwardSeries false image 1) * hgeometricInverse
    have hcleared := congrArg
      (fun value => (1 + PowerSeries.X) *
        (1 - PowerSeries.X * coordinate) * value) hkernel
    rw [hactual] at hcleared
    have hfinish :
        PowerSeries.X * (1 - PowerSeries.X * coordinate) ^ 2 *
            (collapse (forwardSeries false nextImage 1) * nextGeometric) =
          (PowerSeries.X +
              (1 - 2 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) *
                coordinate + PowerSeries.X ^ 2 * coordinate ^ 2) * rightNormalized -
            (1 - parameter * collapse (forwardSeries false 1 1)) *
              (1 - PowerSeries.X ^ 2) ^ 2 * coordinate * nextGeometric := by
      linear_combination hcleared -
        collapse (forwardSeries false nextImage 1) * hleftFactor +
        rightNormalized * hdiagonalFactor +
        (1 - parameter * collapse (forwardSeries false 1 1)) * hboundaryFactor
    let coefficientShift : Polynomial ℚ →+* PowerSeries (Polynomial ℚ) :=
      Polynomial.eval₂RingHom (PowerSeries.C.comp Polynomial.C)
        (PowerSeries.X * coordinate)
    have hcoefficientContinuous : Continuous coefficientShift :=
      continuous_of_discreteTopology
    let shift : PowerSeries (Polynomial ℚ) →+* PowerSeries (Polynomial ℚ) :=
      PowerSeries.eval₂Hom hcoefficientContinuous PowerSeries.HasEval.X
    have hshiftContinuous : Continuous shift := by
      simpa only [shift, PowerSeries.coe_eval₂Hom] using
        PowerSeries.continuous_eval₂ hcoefficientContinuous PowerSeries.HasEval.X
    have hshiftX : shift PowerSeries.X = PowerSeries.X := by
      simp [shift, PowerSeries.coe_eval₂Hom]
    have hshiftCoordinate : shift coordinate = PowerSeries.X * coordinate := by
      simp [shift, PowerSeries.coe_eval₂Hom, coefficientShift, coordinate,
        Polynomial.coe_eval₂RingHom]
    have hshiftAlternating : shift alternating = alternating := by
      have hshifted := congrArg shift halternatingInverse
      simp only [map_mul, map_add, map_one, hshiftX] at hshifted
      have hfactorNonzero : (1 + PowerSeries.X : PowerSeries (Polynomial ℚ)) ≠ 0 := by
        intro hzero
        have hconstant := congrArg PowerSeries.constantCoeff hzero
        simp at hconstant
      exact mul_left_cancel₀ hfactorNonzero (hshifted.trans halternatingInverse.symm)
    have hshiftGeometric : shift geometric = nextGeometric := by
      have hshifted := congrArg shift hgeometricInverse
      simp only [map_mul, map_sub, map_one, hshiftX, hshiftCoordinate] at hshifted
      have hfactorNonzero : (1 - PowerSeries.X ^ 2 * coordinate) ≠ 0 := by
        intro hzero
        have hconstant := congrArg PowerSeries.constantCoeff hzero
        simp at hconstant
      apply mul_left_cancel₀ hfactorNonzero
      convert hshifted.trans hnextInverse.symm using 1
      ring
    have hshiftParameter : shift parameter = parameter := by
      simp only [parameter, map_mul, map_pow, hshiftX, hshiftAlternating]
    have hshiftImage : shift image = nextImage := by
      have himage : image = (1 + PowerSeries.X) * (1 - coordinate) * geometric := by
        simp [image, coordinate]
      rw [himage]
      simp only [map_mul, map_add, map_sub, map_one, hshiftX,
        hshiftCoordinate, hshiftGeometric]
      rfl
    have hforwardShift (depth : ℕ) :
        shift (PowerSeries.coeff depth (forwardSeries false image 1)) =
          PowerSeries.coeff depth (forwardSeries false nextImage 1) := by
      simp only [forwardSeries, PowerSeries.coeff_mk, Finsupp.linearCombination_apply,
        Finsupp.sum, one_pow, mul_one, zsmul_eq_mul, map_sum, map_mul, map_intCast,
        map_pow, hshiftImage]
    have hshiftedEvaluation : shift rightNormalized =
        collapse (forwardSeries false nextImage 1) * nextGeometric := by
      have hshifted : HasSum
          (fun depth => PowerSeries.coeff depth (forwardSeries false nextImage 1) *
            parameter ^ depth * nextGeometric) (shift rightNormalized) := by
        convert hsum.map shift hshiftContinuous using 1
        · funext depth
          simp only [Function.comp_apply, map_mul, map_pow, hforwardShift,
            hshiftParameter, hshiftGeometric]
        · rw [hevaluation]
      have hnextSum := (PowerSeries.hasSum_eval₂
        (φ := RingHom.id (PowerSeries (Polynomial ℚ))) continuous_id hparameter
        (forwardSeries false nextImage 1)).mul_right nextGeometric
      simp only [RingHom.id_apply] at hnextSum
      simpa only [collapse, PowerSeries.coe_eval₂Hom] using hshifted.unique hnextSum
    have hcoefficientShift (poly : Polynomial ℚ) (degree : ℕ) :
        PowerSeries.coeff degree (coefficientShift poly) =
          Polynomial.monomial degree (poly.coeff degree) := by
      induction poly using Polynomial.induction_on' with
      | add left right hleft hright =>
          simp only [map_add, Polynomial.coeff_add, hleft, hright]
      | monomial index value =>
          simp only [coefficientShift, Polynomial.coe_eval₂RingHom,
            Polynomial.eval₂_monomial, RingHom.comp_apply, mul_pow,
            PowerSeries.coeff_C_mul, coordinate]
          have hpower :
              (PowerSeries.C (Polynomial.X : Polynomial ℚ)) ^ index =
                PowerSeries.C (Polynomial.X ^ index) :=
            (map_pow PowerSeries.C Polynomial.X index).symm
          rw [hpower]
          rw [PowerSeries.coeff_X_pow_mul']
          by_cases hle : index ≤ degree
          · rw [if_pos hle]
            by_cases heq : degree = index
            · subst degree
              simp [Polynomial.C_mul_X_pow_eq_monomial]
            · have hsub : degree - index ≠ 0 := by omega
              rw [PowerSeries.coeff_C, if_neg hsub]
              simp only [mul_zero, Polynomial.coeff_monomial,
                if_neg (Ne.symm heq), map_zero]
          · rw [if_neg hle]
            simp [Polynomial.coeff_monomial, show index ≠ degree by omega]
    have hshiftCoefficient (series : PowerSeries (Polynomial ℚ)) (degree index : ℕ) :
        (PowerSeries.coeff degree (shift series)).coeff index =
          if index ≤ degree then
            (PowerSeries.coeff (degree - index) series).coeff index else 0 := by
      have hseriesSum := PowerSeries.hasSum_eval₂ hcoefficientContinuous
        (PowerSeries.HasEval.X (R := Polynomial ℚ)) series
      have hdegreeSum :=
        ((PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff (Polynomial ℚ)).mp
          hseriesSum) degree
      have hzero (depth : ℕ) (hdepth : depth ∉ Finset.range (degree + 1)) :
          PowerSeries.coeff degree
            (coefficientShift (PowerSeries.coeff depth series) * PowerSeries.X ^ depth) =
              0 := by
        rw [PowerSeries.coeff_mul_X_pow', if_neg (by
          simp only [Finset.mem_range, not_lt] at hdepth
          omega)]
      have hformula := hdegreeSum.unique (hasSum_sum_of_ne_finset_zero hzero)
      rw [← PowerSeries.coe_eval₂Hom hcoefficientContinuous PowerSeries.HasEval.X]
        at hformula
      change PowerSeries.coeff degree (shift series) = _ at hformula
      rw [hformula]
      simp only [Polynomial.finsetSum_coeff, PowerSeries.coeff_mul_X_pow',
        hcoefficientShift]
      by_cases hindex : index ≤ degree
      · rw [if_pos hindex, Finset.sum_eq_single (degree - index)]
        · rw [if_pos (by omega)]
          simp [show degree - (degree - index) = index by omega]
        · intro depth hdepth hne
          have hbound : depth ≤ degree := by
            have := Finset.mem_range.mp hdepth
            omega
          rw [if_pos hbound]
          simp [Polynomial.coeff_monomial, show degree - depth ≠ index by omega]
        · intro hnot
          exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
      · rw [if_neg hindex]
        apply Finset.sum_eq_zero
        intro depth hdepth
        have hbound : depth ≤ degree := by
          have := Finset.mem_range.mp hdepth
          omega
        rw [if_pos hbound]
        simp [Polynomial.coeff_monomial, show degree - depth ≠ index by omega]
    let residual := 1 - parameter * collapse (forwardSeries false 1 1)
    let scalarResidual := PowerSeries.map (Polynomial.evalRingHom (0 : ℚ)) residual
    let column (index : ℕ) : PowerSeries (Polynomial ℚ) →+ PowerSeries ℚ :=
      { toFun := fun series => PowerSeries.mk fun degree =>
          (PowerSeries.coeff degree series).coeff index
        map_zero' := by ext degree; simp
        map_add' := by intros left right; ext degree; simp }
    have hrootShift : shift (collapse (forwardSeries false 1 1)) =
        collapse (forwardSeries false 1 1) := by
      have hrootSum := PowerSeries.hasSum_eval₂
        (φ := RingHom.id (PowerSeries (Polynomial ℚ))) continuous_id hparameter
        (forwardSeries false 1 1)
      simp only [RingHom.id_apply] at hrootSum
      have hrootCoefficient (depth : ℕ) :
          shift (PowerSeries.coeff depth
            (forwardSeries false (1 : PowerSeries (Polynomial ℚ)) 1)) =
              PowerSeries.coeff depth (forwardSeries false 1 1) := by
        simp only [forwardSeries, PowerSeries.coeff_mk, Finsupp.linearCombination_apply,
          Finsupp.sum, one_pow, mul_one, zsmul_eq_mul, map_sum, map_intCast]
      have hshifted : HasSum
          (fun depth => PowerSeries.coeff depth (forwardSeries false 1 1) *
            parameter ^ depth) (shift (collapse (forwardSeries false 1 1))) := by
        convert hrootSum.map shift hshiftContinuous using 1
        · funext depth
          simp only [Function.comp_apply, map_mul, map_pow,
            hrootCoefficient, hshiftParameter]
        · simp only [collapse, PowerSeries.coe_eval₂Hom]
      simpa only [collapse, PowerSeries.coe_eval₂Hom] using hshifted.unique hrootSum
    have hresidualFixed : shift residual = residual := by
      simp only [residual, map_sub, map_one, map_mul, hrootShift, hshiftParameter]
    have hresidualSupport (degree index : ℕ) (hpositive : 0 < index) :
        (PowerSeries.coeff degree residual).coeff index = 0 := by
      induction degree using Nat.strong_induction_on with
      | h degree ih =>
          have hcoefficient := hshiftCoefficient residual degree index
          rw [hresidualFixed] at hcoefficient
          by_cases hbound : index ≤ degree
          · rw [if_pos hbound] at hcoefficient
            exact hcoefficient.trans (ih (degree - index) (by omega))
          · simpa only [if_neg hbound] using hcoefficient
    have hresidualScalar : residual = PowerSeries.map Polynomial.C scalarResidual := by
      apply PowerSeries.ext
      intro degree
      apply Polynomial.ext
      intro index
      by_cases hzero : index = 0
      · subst index
        simp [scalarResidual, PowerSeries.coeff_map, Polynomial.coeff_zero_eq_eval_zero]
      · rw [hresidualSupport degree index (by omega)]
        simp [PowerSeries.coeff_map, Polynomial.coeff_C, hzero]
    have hcolumnMultiply (index : ℕ) (factor : PowerSeries ℚ)
        (series : PowerSeries (Polynomial ℚ)) :
        column index (PowerSeries.map Polynomial.C factor * series) =
          factor * column index series := by
      apply PowerSeries.ext
      intro degree
      simp only [column, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PowerSeries.coeff_mk,
        PowerSeries.coeff_mul, Polynomial.finsetSum_coeff, PowerSeries.coeff_map,
        Polynomial.coeff_C_mul]
    have hcolumnCoordinate (index : ℕ) (series : PowerSeries (Polynomial ℚ)) :
        column (index + 1) (coordinate * series) = column index series := by
      ext degree
      simp [column, coordinate, PowerSeries.coeff_C_mul,
        Polynomial.coeff_X_mul]
    have hcolumnCoordinateZero (series : PowerSeries (Polynomial ℚ)) :
        column 0 (coordinate * series) = 0 := by
      ext degree
      simp [column, coordinate, PowerSeries.coeff_C_mul]
    have hcolumnDouble (index : ℕ) (series : PowerSeries (Polynomial ℚ)) :
        column (index + 1) (coordinate ^ 2 * series) =
          if index = 0 then 0 else column (index - 1) series := by
      rw [pow_two, mul_assoc, hcolumnCoordinate]
      cases index with
      | zero => simp [hcolumnCoordinateZero]
      | succ index => simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel,
          hcolumnCoordinate]
    have hcolumnOne (index : ℕ) :
        column index 1 = if index = 0 then 1 else 0 := by
      by_cases hindex : index = 0
      · subst index
        ext degree
        by_cases hdegree : degree = 0 <;> simp [column, hdegree]
      · ext degree
        by_cases hdegree : degree = 0 <;>
          simp [column, hdegree, hindex, Polynomial.coeff_one]
    have hnextGeometricColumn (index : ℕ) :
        column index nextGeometric = PowerSeries.X ^ (2 * index) := by
      induction index with
      | zero =>
          have hrelation := congrArg (column 0) hnextInverse
          have hrewritten : (1 - PowerSeries.X ^ 2 * coordinate) * nextGeometric =
              nextGeometric - PowerSeries.map Polynomial.C (PowerSeries.X ^ 2) *
                (coordinate * nextGeometric) := by
            simp only [map_pow, PowerSeries.map_X]
            ring
          rw [hrewritten, map_sub, hcolumnMultiply, hcolumnCoordinateZero,
            hcolumnOne] at hrelation
          simpa using hrelation
      | succ index ih =>
          have hrelation := congrArg (column (index + 1)) hnextInverse
          have hrewritten : (1 - PowerSeries.X ^ 2 * coordinate) * nextGeometric =
              nextGeometric - PowerSeries.map Polynomial.C (PowerSeries.X ^ 2) *
                (coordinate * nextGeometric) := by
            simp only [map_pow, PowerSeries.map_X]
            ring
          rw [hrewritten, map_sub, hcolumnMultiply, hcolumnCoordinate,
            hcolumnOne, if_neg (by omega), ih] at hrelation
          rw [show 2 * (index + 1) = 2 * index + 2 by omega, pow_add]
          linear_combination hrelation
    let nextNormalized := collapse (forwardSeries false nextImage 1) * nextGeometric
    have hnextColumn (index : ℕ) : column index nextNormalized =
        PowerSeries.X ^ index * column index rightNormalized := by
      apply PowerSeries.ext
      intro degree
      simp only [column, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PowerSeries.coeff_mk]
      rw [PowerSeries.coeff_X_pow_mul']
      dsimp only [nextNormalized]
      rw [← hshiftedEvaluation]
      simp only [PowerSeries.coeff_mk]
      exact hshiftCoefficient rightNormalized degree index
    have hexpanded :
        PowerSeries.map Polynomial.C PowerSeries.X * nextNormalized -
          PowerSeries.map Polynomial.C (2 * PowerSeries.X ^ 2) *
            (coordinate * nextNormalized) +
          PowerSeries.map Polynomial.C (PowerSeries.X ^ 3) *
            (coordinate ^ 2 * nextNormalized) =
        PowerSeries.map Polynomial.C PowerSeries.X * rightNormalized +
          PowerSeries.map Polynomial.C
              (1 - 2 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) *
            (coordinate * rightNormalized) +
          PowerSeries.map Polynomial.C (PowerSeries.X ^ 2) *
            (coordinate ^ 2 * rightNormalized) -
          PowerSeries.map Polynomial.C
              (scalarResidual * (1 - PowerSeries.X ^ 2) ^ 2) *
            (coordinate * nextGeometric) := by
      simp only [map_mul, map_add, map_sub, map_one, map_pow, map_ofNat,
        PowerSeries.map_X]
      have hforce := hresidualScalar
      simp only [residual] at hforce
      rw [← hforce]
      linear_combination hfinish
    have hcolumnAdd (index : ℕ) (left right : PowerSeries (Polynomial ℚ)) :
        column index (left + right) = column index left + column index right :=
      (column index).map_add left right
    have hcolumnSub (index : ℕ) (left right : PowerSeries (Polynomial ℚ)) :
        column index (left - right) = column index left - column index right :=
      map_sub (column index) left right
    have hresult (index : ℕ) :
        (1 - 2 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
            2 * PowerSeries.X ^ (index + 2)) * column index rightNormalized +
          PowerSeries.X * (1 - PowerSeries.X ^ (index + 1)) *
            column (index + 1) rightNormalized +
          PowerSeries.X ^ 2 * (1 - PowerSeries.X ^ index) *
            column (index - 1) rightNormalized =
          scalarResidual * (1 - PowerSeries.X ^ 2) ^ 2 *
            PowerSeries.X ^ (2 * index) := by
      have hrelation := congrArg (column (index + 1)) hexpanded
      simp only [hcolumnAdd, hcolumnSub, hcolumnMultiply, hcolumnCoordinate, hcolumnDouble,
        hnextGeometricColumn, hnextColumn] at hrelation
      cases index with
      | zero => simp only [if_true, pow_zero, mul_zero] at hrelation
                simp only [pow_zero, sub_self, mul_zero, zero_mul, add_zero]
                linear_combination -hrelation
      | succ index =>
          simp only [Nat.succ_ne_zero, if_false] at hrelation
          simp only [pow_succ, Nat.add_sub_cancel] at hrelation ⊢
          linear_combination -hrelation
    have hconstant : PowerSeries.constantCoeff scalarResidual = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simp [scalarResidual, residual, PowerSeries.coeff_zero_eq_constantCoeff_apply, parameter]
    let inverse := PowerSeries.invOfUnit scalarResidual 1
    have hinverse : scalarResidual * inverse = 1 :=
      PowerSeries.mul_invOfUnit scalarResidual 1 hconstant
    let candidate (index : ℕ) := inverse * column index rightNormalized
    have hcandidate (index : ℕ) :
        (1 + (tridiagonalRow index).1) * candidate index +
          (tridiagonalRow index).2.1 * candidate (index + 1) +
          (tridiagonalRow index).2.2 * candidate (index - 1) =
            (1 - PowerSeries.X ^ 2) ^ 2 * PowerSeries.X ^ (2 * index) := by
      dsimp only [candidate, tridiagonalRow]
      linear_combination inverse * hresult index +
        ((1 - PowerSeries.X ^ 2) ^ 2 * PowerSeries.X ^ (2 * index)) * hinverse
    have hidentification := tridiagonal_solution.2.2 candidate hcandidate
    have hcolumns (index : ℕ) : column index rightNormalized =
        scalarResidual * tridiagonalSeries index := by
      calc
        column index rightNormalized = scalarResidual * candidate index := by
          dsimp only [candidate]
          rw [← mul_assoc, hinverse, one_mul]
        _ = _ := congrArg (fun series => scalarResidual * series index) hidentification
    let total : PowerSeries ℚ := PowerSeries.mk fun degree =>
      ∑ index ∈ Finset.range (degree + 1), PowerSeries.coeff degree (tridiagonalSeries index)
    have hevaluated : PowerSeries.map (Polynomial.evalRingHom (1 : ℚ)) rightNormalized =
        scalarResidual * total := by
      apply PowerSeries.ext
      intro degree
      rw [PowerSeries.coeff_map]
      change Polynomial.eval 1 (PowerSeries.coeff degree rightNormalized) = _
      have hdegree := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (hsupport degree)
      rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdegree (Nat.lt_succ_self degree))]
      simp only [one_pow, mul_one]
      calc
        _ = ∑ index ∈ Finset.range (degree + 1),
            PowerSeries.coeff degree (scalarResidual * tridiagonalSeries index) := by
          apply Finset.sum_congr rfl
          intro index _
          simpa only [column, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PowerSeries.coeff_mk] using
            congrArg (PowerSeries.coeff degree) (hcolumns index)
        _ = _ := by
          simp only [total, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro pair hpair
          rw [← Finset.mul_sum]
          congr 1
          have hpairDegree := Finset.mem_antidiagonal.mp hpair
          symm
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro index _ hindex
          apply PowerSeries.X_pow_dvd_iff.mp (tridiagonal_solution.1 index)
          simp only [Finset.mem_range] at hindex
          omega
    have hscalar : scalarResidual * rightScalarSeries = 1 := by
      calc
        scalarResidual * rightScalarSeries =
            PowerSeries.map (Polynomial.evalRingHom (1 : ℚ)) rightNormalized *
              (1 - PowerSeries.X) := by
          rw [hevaluated]
          change scalarResidual * ((1 - PowerSeries.X) * total) = _
          ring
        _ = 1 := by
          rw [hboundary]
          exact PowerSeries.mk_one_mul_one_sub_eq_one ℚ
    refine ⟨?_, ?_, ?_⟩
    · intro index
      simpa only [column, AddMonoidHom.coe_mk, ZeroHom.coe_mk, scalarResidual,
        residual, collapse, PowerSeries.coe_eval₂Hom] using hcolumns index
    · simpa only [scalarResidual, residual, collapse, PowerSeries.coe_eval₂Hom] using hscalar
    · have hzero := congrArg PowerSeries.constantCoeff hscalar
      simpa only [map_mul, map_one, hconstant, one_mul] using hzero

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Normalization
