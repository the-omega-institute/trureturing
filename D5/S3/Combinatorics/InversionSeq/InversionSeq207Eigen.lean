/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Eigen
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Eigen
   mirror-E: none(waiver:formal-polynomial-eigenrelation)
   anchors: []
   utility: none
   digest: Support induction and Euler shifts construct the symmetric polynomial eigenbasis. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Difference

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Polynomials

open InversionSeq207Euler InversionSeq207Difference

universe fieldUniverse

set_option maxHeartbeats 2400000 in
theorem polynomial_system :
    (PowerSeries.constantCoeff polynomialGenerator = 1) ∧
    (∀ index : ℕ,
      (1 - LaurentPolynomial.C (PowerSeries.X ^ (2 * (index + 1)))) *
          PowerSeries.coeff (index + 1) polynomialGenerator =
        (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) -
            2 * LaurentPolynomial.C (PowerSeries.X ^ (2 * index + 1))) *
            PowerSeries.coeff index polynomialGenerator -
          (1 - LaurentPolynomial.C (PowerSeries.X ^ (2 * index))) *
            (if index = 0 then 0 else
              PowerSeries.coeff (index - 1) polynomialGenerator)) ∧
    (∀ index : ℕ,
      LaurentPolynomial.invert (PowerSeries.coeff index polynomialGenerator) =
        PowerSeries.coeff index polynomialGenerator) ∧
    (∀ index : ℕ, ∀ location : ℤ, (index : ℤ) < |location| →
      (PowerSeries.coeff index polynomialGenerator).coeff location = 0) ∧
    (∀ index : ℕ,
      (∏ earlier ∈ Finset.range index,
          (1 - (PowerSeries.X : PowerSeries ℚ) ^ (2 * (earlier + 1)))) *
          (PowerSeries.coeff index polynomialGenerator).coeff (index : ℤ) = 1) ∧
    (∀ degree : ℕ, ∀ poly : LaurentPolynomial (PowerSeries ℚ),
      LaurentPolynomial.invert poly = poly →
      (∀ location : ℤ, (degree : ℤ) < |location| → poly.coeff location = 0) →
      ∃! weights : Fin (degree + 1) → PowerSeries ℚ,
        poly = ∑ index : Fin (degree + 1),
          LaurentPolynomial.C (weights index) *
            PowerSeries.coeff index.val polynomialGenerator) ∧
    (∀ {K : Type fieldUniverse} [Field K]
        (embedding : PowerSeries ℚ →+* K) (hparameter : embedding PowerSeries.X ≠ 0)
        (index : ℕ),
        let rho := embedding PowerSeries.X
        let q := Units.mk0 (rho ^ 2) (pow_ne_zero 2 hparameter)
        let transfer := AddMonoidAlgebra.mapRingHom ℤ embedding
        let poly := transfer (PowerSeries.coeff index polynomialGenerator)
        let indeterminate : LaurentPolynomial K := LaurentPolynomial.T 1
        differenceNumerator rho q poly =
          (1 - indeterminate ^ 2) *
            (1 - LaurentPolynomial.C (q : K) * indeterminate ^ 2) *
            (LaurentPolynomial.C (q : K) - indeterminate ^ 2) *
            (LaurentPolynomial.C ((q : K)⁻¹ ^ index - 1) * poly)) := by
  classical
  let rho : LaurentPolynomial (PowerSeries ℚ) := LaurentPolynomial.C PowerSeries.X
  let q := rho ^ 2
  let lift : PowerSeries ℚ →+* LaurentPolynomial (PowerSeries ℚ) :=
    LaurentPolynomial.C.comp (PowerSeries.expand 2 (by decide)).toRingHom
  let euler := PowerSeries.map lift (PowerSeries.mk eulerCoefficients)
  let numerator := PowerSeries.rescale rho euler
  let first := PowerSeries.rescale (LaurentPolynomial.T 1) euler
  let second := PowerSeries.rescale (LaurentPolynomial.T (-1)) euler
  let denominator := first * second
  let inverse := PowerSeries.invOfUnit denominator 1
  let p := fun index => PowerSeries.coeff index polynomialGenerator
  have heuler : PowerSeries.constantCoeff euler = 1 ∧
      euler = (1 - PowerSeries.X) * PowerSeries.rescale q euler := by
    have hconstant := congrArg lift euler_coefficient_construction.1.1
    have hequation := congrArg (PowerSeries.map lift)
      euler_coefficient_construction.1.2
    have hlift : lift (PowerSeries.X : PowerSeries ℚ) = q := by
      simp [lift, q, rho, PowerSeries.expand_X]
    refine ⟨by simpa [euler, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_mk] using hconstant, ?_⟩
    simpa [euler, map_mul, map_sub, ← PowerSeries.rescale_map, hlift] using hequation
  have hfactor (value : LaurentPolynomial (PowerSeries ℚ)) :
      PowerSeries.rescale value euler =
        (1 - PowerSeries.C value * PowerSeries.X) *
          PowerSeries.rescale q (PowerSeries.rescale value euler) := by
    have hstep := congrArg (PowerSeries.rescale value) heuler.2
    simpa only [map_mul, map_sub, map_one, PowerSeries.rescale_X,
      PowerSeries.rescale_rescale, mul_comm q value] using hstep
  have hnconstant : PowerSeries.constantCoeff numerator = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    change PowerSeries.coeff 0 (PowerSeries.rescale rho euler) = 1
    rw [PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, heuler.1]
  have hdconstant : PowerSeries.constantCoeff denominator = 1 := by
    simp only [denominator, map_mul, first, second,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
      pow_zero, one_mul]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, heuler.1, one_mul]
  have hinverse : denominator * inverse = 1 :=
    PowerSeries.mul_invOfUnit denominator 1 hdconstant
  have hgenerator : polynomialGenerator = numerator ^ 2 * inverse := rfl
  have hzero : p 0 = 1 := by
    simp [p, hgenerator, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hnconstant, inverse]
  have hdenominator : denominator * polynomialGenerator = numerator ^ 2 := by
    rw [hgenerator]
    calc
      _ = numerator ^ 2 * (denominator * inverse) := by ring
      _ = numerator ^ 2 := by rw [hinverse, mul_one]
  have hdnonzero : denominator ≠ 0 := by
    intro hzero
    have h := hdconstant
    rw [hzero, map_zero] at h
    exact zero_ne_one h
  have hfunctional : (1 - PowerSeries.C rho * PowerSeries.X) ^ 2 *
      PowerSeries.rescale q polynomialGenerator =
        (1 - PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X) *
          (1 - PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X) *
            polynomialGenerator := by
    let factor : PowerSeries (LaurentPolynomial (PowerSeries ℚ)) :=
      (1 - PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X) *
      (1 - PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X)
    have hdstep : denominator = factor * PowerSeries.rescale q denominator := by
      calc
        denominator =
            ((1 - PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X) *
                PowerSeries.rescale q first) *
              ((1 - PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X) *
                PowerSeries.rescale q second) :=
          congrArg₂ (· * ·) (hfactor (LaurentPolynomial.T 1))
            (hfactor (LaurentPolynomial.T (-1)))
        _ = factor * PowerSeries.rescale q denominator := by
          change _ = factor * PowerSeries.rescale q (first * second)
          rw [map_mul]
          dsimp only [factor]
          ring
    have hdshift : PowerSeries.rescale q denominator ≠ 0 := by
      intro hzero
      have hconstant : PowerSeries.constantCoeff (PowerSeries.rescale q denominator) =
          1 := by
        simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_rescale, pow_zero, one_mul] using hdconstant
      rw [hzero, map_zero] at hconstant
      exact zero_ne_one hconstant
    apply mul_left_cancel₀ hdshift
    calc
      _ = (1 - PowerSeries.C rho * PowerSeries.X) ^ 2 *
          PowerSeries.rescale q (denominator * polynomialGenerator) := by
            simp only [map_mul]
            ring
      _ = ((1 - PowerSeries.C rho * PowerSeries.X) *
          PowerSeries.rescale q numerator) ^ 2 := by
        rw [hdenominator, map_pow]
        ring
      _ = numerator ^ 2 := (congrArg (· ^ 2) (hfactor rho)).symm
      _ = PowerSeries.rescale q denominator * (factor * polynomialGenerator) := by
        calc
          _ = (factor * PowerSeries.rescale q denominator) * polynomialGenerator := by
            rw [← hdstep, hdenominator]
          _ = _ := by ring
  have hcoeffLinear (value : LaurentPolynomial (PowerSeries ℚ))
      (series : PowerSeries (LaurentPolynomial (PowerSeries ℚ))) (index : ℕ) :
      PowerSeries.coeff (index + 1) (PowerSeries.C value * PowerSeries.X * series) =
        value * PowerSeries.coeff index series := by
    rw [mul_assoc, PowerSeries.coeff_C_mul]
    simpa only [pow_one, Nat.add_comm] using congrArg (value * ·)
      (PowerSeries.coeff_X_pow_mul series 1 index)
  have hcoeffQuadratic (value : LaurentPolynomial (PowerSeries ℚ))
      (series : PowerSeries (LaurentPolynomial (PowerSeries ℚ))) (index : ℕ) :
      PowerSeries.coeff (index + 1) (PowerSeries.C value * PowerSeries.X ^ 2 * series) =
        value * (if index = 0 then 0 else PowerSeries.coeff (index - 1) series) := by
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    by_cases hindex : index = 0
    · subst index
      simp
    · rw [if_pos (by omega), if_neg hindex]
      rw [show index + 1 - 2 = index - 1 by omega]
  have hrecurrence (index : ℕ) :
      (1 - LaurentPolynomial.C (PowerSeries.X ^ (2 * (index + 1)))) * p (index + 1) =
        (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) -
            2 * LaurentPolynomial.C (PowerSeries.X ^ (2 * index + 1))) * p index -
          (1 - LaurentPolynomial.C (PowerSeries.X ^ (2 * index))) *
            (if index = 0 then 0 else p (index - 1)) := by
    have hcoefficient := congrArg (PowerSeries.coeff (index + 1)) hfunctional
    have hexpand :
        (1 - PowerSeries.C rho * PowerSeries.X) ^ 2 *
            PowerSeries.rescale q polynomialGenerator =
          PowerSeries.rescale q polynomialGenerator -
            PowerSeries.C (2 * rho) * PowerSeries.X *
              PowerSeries.rescale q polynomialGenerator +
            PowerSeries.C q * PowerSeries.X ^ 2 *
              PowerSeries.rescale q polynomialGenerator := by
      dsimp only [q]
      simp only [map_mul, map_ofNat, map_pow]
      ring
    have hexpandRight :
        (1 - PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X) *
            (1 - PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X) *
            polynomialGenerator =
          polynomialGenerator - PowerSeries.C
            (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) *
              PowerSeries.X * polynomialGenerator + PowerSeries.C 1 *
                PowerSeries.X ^ 2 * polynomialGenerator := by
      have ht : (LaurentPolynomial.T 1 : LaurentPolynomial (PowerSeries ℚ)) *
          LaurentPolynomial.T (-1) = 1 := by
        rw [← LaurentPolynomial.T_add, show (1 : ℤ) + (-1) = 0 by omega,
          LaurentPolynomial.T_zero]
      have htmap := congrArg PowerSeries.C ht
      simp only [map_mul, map_one] at htmap
      rw [map_add, map_one]
      linear_combination htmap * PowerSeries.X ^ 2 * polynomialGenerator
    rw [hexpand, hexpandRight] at hcoefficient
    simp only [map_add (PowerSeries.coeff (index + 1)),
      map_sub (PowerSeries.coeff (index + 1)), hcoeffLinear, hcoeffQuadratic,
      PowerSeries.coeff_rescale, one_mul] at hcoefficient
    have hpower (index : ℕ) : q ^ index =
        LaurentPolynomial.C (PowerSeries.X ^ (2 * index)) := by
      simp [q, rho, ← map_pow, ← pow_mul]
    have hrho (index : ℕ) : rho * q ^ index =
        LaurentPolynomial.C (PowerSeries.X ^ (2 * index + 1)) := by
      rw [hpower]
      simp only [rho, ← map_mul, ← pow_succ']
    by_cases hindex : index = 0
    · subst index
      simp only [hpower] at hcoefficient
      dsimp only [p]
      simp only [rho, p, ite_true, mul_zero, add_zero, sub_zero, mul_one,
        pow_zero, pow_one, map_one, map_ofNat, map_mul, Nat.zero_add,
        Nat.zero_mul, Nat.zero_sub] at hcoefficient ⊢
      linear_combination -hcoefficient
    · rw [if_neg hindex] at hcoefficient ⊢
      rw [show q * (q ^ (index - 1) * p (index - 1)) =
          q ^ index * p (index - 1) by
            rw [← mul_assoc, ← pow_succ']; congr 2; omega] at hcoefficient
      rw [show 2 * rho * (q ^ index * p index) =
          2 * (rho * q ^ index) * p index by ring, hrho] at hcoefficient
      simp only [hpower] at hcoefficient
      simp only [p, if_neg hindex] at hcoefficient ⊢
      linear_combination -hcoefficient
  have hscalar (value : PowerSeries ℚ) (poly : LaurentPolynomial (PowerSeries ℚ))
      (location : ℤ) : (LaurentPolynomial.C value * poly).coeff location =
        value * poly.coeff location := by
    rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply]
    simp
  have hshift (shift : ℤ) (poly : LaurentPolynomial (PowerSeries ℚ)) (location : ℤ) :
      (LaurentPolynomial.T shift * poly).coeff location = poly.coeff (location - shift) := by
    change (AddMonoidAlgebra.single shift 1 * poly).coeff location = _
    rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
    congr 1
    omega
  have hnonzero (index : ℕ) :
      (1 - (PowerSeries.X : PowerSeries ℚ) ^ (2 * (index + 1))) ≠ 0 := by
    intro hzero
    have hconstant := congrArg PowerSeries.constantCoeff hzero
    simpa using hconstant
  have hcolumn (index : ℕ) (location : ℤ) :
      (1 - PowerSeries.X ^ (2 * (index + 1))) * (p (index + 1)).coeff location =
        (p index).coeff (location - 1) + (p index).coeff (location + 1) -
          2 * PowerSeries.X ^ (2 * index + 1) * (p index).coeff location -
          (1 - PowerSeries.X ^ (2 * index)) *
            (if index = 0 then 0 else (p (index - 1)).coeff location) := by
    have hclean : LaurentPolynomial.C (1 - PowerSeries.X ^ (2 * (index + 1))) *
        p (index + 1) = LaurentPolynomial.T 1 * p index +
          LaurentPolynomial.T (-1) * p index -
            LaurentPolynomial.C (2 * PowerSeries.X ^ (2 * index + 1)) * p index -
              LaurentPolynomial.C (1 - PowerSeries.X ^ (2 * index)) *
                (if index = 0 then 0 else p (index - 1)) := by
      simp only [map_sub, map_one, map_mul, map_ofNat]
      linear_combination hrecurrence index
    have h := congrArg (fun poly => poly.coeff location) hclean
    simp only [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_add,
      Finsupp.sub_apply, Finsupp.add_apply, hscalar, hshift, sub_neg_eq_add,
      mul_assoc] at h
    split_ifs at h ⊢ <;> simpa only [AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply, mul_zero, sub_zero, mul_assoc] using h
  have hsupport (index : ℕ) (location : ℤ) (hlarge : (index : ℤ) < |location|) :
      (p index).coeff location = 0 := by
    induction index using Nat.strong_induction_on generalizing location with
    | h index ih =>
        cases index with
        | zero =>
            rw [hzero]
            have hne : location ≠ 0 := by intro h; simp [h] at hlarge
            change (Finsupp.single (0 : ℤ) (1 : PowerSeries ℚ)) location = 0
            simp only [Finsupp.single_apply, if_neg (Ne.symm hne)]
        | succ index =>
            apply (mul_eq_zero.mp ?_).resolve_left (hnonzero index)
            rw [hcolumn]
            have hleft : (index : ℤ) < |location - 1| := by
              rcases le_total 0 location with hpos | hneg
              · rw [abs_of_nonneg hpos] at hlarge
                rw [abs_of_nonneg (by omega)]; omega
              · rw [abs_of_nonpos hneg] at hlarge
                rw [abs_of_nonpos (by omega)]; omega
            have hright : (index : ℤ) < |location + 1| := by
              rcases le_total 0 location with hpos | hneg
              · rw [abs_of_nonneg hpos] at hlarge
                rw [abs_of_nonneg (by omega)]; omega
              · rw [abs_of_nonpos hneg] at hlarge
                rw [abs_of_nonpos (by omega)]; omega
            rw [ih index (by omega) _ hleft, ih index (by omega) _ hright,
              ih index (by omega) location (by push_cast at hlarge; omega)]
            split_ifs
            · simp
            · rw [ih (index - 1) (by omega) location (by push_cast at hlarge; omega)]
              simp
  have hreflection (index : ℕ) : LaurentPolynomial.invert (p index) = p index := by
    induction index using Nat.strong_induction_on with
    | h index ih =>
        cases index with
        | zero => simp [hzero]
        | succ index =>
            apply AddMonoidAlgebra.ext
            apply Finsupp.ext
            intro location
            simp only [LaurentPolynomial.invert_apply]
            apply mul_left_cancel₀ (hnonzero index)
            rw [hcolumn, hcolumn]
            have hprev (earlier : ℕ) (hlt : earlier < index + 1) (place : ℤ) :
                (p earlier).coeff (-place) = (p earlier).coeff place := by
              simpa using congrArg (fun poly => poly.coeff place) (ih earlier hlt)
            rw [show -location - 1 = -(location + 1) by omega,
              show -location + 1 = -(location - 1) by omega,
              hprev index (by omega) (location + 1),
              hprev index (by omega) (location - 1),
              hprev index (by omega) location]
            split_ifs
            · ring
            · rw [hprev (index - 1) (by omega) location]
              ring
  have hleading (index : ℕ) :
      (∏ earlier ∈ Finset.range index,
          (1 - (PowerSeries.X : PowerSeries ℚ) ^ (2 * (earlier + 1)))) *
        (p index).coeff (index : ℤ) = 1 := by
    induction index with
    | zero => simp [hzero]
    | succ index ih =>
        have h := hcolumn index (index + 1)
        rw [show (index : ℤ) + 1 - 1 = index by omega,
          hsupport index (index + 1 + 1) (by rw [abs_of_nonneg (by omega)]; omega),
          hsupport index (index + 1) (by rw [abs_of_nonneg (by omega)]; omega)] at h
        have hprevious : (if index = 0 then 0 else (p (index - 1)).coeff (index + 1)) =
            0 := by
          split_ifs
          · rfl
          · exact hsupport _ _ (by rw [abs_of_nonneg (by omega)]; omega)
        rw [hprevious] at h
        simp only [add_zero, mul_zero, sub_zero] at h
        rw [Finset.prod_range_succ, mul_assoc, show ((index + 1 : ℕ) : ℤ) =
            (index : ℤ) + 1 by push_cast; rfl, h, ih]
  have htop (degree : ℕ) (weights : Fin (degree + 1) → PowerSeries ℚ) :
      (∑ index : Fin (degree + 1), LaurentPolynomial.C (weights index) *
        p index.val).coeff (degree : ℤ) =
          weights (Fin.last degree) * (p degree).coeff (degree : ℤ) := by
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, hscalar]
    apply Finset.sum_eq_single (Fin.last degree)
    · intro index _ hne
      rw [hsupport index.val degree (by
        rw [abs_of_nonneg (Int.natCast_nonneg degree)]
        have hlt := index.isLt
        have hval : index.val ≠ degree := by
          intro heq
          exact hne (Fin.ext heq)
        omega), mul_zero]
    · simp
  have hleadNonzero (degree : ℕ) : (p degree).coeff (degree : ℤ) ≠ 0 := by
    intro hzero
    have h := hleading degree
    rw [hzero, mul_zero] at h
    exact zero_ne_one h
  have hindependent (degree : ℕ) (weights : Fin (degree + 1) → PowerSeries ℚ)
      (hsum : (∑ index : Fin (degree + 1), LaurentPolynomial.C (weights index) *
        p index.val) = 0) : weights = 0 := by
    induction degree with
    | zero =>
        have h := htop 0 weights
        rw [hsum] at h
        have hlast : weights (Fin.last 0) = 0 := by
          exact (mul_eq_zero.mp h.symm).resolve_right (hleadNonzero 0)
        funext index
        have heq : index = Fin.last 0 := by
          apply Fin.ext
          have hlt := index.isLt
          simp only [Fin.val_last]
          omega
        simpa only [heq, Pi.zero_apply] using hlast
    | succ degree ih =>
        have h := congrArg (fun poly => poly.coeff ((degree + 1 : ℕ) : ℤ)) hsum
        rw [htop] at h
        have hlast : weights (Fin.last (degree + 1)) = 0 := by
          exact (mul_eq_zero.mp h).resolve_right (hleadNonzero (degree + 1))
        have hprevious : (∑ index : Fin (degree + 1),
            LaurentPolynomial.C (weights index.castSucc) * p index.val) = 0 := by
          rw [Fin.sum_univ_castSucc] at hsum
          simpa only [Fin.val_castSucc, hlast, map_zero, zero_mul, add_zero] using hsum
        have hold := ih (fun index => weights index.castSucc) hprevious
        funext index
        refine Fin.lastCases ?_ (fun earlier => ?_) index
        · exact hlast
        · exact congrFun hold earlier
  have hrepresent (degree : ℕ) (poly : LaurentPolynomial (PowerSeries ℚ))
      (hsymmetric : LaurentPolynomial.invert poly = poly)
      (hbounded : ∀ location : ℤ, (degree : ℤ) < |location| → poly.coeff location = 0) :
      ∃ weights : Fin (degree + 1) → PowerSeries ℚ,
        poly = ∑ index : Fin (degree + 1), LaurentPolynomial.C (weights index) *
          p index.val := by
    induction degree generalizing poly with
    | zero =>
        refine ⟨fun _ => poly.coeff 0, ?_⟩
        change poly = ∑ index : Fin 1, LaurentPolynomial.C (poly.coeff 0) * p index.val
        rw [Fin.sum_univ_one]
        change poly = LaurentPolynomial.C (poly.coeff 0) * p 0
        rw [hzero, mul_one]
        apply AddMonoidAlgebra.ext
        apply Finsupp.ext
        intro location
        by_cases hzero : location = 0
        · subst location
          change poly.coeff 0 = (Finsupp.single (0 : ℤ) (poly.coeff 0)) 0
          rw [Finsupp.single_eq_same]
        · rw [hbounded location (by
            exact abs_pos.mpr hzero)]
          change 0 = (Finsupp.single (0 : ℤ) (poly.coeff 0)) location
          simp only [Finsupp.single_apply, if_neg (Ne.symm hzero)]
    | succ degree ih =>
        let weight := poly.coeff ((degree + 1 : ℕ) : ℤ) *
          ∏ earlier ∈ Finset.range (degree + 1),
            (1 - (PowerSeries.X : PowerSeries ℚ) ^ (2 * (earlier + 1)))
        let remainder := poly - LaurentPolynomial.C weight * p (degree + 1)
        have hsym : LaurentPolynomial.invert remainder = remainder := by
          simp only [remainder, map_sub, map_mul, hsymmetric,
            LaurentPolynomial.invert_C, hreflection]
        have hhighest : remainder.coeff ((degree + 1 : ℕ) : ℤ) = 0 := by
          simp only [remainder, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
            hscalar, weight]
          rw [mul_assoc, hleading, mul_one, sub_self]
        have hnegative (location : ℤ) : remainder.coeff (-location) =
            remainder.coeff location := by
          simpa only [LaurentPolynomial.invert_apply] using
            congrArg (fun poly => poly.coeff location) hsym
        have hbound : ∀ location : ℤ, (degree : ℤ) < |location| →
            remainder.coeff location = 0 := by
          intro location hlarge
          by_cases hlarger : ((degree + 1 : ℕ) : ℤ) < |location|
          · simp only [remainder, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hscalar,
              hbounded location hlarger, hsupport (degree + 1) location hlarger,
              mul_zero, sub_zero]
          · have hexact : |location| = ((degree + 1 : ℕ) : ℤ) := by
              push_cast at hlarger ⊢
              omega
            rcases le_total 0 location with hpositive | hnonpositive
            · rw [abs_of_nonneg hpositive] at hexact
              rw [hexact]
              exact hhighest
            · rw [abs_of_nonpos hnonpositive] at hexact
              rw [show location = -((degree + 1 : ℕ) : ℤ) by omega, hnegative]
              exact hhighest
        obtain ⟨weights, hweights⟩ := ih remainder hsym hbound
        refine ⟨Fin.snoc weights weight, ?_⟩
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rw [← hweights]
        dsimp only [remainder]
        ring
  let baseEuler := euler
  have baseProduct := hdenominator
  have baseFunctional := hfunctional
  have heigen {K : Type fieldUniverse} [Field K]
    (embedding : PowerSeries ℚ →+* K) (hparameter : embedding PowerSeries.X ≠ 0)
    (index : ℕ) :
    let rho := embedding PowerSeries.X
    let q := Units.mk0 (rho ^ 2) (pow_ne_zero 2 hparameter)
    let transfer := AddMonoidAlgebra.mapRingHom ℤ embedding
    let poly := transfer (PowerSeries.coeff index polynomialGenerator)
    let indeterminate : LaurentPolynomial K := LaurentPolynomial.T 1
    differenceNumerator rho q poly =
      (1 - indeterminate ^ 2) *
        (1 - LaurentPolynomial.C (q : K) * indeterminate ^ 2) *
        (LaurentPolynomial.C (q : K) - indeterminate ^ 2) *
        (LaurentPolynomial.C ((q : K)⁻¹ ^ index - 1) * poly) := by
    classical
    let rho := embedding PowerSeries.X
    let q := Units.mk0 (rho ^ 2) (pow_ne_zero 2 hparameter)
    let scalar := LaurentPolynomial.C (R := K)
    let transfer := AddMonoidAlgebra.mapRingHom ℤ embedding
    let lift := scalar.comp (embedding.comp (PowerSeries.expand 2 (by decide)).toRingHom)
    let euler := PowerSeries.map lift (PowerSeries.mk eulerCoefficients)
    let parameter := scalar rho
    let step := scalar (q : K)
    let inverseStep := scalar ((q : K)⁻¹)
    let positive : LaurentPolynomial K := LaurentPolynomial.T 1
    let negative : LaurentPolynomial K := LaurentPolynomial.T (-1)
    let factor := fun value : LaurentPolynomial K =>
      1 - PowerSeries.C value * PowerSeries.X
    let numerator := PowerSeries.rescale parameter euler
    let positiveEuler := PowerSeries.rescale positive euler
    let negativeEuler := PowerSeries.rescale negative euler
    generalize hgenerator : PowerSeries.map transfer polynomialGenerator = generator
    have htransferC (value : PowerSeries ℚ) :
        transfer (LaurentPolynomial.C value) = scalar (embedding value) := by
      exact AddMonoidAlgebra.mapRingHom_single embedding 0 value
    have htransferT (location : ℤ) :
        transfer (LaurentPolynomial.T location) = LaurentPolynomial.T location := by
      simpa only [transfer, LaurentPolynomial.T, map_one] using
        AddMonoidAlgebra.mapRingHom_single embedding location 1
    have hlift : lift PowerSeries.X = step := by
      simp [lift, step, scalar, q, rho, PowerSeries.expand_X, map_pow]
    have heuler : PowerSeries.constantCoeff euler = 1 ∧
        euler = factor 1 * PowerSeries.rescale step euler := by
      obtain ⟨hconstant, hfunctional⟩ := euler_coefficient_construction.1
      constructor
      · change lift (PowerSeries.constantCoeff (PowerSeries.mk eulerCoefficients)) = 1
        rw [hconstant, map_one]
      · have h := congrArg (PowerSeries.map lift) hfunctional
        simpa only [map_mul, map_sub, map_one, PowerSeries.map_X,
          ← PowerSeries.rescale_map, hlift, euler, factor, map_one, one_mul] using h
    have hfactor (value : LaurentPolynomial K) :
        PowerSeries.rescale value euler =
          factor value * PowerSeries.rescale (step * value) euler := by
      have h := congrArg (PowerSeries.rescale value) heuler.2
      simpa only [map_mul, map_sub, map_one, PowerSeries.rescale_X,
        PowerSeries.rescale_rescale, factor, map_one, one_mul] using h
    have hconstant (value : LaurentPolynomial K) :
        PowerSeries.constantCoeff (PowerSeries.rescale value euler) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, heuler.1]
    have hproduct : positiveEuler * negativeEuler * generator = numerator ^ 2 := by
      have hmapEuler : PowerSeries.map transfer baseEuler = euler := by
        change PowerSeries.map transfer
          (PowerSeries.map (LaurentPolynomial.C.comp
            (PowerSeries.expand 2 (by decide)).toRingHom)
              (PowerSeries.mk eulerCoefficients)) =
          PowerSeries.map lift (PowerSeries.mk eulerCoefficients)
        apply PowerSeries.ext
        intro degree
        simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk,
          RingHom.comp_apply, lift, htransferC]
      have h := congrArg (PowerSeries.map transfer) baseProduct
      change PowerSeries.map transfer
        (PowerSeries.rescale (LaurentPolynomial.T 1) baseEuler *
          PowerSeries.rescale (LaurentPolynomial.T (-1)) baseEuler * polynomialGenerator) =
        PowerSeries.map transfer
          (PowerSeries.rescale (LaurentPolynomial.C (PowerSeries.X : PowerSeries ℚ))
            baseEuler ^ 2) at h
      simpa only [map_mul, map_pow, ← PowerSeries.rescale_map, htransferC, htransferT,
        hmapEuler, hgenerator] using h
    have hshiftEuler (scale : Kˣ) :
        PowerSeries.map (laurentShift scale) euler = euler := by
      apply PowerSeries.ext
      intro degree
      simp only [euler, PowerSeries.coeff_map, lift, RingHom.comp_apply,
        laurentShift, scalar, LaurentPolynomial.eval₂_C]
    have hshiftPositive (scale : Kˣ) :
        laurentShift scale positive = scalar (scale : K) * positive := by
      simp [laurentShift, positive, scalar, LaurentPolynomial.eval₂_T,
        unitOfInvertible, Units.val_mul]
    have hshiftNegative (scale : Kˣ) :
        laurentShift scale negative = scalar ((scale : K)⁻¹) * negative := by
      simp [laurentShift, negative, scalar, LaurentPolynomial.eval₂_T,
        unitOfInvertible, mul_inv_rev]
    have hshiftParameter (scale : Kˣ) : laurentShift scale parameter = parameter := by
      simp only [parameter, scalar, laurentShift, LaurentPolynomial.eval₂_C]
    have hstepInverse : step * inverseStep = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (Units.ne_zero q), map_one]
    have hsquare : parameter ^ 2 = step := by
      change scalar rho ^ 2 = scalar (rho ^ 2)
      exact (map_pow scalar rho 2).symm
    have hpositiveNegative : positive * negative = 1 := by
      change LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) = 1
      rw [← LaurentPolynomial.T_add]
      norm_num
    have hplus : factor (inverseStep * negative) *
        PowerSeries.map (laurentShift q) generator = factor positive * generator := by
      have hshiftProduct := congrArg (PowerSeries.map (laurentShift q)) hproduct
      simp only [map_mul, map_pow, ← PowerSeries.rescale_map, positiveEuler, negativeEuler,
        numerator,
        hshiftPositive, hshiftNegative, hshiftParameter, hshiftEuler] at hshiftProduct
      change PowerSeries.rescale (step * positive) euler *
        PowerSeries.rescale (inverseStep * negative) euler *
          PowerSeries.map (laurentShift q) generator = numerator ^ 2 at hshiftProduct
      have hback : PowerSeries.rescale (inverseStep * negative) euler =
          factor (inverseStep * negative) * negativeEuler := by
        simpa only [mul_assoc, ← mul_assoc step inverseStep, hstepInverse, one_mul,
          negativeEuler] using hfactor (inverseStep * negative)
      have hforward := hfactor positive
      apply mul_left_cancel₀
        (a := PowerSeries.rescale (step * positive) euler * negativeEuler)
        (by
          intro hzero
          have h := congrArg PowerSeries.constantCoeff hzero
          simp only [negativeEuler, map_mul, hconstant, map_zero, one_mul] at h
          exact one_ne_zero h)
      calc
        _ = numerator ^ 2 := by rw [← hshiftProduct, hback]; ring
        _ = _ := by rw [← hproduct]; dsimp only [positiveEuler]; rw [hforward]; ring
    have hminus : factor (inverseStep * positive) *
        PowerSeries.map (laurentShift q⁻¹) generator = factor negative * generator := by
      have hshiftProduct := congrArg (PowerSeries.map (laurentShift q⁻¹)) hproduct
      simp only [map_mul, map_pow, ← PowerSeries.rescale_map, positiveEuler, negativeEuler,
        numerator,
        hshiftPositive, hshiftNegative, hshiftParameter, hshiftEuler, Units.val_inv_eq_inv_val,
        inv_inv] at hshiftProduct
      change PowerSeries.rescale (inverseStep * positive) euler *
        PowerSeries.rescale (step * negative) euler *
          PowerSeries.map (laurentShift q⁻¹) generator = numerator ^ 2 at hshiftProduct
      have hback : PowerSeries.rescale (inverseStep * positive) euler =
          factor (inverseStep * positive) * positiveEuler := by
        simpa only [mul_assoc, ← mul_assoc step inverseStep, hstepInverse, one_mul,
          positiveEuler] using hfactor (inverseStep * positive)
      have hforward := hfactor negative
      apply mul_left_cancel₀
        (a := positiveEuler * PowerSeries.rescale (step * negative) euler)
        (by
          intro hzero
          have h := congrArg PowerSeries.constantCoeff hzero
          simp only [positiveEuler, map_mul, hconstant, map_zero, one_mul] at h
          exact one_ne_zero h)
      calc
        _ = numerator ^ 2 := by rw [← hshiftProduct, hback]; ring
        _ = _ := by rw [← hproduct]; dsimp only [negativeEuler]; rw [hforward]; ring
    have hinverseRescale :
        factor (inverseStep * positive) * factor (inverseStep * negative) *
            PowerSeries.rescale inverseStep generator =
          factor (inverseStep * parameter) ^ 2 * generator := by
      have h := congrArg (PowerSeries.map transfer) baseFunctional
      change PowerSeries.map transfer
        ((1 - PowerSeries.C (LaurentPolynomial.C (PowerSeries.X : PowerSeries ℚ)) *
            PowerSeries.X) ^ 2 *
          PowerSeries.rescale (LaurentPolynomial.C (PowerSeries.X : PowerSeries ℚ) ^ 2)
            polynomialGenerator) =
        PowerSeries.map transfer
          ((1 - PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X) *
            (1 - PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X) *
              polynomialGenerator) at h
      simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.map_C, PowerSeries.map_X,
        ← PowerSeries.rescale_map, htransferC, htransferT, map_pow, hgenerator] at h
      change factor parameter ^ 2 * PowerSeries.rescale (parameter ^ 2) generator =
        factor positive * factor negative * generator at h
      rw [hsquare] at h
      change factor parameter ^ 2 * PowerSeries.rescale step generator =
        factor positive * factor negative * generator at h
      have hrescaleC (scale value : LaurentPolynomial K) :
          PowerSeries.rescale scale (PowerSeries.C value) = PowerSeries.C value := by
        apply PowerSeries.ext
        intro degree
        simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
        split_ifs with hzero
        · subst degree; rw [pow_zero, one_mul]
        · rw [mul_zero]
      have hrescaleFactor (value : LaurentPolynomial K) :
          PowerSeries.rescale inverseStep (factor value) = factor (inverseStep * value) := by
        dsimp only [factor]
        rw [map_sub, map_one, map_mul, hrescaleC, PowerSeries.rescale_X, ← mul_assoc,
          ← map_mul PowerSeries.C, mul_comm value inverseStep]
      have hround : PowerSeries.rescale inverseStep (PowerSeries.rescale step generator) =
          generator := by
        rw [PowerSeries.rescale_rescale, hstepInverse, PowerSeries.rescale_one]
        rfl
      have hrescaled := congrArg (PowerSeries.rescale inverseStep) h
      rw [map_mul, map_pow, hrescaleFactor, hround, map_mul, map_mul,
        hrescaleFactor, hrescaleFactor] at hrescaled
      exact hrescaled.symm
    let forwardWeight := (1 - parameter * positive) ^ 2 * (step - positive ^ 2)
    let backwardWeight := (positive - parameter) ^ 2 * positive ^ 2 *
      (1 - step * positive ^ 2)
    let denominator := (1 - positive ^ 2) * (1 - step * positive ^ 2) *
      (step - positive ^ 2)
    have halgebra :
        PowerSeries.C forwardWeight * (factor positive - factor (inverseStep * negative)) *
            factor (inverseStep * positive) +
          PowerSeries.C backwardWeight * (factor negative - factor (inverseStep * positive)) *
            factor (inverseStep * negative) =
        PowerSeries.C denominator *
          (factor (inverseStep * parameter) ^ 2 -
            factor (inverseStep * positive) * factor (inverseStep * negative)) := by
      let spectral : PowerSeries (LaurentPolynomial K) := PowerSeries.C parameter
      let inverseDilation : PowerSeries (LaurentPolynomial K) := PowerSeries.C inverseStep
      let forward : PowerSeries (LaurentPolynomial K) := PowerSeries.C positive
      let backward : PowerSeries (LaurentPolynomial K) := PowerSeries.C negative
      let coordinate : PowerSeries (LaurentPolynomial K) := PowerSeries.X
      have hpair : forward * backward = 1 := by
        rw [← map_mul, hpositiveNegative, map_one]
      have hunit : spectral ^ 2 * inverseDilation = 1 := by
        rw [← map_pow, ← map_mul, hsquare, hstepInverse, map_one]
      dsimp only [forwardWeight, backwardWeight, denominator, factor]
      rw [← hsquare]
      simp only [map_mul, map_sub, map_pow, map_one]
      change (1 - spectral * forward) ^ 2 * (spectral ^ 2 - forward ^ 2) *
          ((1 - forward * coordinate) - (1 - inverseDilation * backward * coordinate)) *
          (1 - inverseDilation * forward * coordinate) +
        (forward - spectral) ^ 2 * forward ^ 2 * (1 - spectral ^ 2 * forward ^ 2) *
          ((1 - backward * coordinate) - (1 - inverseDilation * forward * coordinate)) *
          (1 - inverseDilation * backward * coordinate) =
        (1 - forward ^ 2) * (1 - spectral ^ 2 * forward ^ 2) *
          (spectral ^ 2 - forward ^ 2) *
          ((1 - inverseDilation * spectral * coordinate) ^ 2 -
            (1 - inverseDilation * forward * coordinate) *
              (1 - inverseDilation * backward * coordinate))
      linear_combination
        -coordinate * (forward - spectral) * (spectral * forward - 1) *
          (2 * spectral ^ 2 * inverseDilation ^ 2 * coordinate * forward ^ 3 -
            2 * spectral ^ 2 * inverseDilation ^ 2 * coordinate * forward -
            spectral ^ 2 * inverseDilation * coordinate * forward ^ 2 * backward -
            spectral ^ 2 * inverseDilation * coordinate * forward -
            spectral ^ 2 * inverseDilation * forward ^ 2 +
            2 * spectral ^ 2 * inverseDilation + spectral ^ 2 * forward ^ 2 +
            spectral * inverseDilation * coordinate * forward ^ 3 * backward +
            spectral * inverseDilation * coordinate * forward ^ 2 -
            spectral * inverseDilation * coordinate * forward * backward -
            spectral * inverseDilation * coordinate - spectral * inverseDilation * forward ^ 3 +
            spectral * inverseDilation * forward - spectral * forward ^ 3 + spectral * forward +
            inverseDilation * coordinate * forward ^ 2 * backward +
            inverseDilation * coordinate * forward - inverseDilation * forward ^ 2 -
            forward ^ 2) * hpair +
        coordinate * (forward - spectral) * (forward - 1) * (forward + 1) *
          (spectral * forward - 1) *
          (spectral ^ 2 * inverseDilation * coordinate * forward +
            spectral * inverseDilation * coordinate * forward ^ 2 +
            spectral * inverseDilation * coordinate - 2 * spectral * forward -
            inverseDilation * coordinate * forward) * hunit
    have hgenerating :
        PowerSeries.C denominator * (PowerSeries.rescale inverseStep generator - generator) =
          PowerSeries.C forwardWeight * (PowerSeries.map (laurentShift q) generator - generator) +
            PowerSeries.C backwardWeight *
              (PowerSeries.map (laurentShift q⁻¹) generator - generator) := by
      have hzero : factor (inverseStep * positive) * factor (inverseStep * negative) *
          (PowerSeries.C denominator *
            (PowerSeries.rescale inverseStep generator - generator) -
              (PowerSeries.C forwardWeight *
                  (PowerSeries.map (laurentShift q) generator - generator) +
                PowerSeries.C backwardWeight *
                  (PowerSeries.map (laurentShift q⁻¹) generator - generator))) = 0 := by
        linear_combination PowerSeries.C denominator * hinverseRescale -
          PowerSeries.C forwardWeight * factor (inverseStep * positive) * hplus -
          PowerSeries.C backwardWeight * factor (inverseStep * negative) * hminus -
          generator * halgebra
      have hnonzero : factor (inverseStep * positive) * factor (inverseStep * negative) ≠ 0 := by
        intro hzero
        have h := congrArg PowerSeries.constantCoeff hzero
        simp only [factor, map_mul, map_sub, map_one, PowerSeries.constantCoeff_C,
          PowerSeries.constantCoeff_X, mul_zero, sub_zero, one_mul, map_zero] at h
        exact one_ne_zero h
      exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hnonzero)
    have hcoefficient := congrArg (PowerSeries.coeff index) hgenerating
    simp only [PowerSeries.coeff_C_mul, map_sub, map_add, PowerSeries.coeff_rescale,
      PowerSeries.coeff_map] at hcoefficient
    change differenceNumerator rho q
        (transfer (PowerSeries.coeff index polynomialGenerator)) = _
    have hactual : transfer (PowerSeries.coeff index polynomialGenerator) =
        PowerSeries.coeff index generator := by
      simpa only [PowerSeries.coeff_map] using congrArg (PowerSeries.coeff index) hgenerator
    rw [hactual]
    change forwardWeight *
        (laurentShift q (PowerSeries.coeff index generator) - PowerSeries.coeff index generator) +
      backwardWeight *
        (laurentShift q⁻¹ (PowerSeries.coeff index generator) -
          PowerSeries.coeff index generator) =
      denominator * (scalar ((q : K)⁻¹ ^ index - 1) * PowerSeries.coeff index generator)
    rw [hcoefficient.symm]
    rw [map_sub, map_pow, map_one, sub_mul, one_mul]
  refine ⟨by simpa [p, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero,
    hrecurrence, hreflection, hsupport, hleading, ?_, @heigen⟩
  intro degree poly hsymmetric hbounded
  obtain ⟨weights, hweights⟩ := hrepresent degree poly hsymmetric hbounded
  refine ⟨weights, hweights, ?_⟩
  intro candidate hcandidate
  have hdifference : (∑ index : Fin (degree + 1),
      LaurentPolynomial.C (candidate index - weights index) * p index.val) = 0 := by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [← hcandidate, ← hweights, sub_self]
  have hzeroDifference := hindependent degree (fun index => candidate index - weights index)
    hdifference
  funext index
  exact sub_eq_zero.mp (congrFun hzeroDifference index)


end D5.S3.Combinatorics.InversionSeq.InversionSeq207Polynomials
