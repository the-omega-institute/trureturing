/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Pearson
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Pearson
   mirror-E: none(waiver:bounded-formal-pearson-shift)
   anchors: []
   utility: none
   digest: Stable truncations construct the weight, its Pearson product, and bounded shift. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Difference

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Pearson

open InversionSeq207Difference
open Finset.HasAntidiagonal

noncomputable def pearsonTruncation (cutoff : ℕ) : Polynomial (LaurentPolynomial ℚ) :=
  ∏ index ∈ Finset.range cutoff,
    (1 - Polynomial.monomial (2 * index + 4) (LaurentPolynomial.T 2)) *
      (1 - Polynomial.monomial (2 * index) (LaurentPolynomial.T (-2))) *
      (∑ count ∈ Finset.range cutoff,
        Polynomial.monomial ((2 * index + 3) * count)
          (LaurentPolynomial.T (count : ℤ))) ^ 2 *
      (∑ count ∈ Finset.range cutoff,
        Polynomial.monomial ((2 * index + 1) * count)
          (LaurentPolynomial.T (-(count : ℤ)))) ^ 2

noncomputable def pearsonProduct : PowerSeries (LaurentPolynomial ℚ) :=
  PowerSeries.mk fun degree => (pearsonTruncation (degree + 1)).coeff degree

noncomputable def weightTruncation (cutoff : ℕ) : Polynomial (LaurentPolynomial ℚ) :=
  ∏ index ∈ Finset.range cutoff,
    (1 - Polynomial.monomial (2 * index) (LaurentPolynomial.T 2)) *
      (1 - Polynomial.monomial (2 * index) (LaurentPolynomial.T (-2))) *
      (∑ count ∈ Finset.range cutoff,
        Polynomial.monomial ((2 * index + 1) * count)
          (LaurentPolynomial.T (count : ℤ))) ^ 2 *
      (∑ count ∈ Finset.range cutoff,
        Polynomial.monomial ((2 * index + 1) * count)
          (LaurentPolynomial.T (-(count : ℤ)))) ^ 2

noncomputable def formalWeight : PowerSeries (LaurentPolynomial ℚ) :=
  PowerSeries.mk fun degree => (weightTruncation (degree + 1)).coeff degree

set_option maxHeartbeats 2400000 in
theorem pearson_balance :
    (∀ degree cutoff : ℕ, degree < cutoff →
      PowerSeries.coeff degree pearsonProduct = (pearsonTruncation cutoff).coeff degree) ∧
    (∀ location : ℤ,
      (PowerSeries.mk (fun degree =>
        (PowerSeries.coeff degree pearsonProduct).coeff (-location)) : LaurentSeries ℚ) =
      HahnSeries.single (-(2 * location)) 1 *
        (PowerSeries.mk (fun degree =>
          (PowerSeries.coeff degree pearsonProduct).coeff location) : LaurentSeries ℚ)) ∧
    (∀ degree cutoff : ℕ, degree < cutoff →
      PowerSeries.coeff degree formalWeight = (weightTruncation cutoff).coeff degree) ∧
    formalWeight * (1 - PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 1)) ^ 2 =
      pearsonProduct * (1 - PowerSeries.C (LaurentPolynomial.T 2)) *
        (1 - PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 2)) ∧
    (∀ degree : ℕ, LaurentPolynomial.invert (PowerSeries.coeff degree formalWeight) =
      PowerSeries.coeff degree formalWeight) := by
  classical
  let monomial (degree : ℕ) (location : ℤ) : Polynomial (LaurentPolynomial ℚ) :=
    Polynomial.monomial degree (LaurentPolynomial.T location)
  let geometric (degree : ℕ) (location : ℤ) (cutoff : ℕ) :=
    ∑ count ∈ Finset.range cutoff, monomial (degree * count) (location * count)
  let factor (index cutoff : ℕ) :=
    (1 - monomial (2 * index + 4) 2) * (1 - monomial (2 * index) (-2)) *
      geometric (2 * index + 3) 1 cutoff ^ 2 *
      geometric (2 * index + 1) (-1) cutoff ^ 2
  have hfinite (cutoff : ℕ) :
      pearsonTruncation cutoff = ∏ index ∈ Finset.range cutoff, factor index cutoff := by
    simp [pearsonTruncation, factor, geometric, monomial]
  have hmulCongruence (degree : ℕ) (first second third fourth :
      Polynomial (LaurentPolynomial ℚ))
      (hfirst : ∀ earlier ≤ degree, first.coeff earlier = second.coeff earlier)
      (hsecond : ∀ earlier ≤ degree, third.coeff earlier = fourth.coeff earlier) :
      ∀ earlier ≤ degree, (first * third).coeff earlier = (second * fourth).coeff earlier := by
    intro earlier hsmall
    rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro pair hpair
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
    rw [hfirst pair.1 (by omega), hsecond pair.2 (by omega)]
  have hpowCongruence (degree : ℕ) (first second : Polynomial (LaurentPolynomial ℚ))
      (hfirst : ∀ earlier ≤ degree, first.coeff earlier = second.coeff earlier)
      (exponent : ℕ) :
      ∀ earlier ≤ degree,
        (first ^ exponent).coeff earlier = (second ^ exponent).coeff earlier := by
    induction exponent with
    | zero => simp
    | succ exponent ih =>
        simpa only [pow_succ] using hmulCongruence degree _ _ _ _ ih hfirst
  have hprodCongruence (degree : ℕ) (indices : Finset ℕ)
      (first second : ℕ → Polynomial (LaurentPolynomial ℚ))
      (hfirst : ∀ index ∈ indices, ∀ earlier ≤ degree,
        (first index).coeff earlier = (second index).coeff earlier) :
      ∀ earlier ≤ degree, (∏ index ∈ indices, first index).coeff earlier =
        (∏ index ∈ indices, second index).coeff earlier := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices houtside ih =>
        simp only [Finset.prod_insert houtside]
        apply hmulCongruence degree
        · exact hfirst index (Finset.mem_insert_self _ _)
        · exact ih (fun other hother => hfirst other (Finset.mem_insert_of_mem hother))
  have hgeometricStep (degree cutoff : ℕ) (location : ℤ) :
      geometric degree location (cutoff + 1) =
        geometric degree location cutoff + monomial (degree * cutoff) (location * cutoff) :=
    Finset.sum_range_succ _ cutoff
  have hgeometricCongruence (bound degree cutoff : ℕ) (location : ℤ)
      (hpositive : 0 < degree) (hlarge : bound < cutoff) :
      ∀ earlier ≤ bound, (geometric degree location (cutoff + 1)).coeff earlier =
        (geometric degree location cutoff).coeff earlier := by
    intro earlier hearlier
    rw [hgeometricStep, Polynomial.coeff_add]
    have hsmall : earlier < degree * cutoff := by
      have := Nat.mul_le_mul_right cutoff hpositive
      omega
    simp [monomial, Polynomial.coeff_monomial, ne_of_gt hsmall]
  have hfactorCongruence (bound cutoff index : ℕ) (hlarge : bound < cutoff) :
      ∀ earlier ≤ bound, (factor index (cutoff + 1)).coeff earlier =
        (factor index cutoff).coeff earlier := by
    apply hmulCongruence bound
    · apply hmulCongruence bound
      · intro earlier _
        rfl
      · exact hpowCongruence bound _ _
          (hgeometricCongruence bound (2 * index + 3) cutoff 1 (by omega) hlarge) 2
    · exact hpowCongruence bound _ _
        (hgeometricCongruence bound (2 * index + 1) cutoff (-1) (by omega) hlarge) 2
  have hnewGeometric (bound degree cutoff : ℕ) (location : ℤ)
      (hdegree : bound < degree) :
      ∀ earlier ≤ bound, (geometric degree location (cutoff + 1)).coeff earlier =
        (1 : Polynomial (LaurentPolynomial ℚ)).coeff earlier := by
    intro earlier hearlier
    unfold geometric
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
    · simp [monomial, Polynomial.coeff_monomial, Polynomial.coeff_one]
    · intro count _ hnonzero
      have hsmall : earlier < degree * count := by
        have := Nat.mul_le_mul_left degree (show 1 ≤ count by omega)
        omega
      simp [monomial, Polynomial.coeff_monomial, ne_of_gt hsmall]
    · simp
  have hnewFactor (bound cutoff : ℕ) (hlarge : bound < cutoff) :
      ∀ earlier ≤ bound, (factor cutoff (cutoff + 1)).coeff earlier =
        (1 : Polynomial (LaurentPolynomial ℚ)).coeff earlier := by
    have hfirst : ∀ earlier ≤ bound,
        ((1 - monomial (2 * cutoff + 4) 2) *
          (1 - monomial (2 * cutoff) (-2))).coeff earlier =
        (1 : Polynomial (LaurentPolynomial ℚ)).coeff earlier := by
      have hmono (power : ℕ) (location : ℤ) (hpower : bound < power) :
          ∀ earlier ≤ bound, (1 - monomial power location).coeff earlier =
            (1 : Polynomial (LaurentPolynomial ℚ)).coeff earlier := by
        intro earlier hearlier
        simp [monomial, Polynomial.coeff_monomial, ne_of_gt (by omega : earlier < power)]
      simpa only [one_mul] using hmulCongruence bound _ 1 _ 1
        (hmono _ _ (by omega)) (hmono _ _ (by omega))
    dsimp only [factor]
    have hsecond := hpowCongruence bound _ 1
      (hnewGeometric bound (2 * cutoff + 3) cutoff 1 (by omega)) 2
    have hthird := hpowCongruence bound _ 1
      (hnewGeometric bound (2 * cutoff + 1) cutoff (-1) (by omega)) 2
    simpa only [one_pow, one_mul] using hmulCongruence bound _ 1 _ 1
      (by simpa only [one_pow, one_mul] using
        hmulCongruence bound _ 1 _ 1 hfirst (by simpa using hsecond))
      (by simpa using hthird)
  have hstableStep (degree cutoff : ℕ) (hlarge : degree < cutoff) :
      (pearsonTruncation (cutoff + 1)).coeff degree =
        (pearsonTruncation cutoff).coeff degree := by
    rw [hfinite, Finset.prod_range_succ, hfinite]
    have hprod := hprodCongruence degree (Finset.range cutoff)
      (fun index => factor index (cutoff + 1)) (fun index => factor index cutoff)
      (fun index _ => hfactorCongruence degree cutoff index hlarge)
    simpa only [mul_one] using
      hmulCongruence degree _ _ _ 1 hprod (hnewFactor degree cutoff hlarge) degree le_rfl
  have hstable (degree cutoff : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree pearsonProduct = (pearsonTruncation cutoff).coeff degree := by
    have hpadding (extra : ℕ) :
        (pearsonTruncation (degree + 1 + extra)).coeff degree =
          (pearsonTruncation (degree + 1)).coeff degree := by
      induction extra with
      | zero => simp
      | succ extra ih =>
          rw [show degree + 1 + (extra + 1) = (degree + 1 + extra) + 1 by omega,
            hstableStep degree (degree + 1 + extra) (by omega), ih]
    simp only [pearsonProduct, PowerSeries.coeff_mk]
    rw [show cutoff = degree + 1 + (cutoff - (degree + 1)) by omega]
    exact (hpadding _).symm
  let weightFactor (index cutoff : ℕ) :=
    (1 - monomial (2 * index) 2) * (1 - monomial (2 * index) (-2)) *
      geometric (2 * index + 1) 1 cutoff ^ 2 *
      geometric (2 * index + 1) (-1) cutoff ^ 2
  have hweightFinite (cutoff : ℕ) :
      weightTruncation cutoff = ∏ index ∈ Finset.range cutoff, weightFactor index cutoff := by
    simp [weightTruncation, weightFactor, geometric, monomial]
  have hmonoCongruence (bound power : ℕ) (location : ℤ) (hpower : bound < power) :
      ∀ earlier ≤ bound, (1 - monomial power location).coeff earlier =
        (1 : Polynomial (LaurentPolynomial ℚ)).coeff earlier := by
    intro earlier hearlier
    simp [monomial, Polynomial.coeff_monomial, ne_of_gt (by omega : earlier < power)]
  have hweightStep (degree cutoff : ℕ) (hlarge : degree < cutoff) :
      (weightTruncation (cutoff + 1)).coeff degree =
        (weightTruncation cutoff).coeff degree := by
    rw [hweightFinite, Finset.prod_range_succ, hweightFinite]
    have hprod := hprodCongruence degree (Finset.range cutoff)
      (fun index => weightFactor index (cutoff + 1)) (fun index => weightFactor index cutoff)
      (fun index _ => hmulCongruence degree _ _ _ _
        (hmulCongruence degree _ _ _ _ (fun _ _ => rfl)
          (hpowCongruence degree _ _
            (hgeometricCongruence degree (2 * index + 1) cutoff 1 (by omega) hlarge) 2))
        (hpowCongruence degree _ _
          (hgeometricCongruence degree (2 * index + 1) cutoff (-1) (by omega) hlarge) 2))
    have hnew := hmulCongruence degree _ 1 _ 1
      (by simpa only [one_mul] using (hmulCongruence degree _ 1 _ 1
        (by simpa only [one_mul] using (hmulCongruence degree _ 1 _ 1
          (hmonoCongruence degree (2 * cutoff) 2 (by omega))
          (hmonoCongruence degree (2 * cutoff) (-2) (by omega))))
        (by simpa only [one_pow] using (hpowCongruence degree _ 1
          (hnewGeometric degree (2 * cutoff + 1) cutoff 1 (by omega)) 2))))
      (by simpa only [one_pow] using (hpowCongruence degree _ 1
        (hnewGeometric degree (2 * cutoff + 1) cutoff (-1) (by omega)) 2))
    simpa only [weightFactor, one_mul, one_pow, mul_one] using
      hmulCongruence degree _ _ _ 1 hprod (by simpa using hnew) degree le_rfl
  have hweightStable (degree cutoff : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree formalWeight = (weightTruncation cutoff).coeff degree := by
    have hpadding (extra : ℕ) :
        (weightTruncation (degree + 1 + extra)).coeff degree =
          (weightTruncation (degree + 1)).coeff degree := by
      induction extra with
      | zero => simp
      | succ extra ih =>
          rw [show degree + 1 + (extra + 1) = (degree + 1 + extra) + 1 by omega,
            hweightStep degree (degree + 1 + extra) (by omega), ih]
    simp only [formalWeight, PowerSeries.coeff_mk]
    rw [show cutoff = degree + 1 + (cutoff - (degree + 1)) by omega]
    exact (hpadding _).symm
  have hweightRelation :
      formalWeight * (1 - PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 1)) ^ 2 =
        pearsonProduct * (1 - PowerSeries.C (LaurentPolynomial.T 2)) *
          (1 - PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 2)) := by
    let numerator (length offset : ℕ) :=
      ∏ index ∈ Finset.range length, (1 - monomial (2 * index + offset) 2)
    let positive (length offset cutoff : ℕ) :=
      ∏ index ∈ Finset.range length, geometric (2 * index + offset) 1 cutoff
    let negative (cutoff : ℕ) :=
      (∏ index ∈ Finset.range cutoff, (1 - monomial (2 * index) (-2))) *
        (∏ index ∈ Finset.range cutoff, geometric (2 * index + 1) (-1) cutoff) ^ 2
    have hweight (cutoff : ℕ) : weightTruncation cutoff =
        numerator cutoff 0 * positive cutoff 1 cutoff ^ 2 * negative cutoff := by
      simp only [weightTruncation, numerator, positive, negative, monomial, geometric,
        Nat.add_zero, Int.one_mul, Finset.prod_mul_distrib, Finset.prod_pow]
      ring
    have hpearson (cutoff : ℕ) : pearsonTruncation cutoff =
        numerator cutoff 4 * positive cutoff 3 cutoff ^ 2 * negative cutoff := by
      simp only [pearsonTruncation, numerator, positive, negative, monomial, geometric,
        Int.one_mul, Finset.prod_mul_distrib, Finset.prod_pow]
      ring
    have hnumerator (bound cutoff : ℕ) (hlarge : bound < cutoff) :
        ∀ earlier ≤ bound, (numerator cutoff 0).coeff earlier =
          ((1 - monomial 0 2) * (1 - monomial 2 2) *
            numerator cutoff 4).coeff earlier := by
      have htail : numerator (cutoff + 2) 0 = numerator cutoff 0 *
          (1 - monomial (2 * cutoff) 2) * (1 - monomial (2 * cutoff + 2) 2) := by
        simp only [numerator, show cutoff + 2 = cutoff + 1 + 1 by omega,
          Finset.prod_range_succ, Nat.add_zero]
        congr 2
      have hfront : numerator (cutoff + 2) 0 =
          (1 - monomial 0 2) * (1 - monomial 2 2) * numerator cutoff 4 := by
        rw [show cutoff + 2 = 2 + cutoff by omega]
        simp only [numerator, Finset.prod_range_add, Finset.prod_range_succ,
          Finset.prod_range_zero, mul_one, Nat.add_zero]
        have hindices : ∀ index : ℕ, 2 * (2 + index) = 2 * index + 4 := by omega
        simp only [hindices, Nat.mul_zero, one_mul]
      have hcongr := hmulCongruence bound _ (numerator cutoff 0) _ 1
        (by simpa only [mul_one] using (hmulCongruence bound
          (numerator cutoff 0) (numerator cutoff 0) _ 1 (fun _ _ => rfl)
          (hmonoCongruence bound (2 * cutoff) 2 (by omega))))
        (hmonoCongruence bound (2 * cutoff + 2) 2 (by omega))
      intro earlier hearlier
      rw [← hfront, htail]
      simpa only [mul_one] using (hcongr earlier hearlier).symm
    have hgeometricCancel (cutoff : ℕ) :
        geometric 1 1 cutoff * (1 - monomial 1 1) = 1 - monomial cutoff (cutoff : ℤ) := by
      induction cutoff with
      | zero => simp [geometric, monomial]
      | succ cutoff ih =>
          rw [hgeometricStep, add_mul, ih]
          have hmul : monomial cutoff (cutoff : ℤ) * monomial 1 1 =
              monomial (cutoff + 1) ((cutoff + 1 : ℕ) : ℤ) := by
            simp only [monomial, Polynomial.monomial_mul_monomial, ← LaurentPolynomial.T_add,
              Nat.cast_add, Nat.cast_one]
          simp only [Nat.one_mul, Int.one_mul, mul_sub, mul_one, hmul]
          ring
    have hpositive (bound cutoff : ℕ) (hlarge : bound < cutoff) :
        ∀ earlier ≤ bound,
          (positive cutoff 1 cutoff * (1 - monomial 1 1)).coeff earlier =
            (positive cutoff 3 cutoff).coeff earlier := by
      have hfront : positive (cutoff + 1) 1 cutoff =
          geometric 1 1 cutoff * positive cutoff 3 cutoff := by
        simp only [positive, Finset.prod_range_succ', Nat.mul_zero, zero_add]
        have hindices : ∀ index : ℕ, 2 * (index + 1) + 1 = 2 * index + 3 := by omega
        simp only [hindices]
        rw [mul_comm]
      have htail : positive (cutoff + 1) 1 cutoff =
          positive cutoff 1 cutoff * geometric (2 * cutoff + 1) 1 cutoff := by
        exact Finset.prod_range_succ _ cutoff
      have hnew : ∀ earlier ≤ bound,
          (geometric (2 * cutoff + 1) 1 cutoff).coeff earlier =
            (1 : Polynomial (LaurentPolynomial ℚ)).coeff earlier := by
        have hcutoff : cutoff = (cutoff - 1) + 1 := by omega
        rw [hcutoff]
        exact hnewGeometric bound (2 * ((cutoff - 1) + 1) + 1) (cutoff - 1) 1 (by omega)
      have hfirst := hmulCongruence bound _ (positive cutoff 1 cutoff * 1)
        (1 - monomial 1 1) (1 - monomial 1 1)
        (hmulCongruence bound (positive cutoff 1 cutoff) (positive cutoff 1 cutoff)
          _ 1 (fun _ _ => rfl) hnew) (fun _ _ => rfl)
      have hlast := hmulCongruence bound _ 1
        (positive cutoff 3 cutoff) (positive cutoff 3 cutoff)
        (hmonoCongruence bound cutoff (cutoff : ℤ) hlarge) (fun _ _ => rfl)
      intro earlier hearlier
      calc
        _ = (positive (cutoff + 1) 1 cutoff * (1 - monomial 1 1)).coeff earlier := by
          rw [htail]
          simpa only [mul_one] using (hfirst earlier hearlier).symm
        _ = ((1 - monomial cutoff (cutoff : ℤ)) *
            positive cutoff 3 cutoff).coeff earlier := by
          rw [hfront, mul_right_comm, hgeometricCancel]
        _ = _ := by simpa only [one_mul] using hlast earlier hearlier
    apply PowerSeries.ext
    intro degree
    let cutoff := degree + 1
    have hlarge : degree < cutoff := by dsimp [cutoff]; omega
    have hpolynomial :
        (weightTruncation cutoff * (1 - monomial 1 1) ^ 2).coeff degree =
          (pearsonTruncation cutoff * (1 - monomial 0 2) *
            (1 - monomial 2 2)).coeff degree := by
      rw [hweight, hpearson]
      have hleft : numerator cutoff 0 * positive cutoff 1 cutoff ^ 2 * negative cutoff *
          (1 - monomial 1 1) ^ 2 =
          numerator cutoff 0 * (positive cutoff 1 cutoff * (1 - monomial 1 1)) ^ 2 *
            negative cutoff := by ring
      rw [hleft]
      have hcongr := hmulCongruence degree _ _ (negative cutoff) (negative cutoff)
        (hmulCongruence degree _ _ _ _ (hnumerator degree cutoff hlarge)
          (hpowCongruence degree _ _ (hpositive degree cutoff hlarge) 2))
        (fun _ _ => rfl)
      convert hcongr degree le_rfl using 1 <;> ring
    have hseriesMul (bound : ℕ) (first : PowerSeries (LaurentPolynomial ℚ))
        (second third : Polynomial (LaurentPolynomial ℚ))
        (hfirst : ∀ earlier ≤ bound, PowerSeries.coeff earlier first = second.coeff earlier) :
        PowerSeries.coeff bound (first * (third : PowerSeries (LaurentPolynomial ℚ))) =
          (second * third).coeff bound := by
      rw [PowerSeries.coeff_mul, Polynomial.coeff_mul]
      apply Finset.sum_congr rfl
      intro pair hpair
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
      rw [hfirst pair.1 (by omega), Polynomial.coeff_coe]
    have hmonomial (power : ℕ) (location : ℤ) :
        (monomial power location : PowerSeries (LaurentPolynomial ℚ)) =
          PowerSeries.X ^ power * PowerSeries.C (LaurentPolynomial.T location) := by
      simp [monomial, Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow, mul_comm]
    have hleft := hseriesMul degree formalWeight (weightTruncation cutoff)
      ((1 - monomial 1 1) ^ 2) (fun earlier hearlier =>
        hweightStable earlier cutoff (by omega))
    have hright := hseriesMul degree pearsonProduct (pearsonTruncation cutoff)
      ((1 - monomial 0 2) * (1 - monomial 2 2)) (fun earlier hearlier =>
        hstable earlier cutoff (by omega))
    have hright' := hright
    rw [← mul_assoc] at hright'
    simpa only [Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_mul, hmonomial, pow_one, pow_zero, one_mul, mul_assoc] using
      hleft.trans (hpolynomial.trans hright'.symm)
  have hweightSymmetric (degree : ℕ) :
      LaurentPolynomial.invert (PowerSeries.coeff degree formalWeight) =
        PowerSeries.coeff degree formalWeight := by
    have hinvert (poly : LaurentPolynomial ℚ) :
        LaurentPolynomial.invert.toRingHom poly = LaurentPolynomial.invert poly := rfl
    have hgeometricInvert (power cutoff : ℕ) (location : ℤ) :
        (geometric power location cutoff).map LaurentPolynomial.invert.toRingHom =
          geometric power (-location) cutoff := by
      simp only [geometric, Polynomial.map_sum, monomial, Polynomial.map_monomial,
        hinvert, LaurentPolynomial.invert_T, neg_mul]
    have hfiniteInvert (cutoff : ℕ) :
        (weightTruncation cutoff).map LaurentPolynomial.invert.toRingHom =
          weightTruncation cutoff := by
      rw [hweightFinite, Polynomial.map_prod]
      apply Finset.prod_congr rfl
      intro index _
      simp only [weightFactor, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
        Polynomial.map_pow]
      rw [hgeometricInvert, hgeometricInvert]
      simp only [monomial, Polynomial.map_monomial, hinvert, LaurentPolynomial.invert_T,
        neg_neg]
      ring
    rw [hweightStable degree (degree + 1) (by omega)]
    simpa only [Polynomial.coeff_map, hinvert] using
      congrArg (fun poly : Polynomial (LaurentPolynomial ℚ) => poly.coeff degree)
        (hfiniteInvert (degree + 1))
  refine ⟨hstable, ?_, hweightStable, hweightRelation, hweightSymmetric⟩
  let rho : LaurentSeries ℚ := (PowerSeries.X : PowerSeries ℚ)
  let rational : ℚ →+* LaurentSeries ℚ := algebraMap ℚ (LaurentSeries ℚ)
  let transfer : LaurentPolynomial ℚ →+* LaurentPolynomial (LaurentSeries ℚ) :=
    AddMonoidAlgebra.mapRingHom ℤ rational
  let lift : Polynomial (LaurentPolynomial ℚ) →+* LaurentPolynomial (LaurentSeries ℚ) :=
    Polynomial.eval₂RingHom transfer (LaurentPolynomial.C rho)
  have hrational (value : ℚ) : rational value = HahnSeries.single 0 value := by
    have hequal : rational = HahnSeries.C := Subsingleton.elim _ _
    exact congrArg (fun hom : ℚ →+* LaurentSeries ℚ => hom value) hequal
  have hrho : rho ≠ 0 := by
    intro hzero
    have h := congrArg (fun series : LaurentSeries ℚ => series.coeff 1) hzero
    simp [rho] at h
  let scale := (Units.mk0 (rho ^ 2) (pow_ne_zero 2 hrho))⁻¹
  have hscale (location : ℤ) : (scale : LaurentSeries ℚ) ^ location =
      rho ^ (-(2 * location)) := by
    simp only [scale, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [inv_zpow, ← zpow_natCast, ← zpow_mul, ← zpow_neg]
    rfl
  have htransferC (value : ℚ) :
      transfer (LaurentPolynomial.C value) = LaurentPolynomial.C (rational value) :=
    AddMonoidAlgebra.mapRingHom_single rational 0 value
  have htransferT (location : ℤ) :
      transfer (LaurentPolynomial.T location) = LaurentPolynomial.T location := by
    simpa only [transfer, LaurentPolynomial.T, map_one] using
      AddMonoidAlgebra.mapRingHom_single rational location 1
  have hliftMonomial (degree : ℕ) (location : ℤ) :
      lift (monomial degree location) =
        LaurentPolynomial.C (rho ^ degree) * LaurentPolynomial.T location := by
    simp only [lift, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, monomial,
      htransferT, ← map_pow]
    ring
  have hshiftT (location : ℤ) :
      laurentShift scale (LaurentPolynomial.T location) =
        LaurentPolynomial.C ((scale : LaurentSeries ℚ) ^ location) *
          LaurentPolynomial.T location := by
    have hunit (exponent : ℤ) :
        ((unitOfInvertible (LaurentPolynomial.T 1) ^ exponent :
          (LaurentPolynomial (LaurentSeries ℚ))ˣ) : LaurentPolynomial (LaurentSeries ℚ)) =
            LaurentPolynomial.T exponent := by
      cases exponent with
      | ofNat index => simp [zpow_natCast, unitOfInvertible, LaurentPolynomial.T_pow]
      | negSucc index =>
          simp [zpow_negSucc, unitOfInvertible, LaurentPolynomial.T_pow]
          congr 1
          omega
    simp only [laurentShift, LaurentPolynomial.eval₂_T, mul_zpow, Units.val_mul]
    rw [← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val, hunit]
    rfl
  have hshiftC (value : LaurentSeries ℚ) :
      laurentShift scale (LaurentPolynomial.C value) = LaurentPolynomial.C value := by
    simp [laurentShift]
  have hshiftMonomial (degree target : ℕ) (location : ℤ)
      (hexponent : (degree : ℤ) - 2 * location = target) :
      laurentShift scale (lift (monomial degree location)) =
        LaurentPolynomial.invert (lift (monomial target (-location))) := by
    rw [hliftMonomial, map_mul, hshiftC, hshiftT, hscale, ← mul_assoc, ← map_mul]
    have hpowers : rho ^ degree * rho ^ (-(2 * location)) = rho ^ target := by
      rw [← zpow_natCast, ← zpow_add₀ hrho]
      rw [show (degree : ℤ) + -(2 * location) = target by omega, zpow_natCast]
    rw [hpowers, hliftMonomial]
    simp
  have hshiftPositive (index cutoff : ℕ) :
      laurentShift scale (lift (geometric (2 * index + 3) 1 cutoff)) =
        LaurentPolynomial.invert (lift (geometric (2 * index + 1) (-1) cutoff)) := by
    simp only [geometric, map_sum]
    apply Finset.sum_congr rfl
    intro count _
    simpa only [one_mul, neg_one_mul, neg_neg] using
      hshiftMonomial ((2 * index + 3) * count) ((2 * index + 1) * count)
        (count : ℤ) (by push_cast; ring)
  have hshiftNegative (index cutoff : ℕ) :
      laurentShift scale (lift (geometric (2 * index + 1) (-1) cutoff)) =
        LaurentPolynomial.invert (lift (geometric (2 * index + 3) 1 cutoff)) := by
    simp only [geometric, map_sum]
    apply Finset.sum_congr rfl
    intro count _
    simpa only [one_mul, neg_one_mul, neg_neg] using
      hshiftMonomial ((2 * index + 1) * count) ((2 * index + 3) * count)
        (-(count : ℤ)) (by push_cast; ring)
  have hshiftFactor (index cutoff : ℕ) :
      laurentShift scale (lift (factor index cutoff)) =
        LaurentPolynomial.invert (lift (factor index cutoff)) := by
    dsimp only [factor]
    simp only [map_mul, map_pow, map_sub, map_one]
    rw [hshiftPositive, hshiftNegative,
      hshiftMonomial (2 * index + 4) (2 * index) 2 (by push_cast; ring),
      hshiftMonomial (2 * index) (2 * index + 4) (-2) (by push_cast; ring)]
    ring
  have hfiniteShift (cutoff : ℕ) :
      laurentShift scale (lift (pearsonTruncation cutoff)) =
        LaurentPolynomial.invert (lift (pearsonTruncation cutoff)) := by
    rw [hfinite]
    simp only [map_prod]
    exact Finset.prod_congr rfl (fun index _ => hshiftFactor index cutoff)
  have hshiftCoeff (poly : LaurentPolynomial (LaurentSeries ℚ)) (location : ℤ) :
      (laurentShift scale poly).coeff location =
        (scale : LaurentSeries ℚ) ^ location * poly.coeff location := by
    induction poly using LaurentPolynomial.induction_on' with
    | add first second hfirst hsecond =>
        simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hfirst, hsecond]
        ring
    | C_mul_T exponent value =>
        rw [map_mul, hshiftC, hshiftT, ← mul_assoc, ← map_mul]
        rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T]
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
        split_ifs with hequal
        · subst location
          ring
        · simp
  have hfiniteColumns (cutoff : ℕ) (location : ℤ) :
      (lift (pearsonTruncation cutoff)).coeff (-location) =
        rho ^ (-(2 * location)) * (lift (pearsonTruncation cutoff)).coeff location := by
    rw [← LaurentPolynomial.invert_apply, ← hfiniteShift, hshiftCoeff, hscale]
  have hrhoPow (degree : ℕ) : rho ^ degree = HahnSeries.single (degree : ℤ) 1 := by
    simp [rho, PowerSeries.coe_X, HahnSeries.single_pow]
  have hliftCoeff (poly : Polynomial (LaurentPolynomial ℚ)) (location degree : ℤ) :
      ((lift poly).coeff location).coeff degree =
        if degree < 0 then 0 else (poly.coeff degree.toNat).coeff location := by
    induction poly using Polynomial.induction_on' with
    | add first second hfirst hsecond =>
        simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
          HahnSeries.coeff_add, Polynomial.coeff_add, hfirst, hsecond]
        split_ifs <;> simp
    | monomial power value =>
        induction value using LaurentPolynomial.induction_on' with
        | add first second hfirst hsecond =>
            simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
              HahnSeries.coeff_add, Polynomial.coeff_add, hfirst, hsecond]
            split_ifs <;> simp
        | C_mul_T exponent value =>
            simp only [lift, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, map_mul,
              htransferC, htransferT, ← map_pow, hrhoPow]
            rw [show LaurentPolynomial.C (rational value) * LaurentPolynomial.T exponent *
                LaurentPolynomial.C (HahnSeries.single (power : ℤ) 1) =
              LaurentPolynomial.C (rational value * HahnSeries.single (power : ℤ) 1) *
                LaurentPolynomial.T exponent by rw [map_mul]; ring]
            rw [← LaurentPolynomial.single_eq_C_mul_T]
            rw [hrational, HahnSeries.single_mul_single]
            simp only [zero_add, mul_one, AddMonoidAlgebra.coeff_single,
              Finsupp.single_apply, Polynomial.coeff_monomial]
            rw [← LaurentPolynomial.single_eq_C_mul_T]
            by_cases hnegative : degree < 0
            · have hne : degree ≠ (power : ℤ) := by omega
              split_ifs <;> simp [hnegative, hne, HahnSeries.coeff_single]
            · by_cases hpower : power = degree.toNat
              · have hequal : degree = (power : ℤ) := by omega
                have hnonnegative : ¬ (power : ℤ) < 0 := by omega
                by_cases hlocation : exponent = location <;>
                  simp [hequal, hnonnegative, hlocation, HahnSeries.coeff_single,
                    ← LaurentPolynomial.single_eq_C_mul_T,
                    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
              · have hne : degree ≠ (power : ℤ) := by omega
                by_cases hlocation : exponent = location <;>
                  simp [hnegative, hpower, hne, hlocation, HahnSeries.coeff_single]
  intro location
  apply HahnSeries.ext
  funext degree
  have hfiniteAt (cutoff : ℕ) :
      ((lift (pearsonTruncation cutoff)).coeff (-location)).coeff degree =
        ((lift (pearsonTruncation cutoff)).coeff location).coeff (degree + 2 * location) := by
    rw [hfiniteColumns]
    have hrhoZpow : rho ^ (-(2 * location)) = HahnSeries.single (-(2 * location)) 1 := by
      cases hindex : -(2 * location) with
      | ofNat index => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hrhoPow index
      | negSucc index =>
          rw [zpow_negSucc, hrhoPow, HahnSeries.inv_single]
          simp only [inv_one]
          congr 1
    rw [hrhoZpow, HahnSeries.coeff_single_mul, one_mul]
    congr 1
    omega
  have hcolumn (index : ℤ) (position : ℤ) (cutoff : ℕ)
      (hlarge : index.toNat < cutoff) :
      ((lift (pearsonTruncation cutoff)).coeff position).coeff index =
        (PowerSeries.mk (fun earlier =>
          (PowerSeries.coeff earlier pearsonProduct).coeff position) : LaurentSeries ℚ).coeff
          index := by
    rw [hliftCoeff, PowerSeries.coeff_coe]
    split_ifs with hnegative
    · rfl
    · rw [show index.natAbs = index.toNat by omega, PowerSeries.coeff_mk,
        hstable _ cutoff hlarge]
  let cutoff := degree.toNat + (degree + 2 * location).toNat + 1
  rw [HahnSeries.coeff_single_mul, one_mul,
    show degree - -(2 * location) = degree + 2 * location by omega]
  rw [← hcolumn degree (-location) cutoff (by dsimp [cutoff]; omega),
    ← hcolumn (degree + 2 * location) location cutoff (by dsimp [cutoff]; omega)]
  exact hfiniteAt cutoff

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Pearson
