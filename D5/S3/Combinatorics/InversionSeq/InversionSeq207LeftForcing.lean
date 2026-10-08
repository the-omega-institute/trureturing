/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207LeftForcing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207LeftForcing
   mirror-E: none(waiver:formal-left-forcing-reflection)
   anchors: [mathlib/module/Mathlib.RingTheory.LaurentSeries]
   utility: none
   digest: Finite Laurent support constructs the unique normalized additive Lambert primitive. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftRational
import Mathlib.RingTheory.LaurentSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftForcing

open InversionSeq207LeftMoment
open Finset.HasAntidiagonal

set_option maxHeartbeats 6400000 in
theorem left_lambert_primitive :
    ∃! primitive : PowerSeries (LaurentPolynomial ℚ),
      PowerSeries.map (LaurentPolynomial.invert (R := ℚ)).toRingHom primitive = primitive ∧
      PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1) primitive = 0 ∧
      ∀ index : ℤ,
        (HahnSeries.single index (1 : ℚ) - 1) *
          ((PowerSeries.mk (fun degree =>
            (PowerSeries.coeff degree primitive).coeff index) : PowerSeries ℚ) :
              LaurentSeries ℚ) =
          ((PowerSeries.mk (fun degree =>
            (PowerSeries.coeff degree leftRationalNumerator).coeff index) : PowerSeries ℚ) :
              LaurentSeries ℚ) := by
  classical
  let q : PowerSeries ℚ := PowerSeries.X
  let denominator : LaurentPolynomial (PowerSeries ℚ) :=
    1 + LaurentPolynomial.C q * (LaurentPolynomial.T (-1) - 2) +
      LaurentPolynomial.C (q ^ 2) * (LaurentPolynomial.T 1 - 2) +
        LaurentPolynomial.C (q ^ 3)
  let numerator : LaurentPolynomial (PowerSeries ℚ) :=
    (LaurentPolynomial.C q - 1) ^ 3 * (LaurentPolynomial.C q + 1) ^ 3 *
      (LaurentPolynomial.T 1 - 1) ^ 2 *
      (LaurentPolynomial.C q * LaurentPolynomial.T 1 - 1) ^ 2 *
      (LaurentPolynomial.C q * LaurentPolynomial.T 2 - 1) * LaurentPolynomial.T (-3)
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
  have hexpandConstant (value : PowerSeries ℚ) :
      expand (LaurentPolynomial.C value) = PowerSeries.map LaurentPolynomial.C value := by
    simpa using hexpandMonomial value 0
  have hexpandT (exponent : ℤ) :
      expand (LaurentPolynomial.T exponent) =
        PowerSeries.C (LaurentPolynomial.T exponent) := by
    simpa using hexpandMonomial 1 exponent
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
  have hpromoteConstant (value : PowerSeries ℚ) :
      promote (LaurentPolynomial.C value) =
        LaurentPolynomial.C (value : LaurentSeries ℚ) := by
    simpa using hpromoteMonomial value 0
  have hpromoteT (exponent : ℤ) :
      promote (LaurentPolynomial.T exponent) = LaurentPolynomial.T exponent := by
    simpa using hpromoteMonomial 1 exponent
  have hpromoteCoeff (polynomial : LaurentPolynomial (PowerSeries ℚ)) (exponent : ℤ) :
      (promote polynomial).coeff exponent = (polynomial.coeff exponent : LaurentSeries ℚ) :=
    by
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
      (LaurentPolynomial.C (HahnSeries.single (-exponent) 1) *
        LaurentPolynomial.T (-exponent)) = _
    rw [← mul_assoc, ← map_mul]
  have hreflectConstant (value : LaurentSeries ℚ) :
      reflect (LaurentPolynomial.C value) = LaurentPolynomial.C value := by
    simpa only [LaurentPolynomial.T_zero, mul_one, neg_zero, ← HahnSeries.C_apply,
      map_one] using hreflectMonomial value 0
  have hreflectT (exponent : ℤ) :
      reflect (LaurentPolynomial.T exponent) =
        LaurentPolynomial.C (HahnSeries.single (-exponent) 1) *
          LaurentPolynomial.T (-exponent) := by
    simpa using hreflectMonomial 1 exponent
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
  have hdenominatorReflection : reflect (promote denominator) = promote denominator := by
    simp only [denominator, map_add, map_mul, map_sub, map_one, map_ofNat,
      hpromoteConstant, hpromoteT, hreflectConstant, hreflectT,
      PowerSeries.coe_pow, q, PowerSeries.coe_X]
    ring_nf
    simp only [← map_pow, ← map_mul, HahnSeries.single_pow,
      HahnSeries.single_mul_single, one_pow, one_mul]
    norm_num
    ring
  have hnumeratorReflection : reflect (promote numerator) = -promote numerator := by
    let core : LaurentPolynomial (PowerSeries ℚ) :=
      (LaurentPolynomial.T 1 - 1) ^ 2 *
        (LaurentPolynomial.C q * LaurentPolynomial.T 1 - 1) ^ 2 *
        (LaurentPolynomial.C q * LaurentPolynomial.T 2 - 1) * LaurentPolynomial.T (-3)
    have hfactor : numerator =
        LaurentPolynomial.C ((q - 1) ^ 3 * (q + 1) ^ 3) * core := by
      simp only [numerator, core, map_mul, map_pow, map_sub, map_add, map_one, mul_assoc]
    have hcore : reflect (promote core) = -promote core := by
      simp only [core, map_mul, map_pow, map_sub, map_one,
        hpromoteConstant, hpromoteT, hreflectConstant, hreflectT, q, PowerSeries.coe_X]
      simp only [← LaurentPolynomial.single_eq_C, LaurentPolynomial.T,
        pow_succ, pow_zero, mul_sub, sub_mul, one_mul, mul_one,
        AddMonoidAlgebra.single_mul_single, HahnSeries.single_mul_single]
      norm_num
      ring
    rw [hfactor, map_mul, map_mul, hpromoteConstant, hreflectConstant, hcore]
    exact mul_neg
      (LaurentPolynomial.C ((HahnSeries.ofPowerSeries ℤ ℚ) ((q - 1) ^ 3 * (q + 1) ^ 3)))
      (promote core)
  let delta := 1 - denominator
  let approximant (bound : ℕ) := numerator * ∑ earlier ∈ Finset.range bound, delta ^ earlier
  have hpartialReflection (bound : ℕ) :
      reflect (promote (approximant bound)) = -promote (approximant bound) := by
    simp only [approximant, map_mul, map_sum, map_pow, delta, map_sub, map_one,
      hdenominatorReflection, hnumeratorReflection]
    exact neg_mul (promote numerator)
      (∑ earlier ∈ Finset.range bound, (1 - promote denominator) ^ earlier)
  have hdenominatorExpand : expand denominator =
      1 + PowerSeries.X * PowerSeries.C (LaurentPolynomial.T (-1) - 2) +
        PowerSeries.X ^ 2 * PowerSeries.C (LaurentPolynomial.T 1 - 2) +
          PowerSeries.X ^ 3 := by
    simp only [denominator, map_add, map_mul, map_sub, map_one, map_ofNat,
      hexpandConstant, hexpandT, q, PowerSeries.map_X, map_pow]
  have hnumeratorExpand : expand numerator =
      (PowerSeries.X - 1) ^ 3 * (PowerSeries.X + 1) ^ 3 *
        PowerSeries.C ((LaurentPolynomial.T 1 - 1) ^ 2) *
        (PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 1) - 1) ^ 2 *
        (PowerSeries.X * PowerSeries.C (LaurentPolynomial.T 2) - 1) *
          PowerSeries.C (LaurentPolynomial.T (-3)) := by
    simp only [numerator, map_mul, map_pow, map_sub, map_add, map_one,
      hexpandConstant, hexpandT, q, PowerSeries.map_X]
  have hproduct : expand denominator * leftRationalNumerator = expand numerator := by
    rw [hdenominatorExpand, hnumeratorExpand]
    exact left_rational_regularity.1
  have hdeltaDiv : PowerSeries.X ∣ expand delta := by
    rw [PowerSeries.X_dvd_iff]
    simp [delta, hdenominatorExpand]
  have hstabilization (degree bound : ℕ) (hbound : degree < bound) :
      PowerSeries.coeff degree (expand (approximant bound)) =
        PowerSeries.coeff degree leftRationalNumerator := by
    have hgeometric : (∑ earlier ∈ Finset.range bound, delta ^ earlier) * denominator =
        1 - delta ^ bound := by
      simpa [delta] using geom_sum_mul_neg delta bound
    have hequality : expand (approximant bound) =
        leftRationalNumerator * (1 - expand delta ^ bound) := by
      change expand (numerator * _) = _
      rw [map_mul, ← hproduct]
      calc
        expand denominator * leftRationalNumerator *
            expand (∑ earlier ∈ Finset.range bound, delta ^ earlier) =
          leftRationalNumerator *
            expand ((∑ earlier ∈ Finset.range bound, delta ^ earlier) * denominator) := by
              rw [map_mul]
              ring
        _ = _ := by rw [hgeometric, map_sub, map_one, map_pow]
    have hdiv : PowerSeries.X ^ bound ∣ leftRationalNumerator * expand delta ^ bound :=
      dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdeltaDiv bound) _
    rw [hequality, mul_sub, mul_one, map_sub,
      (PowerSeries.X_pow_dvd_iff.mp hdiv) degree hbound, sub_zero]
  have hreflection (index : ℤ) :
      ((PowerSeries.mk (fun degree =>
        (PowerSeries.coeff degree leftRationalNumerator).coeff index) : PowerSeries ℚ) :
          LaurentSeries ℚ) =
        -HahnSeries.single index (1 : ℚ) *
          ((PowerSeries.mk (fun degree =>
            (PowerSeries.coeff degree leftRationalNumerator).coeff (-index)) :
              PowerSeries ℚ) : LaurentSeries ℚ) := by
    apply HahnSeries.ext
    funext degree
    rw [neg_mul, HahnSeries.coeff_neg, HahnSeries.coeff_single_mul, one_mul]
    simp only [PowerSeries.coeff_coe, PowerSeries.coeff_mk]
    let bound := degree.natAbs + (degree - index).natAbs + 1
    have hfinite := congrArg (fun polynomial : LaurentPolynomial (LaurentSeries ℚ) =>
        (polynomial.coeff index).coeff degree) (hpartialReflection bound)
    rw [hreflectCoeff, hpromoteCoeff,
      AddMonoidAlgebra.coeff_neg, Finsupp.coe_neg, Pi.neg_apply, hpromoteCoeff,
      HahnSeries.coeff_single_mul, one_mul, HahnSeries.coeff_neg] at hfinite
    simp only [PowerSeries.coeff_coe] at hfinite
    have hstable (location : ℤ) (earlier : ℕ) (hsmall : earlier < bound) :
        PowerSeries.coeff earlier ((approximant bound).coeff location) =
          (PowerSeries.coeff earlier leftRationalNumerator).coeff location := by
      rw [← hexpandCoeff]
      rw [hstabilization earlier bound hsmall]
    split_ifs at hfinite ⊢ <;>
      (try simp only [hstable index degree.natAbs (by dsimp [bound]; omega),
        hstable (-index) (degree - index).natAbs (by dsimp [bound]; omega)] at hfinite ⊢) <;>
      linarith

  let column (series : PowerSeries (LaurentPolynomial ℚ)) (index : ℤ) : PowerSeries ℚ :=
    PowerSeries.mk fun degree => (PowerSeries.coeff degree series).coeff index
  have hreflectColumn (index : ℤ) :
      (column leftRationalNumerator index : LaurentSeries ℚ) =
        -HahnSeries.single index 1 * (column leftRationalNumerator (-index) :
          LaurentSeries ℚ) := hreflection index
  have hforcingSmall (degree index : ℕ) (hsmall : degree < index) :
      PowerSeries.coeff degree (column leftRationalNumerator index) = 0 := by
    have hequality := congrArg (fun series : LaurentSeries ℚ => series.coeff (degree : ℤ))
      (hreflectColumn index)
    rw [neg_mul, HahnSeries.coeff_neg, HahnSeries.coeff_single_mul, one_mul] at hequality
    simpa only [PowerSeries.coeff_coe, Int.natAbs_natCast,
      if_neg (show ¬(degree : ℤ) < 0 by omega),
      if_pos (show (degree : ℤ) - index < 0 by omega), neg_zero] using hequality
  have hforcingSlope (degree index : ℕ) (hlarge : (degree : ℤ) + 3 < 2 * index) :
      PowerSeries.coeff degree (column leftRationalNumerator index) = 0 := by
    by_cases hsmall : degree < index
    · exact hforcingSmall degree index hsmall
    have hlow : index ≤ degree := by omega
    have hzero : PowerSeries.coeff (degree - index)
        (column leftRationalNumerator (-(index : ℤ))) = 0 := by
      simpa only [column, PowerSeries.coeff_mk] using
        left_rational_regularity.2.1 (degree - index) (-(index : ℤ)) (by
          rw [abs_neg, abs_of_nonneg (by omega)]
          omega)
    have hequality := congrArg (fun series : LaurentSeries ℚ => series.coeff (degree : ℤ))
      (hreflectColumn index)
    rw [neg_mul, HahnSeries.coeff_neg, HahnSeries.coeff_single_mul, one_mul] at hequality
    simpa only [PowerSeries.coeff_coe, Int.natAbs_natCast,
      ← Int.natCast_sub hlow, if_neg (show ¬(degree : ℤ) < 0 by omega),
      if_neg (show ¬((degree - index : ℕ) : ℤ) < 0 by omega), hzero, neg_zero] using
        hequality
  let positive (index : ℕ) : PowerSeries ℚ :=
    if index = 0 then 0 else
      -(column leftRationalNumerator index *
        PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1)
  have hpositiveSupport (degree index : ℕ)
      (hlarge : degree < index ∨ (degree : ℤ) + 3 < 2 * index) :
      PowerSeries.coeff degree (positive index) = 0 := by
    by_cases hzero : index = 0
    · simp [positive, hzero]
    simp only [positive, if_neg hzero, map_neg, PowerSeries.coeff_mul]
    rw [neg_eq_zero]
    apply Finset.sum_eq_zero
    intro pair hpair
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
    have hvanish : PowerSeries.coeff pair.1 (column leftRationalNumerator index) = 0 := by
      rcases hlarge with hsmall | hslope
      · exact hforcingSmall pair.1 index (by omega)
      · exact hforcingSlope pair.1 index (by omega)
    rw [hvanish, zero_mul]
  let primitive : PowerSeries (LaurentPolynomial ℚ) := PowerSeries.mk fun degree =>
    ∑ index ∈ Finset.range (degree + 4),
      LaurentPolynomial.C (PowerSeries.coeff degree (positive index)) *
        (LaurentPolynomial.T (index : ℤ) + LaurentPolynomial.T (-(index : ℤ)) - 2)
  have hsymmetry : PowerSeries.map LaurentPolynomial.invert.toRingHom primitive =
      primitive := by
    apply PowerSeries.ext
    intro degree
    simp only [primitive, PowerSeries.coeff_map, PowerSeries.coeff_mk, map_sum,
      map_mul, map_sub, map_add, map_ofNat]
    apply Finset.sum_congr rfl
    intro index _
    change LaurentPolynomial.invert
        (LaurentPolynomial.C (PowerSeries.coeff degree (positive index))) *
      (LaurentPolynomial.invert (LaurentPolynomial.T (index : ℤ)) +
        LaurentPolynomial.invert (LaurentPolynomial.T (-(index : ℤ))) - 2) = _
    simp only [LaurentPolynomial.invert_C, LaurentPolynomial.invert_T, neg_neg]
    rw [add_comm]
  have hnormalized :
      PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1) primitive = 0 := by
    ext degree
    have hevalTwo : LaurentPolynomial.eval₂ (RingHom.id ℚ) 1
        (2 : LaurentPolynomial ℚ) = 2 := by
      rw [show (2 : LaurentPolynomial ℚ) = 1 + 1 by norm_num, map_add, map_one]
      norm_num
    simp [primitive, LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_C, hevalTwo]
    norm_num
  have hterm (degree earlier : ℕ) (location : ℤ) :
      (LaurentPolynomial.C (PowerSeries.coeff degree (positive earlier)) *
        (LaurentPolynomial.T (earlier : ℤ) +
          LaurentPolynomial.T (-(earlier : ℤ)) - 2)).coeff location =
        (if (earlier : ℤ) = location then PowerSeries.coeff degree (positive earlier) else 0) +
        (if -(earlier : ℤ) = location then PowerSeries.coeff degree (positive earlier)
          else 0) -
        (if location = 0 then 2 * PowerSeries.coeff degree (positive earlier) else 0) := by
    rw [mul_sub, mul_add]
    simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_sub,
      AddMonoidAlgebra.coeff_add, Finsupp.coe_sub, Finsupp.coe_add,
      Pi.sub_apply, Pi.add_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    have hscalar : (LaurentPolynomial.C (PowerSeries.coeff degree (positive earlier)) * 2) =
        LaurentPolynomial.C (2 * PowerSeries.coeff degree (positive earlier)) := by
      rw [map_mul, map_ofNat]
      ring
    rw [hscalar]
    simp only [LaurentPolynomial.C_apply]
  have hpositiveColumn (index : ℕ) (hindex : index ≠ 0) : column primitive index =
      positive index := by
    ext degree
    simp only [column, primitive, PowerSeries.coeff_mk, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
    have htermPositive (earlier : ℕ) :
        (LaurentPolynomial.C (PowerSeries.coeff degree (positive earlier)) *
          (LaurentPolynomial.T (earlier : ℤ) +
            LaurentPolynomial.T (-(earlier : ℤ)) - 2)).coeff (index : ℤ) =
          if earlier = index then PowerSeries.coeff degree (positive earlier) else 0 := by
      rw [hterm]
      simp only [Int.natCast_inj, if_neg (show -(earlier : ℤ) ≠ index by omega),
        if_neg (show (index : ℤ) ≠ 0 by omega), add_zero, sub_zero]
    simp only [htermPositive]
    rw [Finset.sum_eq_single index]
    · simp
    · intro earlier _ hne
      exact if_neg hne
    · intro houtside
      have hlarge : degree + 4 ≤ index := by simpa using houtside
      simpa using hpositiveSupport degree index (Or.inr (by omega))
  have hcolumnSymmetry (index : ℤ) : column primitive (-index) = column primitive index :=
    by
    ext degree
    have hequality := congrArg (fun series : PowerSeries (LaurentPolynomial ℚ) =>
      (PowerSeries.coeff degree series).coeff index) hsymmetry
    simp only [PowerSeries.coeff_map] at hequality
    change (LaurentPolynomial.invert (PowerSeries.coeff degree primitive)).coeff index =
      (PowerSeries.coeff degree primitive).coeff index at hequality
    simpa only [column, PowerSeries.coeff_mk, LaurentPolynomial.invert_apply] using hequality
  have hpositiveEquation (index : ℕ) (hindex : index ≠ 0) :
      (PowerSeries.X ^ index - 1) * positive index = column leftRationalNumerator index :=
    by
    have hunit : (1 - PowerSeries.X ^ index) *
        PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) (1 : ℚˣ) = 1 := by
      apply PowerSeries.mul_invOfUnit
      simp [hindex]
    simp only [positive, if_neg hindex]
    calc
      (PowerSeries.X ^ index - 1) *
          -(column leftRationalNumerator index *
            PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1) =
        column leftRationalNumerator index *
          ((1 - PowerSeries.X ^ index) *
            PowerSeries.invOfUnit (1 - PowerSeries.X ^ index) 1) := by ring
      _ = _ := by rw [hunit, mul_one]
  have hequation (index : ℤ) :
      (HahnSeries.single index (1 : ℚ) - 1) * (column primitive index : LaurentSeries ℚ) =
        (column leftRationalNumerator index : LaurentSeries ℚ) := by
    rcases lt_trichotomy index 0 with hnegative | hzero | hpositive
    · have hpos : index.natAbs ≠ 0 := by omega
      have hcast : (index.natAbs : ℤ) = -index := by
        rw [Int.natCast_natAbs, abs_of_neg hnegative]
      have hprevious := congrArg (HahnSeries.ofPowerSeries ℤ ℚ)
        (hpositiveEquation index.natAbs hpos)
      rw [PowerSeries.coe_mul, PowerSeries.coe_sub, PowerSeries.coe_pow,
        PowerSeries.coe_X, PowerSeries.coe_one, HahnSeries.single_pow] at hprevious
      simp only [one_pow, nsmul_eq_mul, mul_one] at hprevious
      rw [← hpositiveColumn index.natAbs hpos, hcast, hcolumnSymmetry] at hprevious
      have hreflection := hreflectColumn index
      rw [← hprevious] at hreflection
      rw [hreflection]
      have hinverse : HahnSeries.single index (1 : ℚ) * HahnSeries.single (-index) 1 = 1 :=
        by simp [HahnSeries.single_mul_single, ← HahnSeries.C_apply]
      calc
        (HahnSeries.single index 1 - 1) * (column primitive index : LaurentSeries ℚ) =
          -(HahnSeries.single index 1 * HahnSeries.single (-index) 1 -
            HahnSeries.single index 1) * (column primitive index : LaurentSeries ℚ) := by
              rw [hinverse]
              ring
        _ = _ := by ring
    · subst index
      have hequality := hreflectColumn 0
      simp only [neg_zero, ← HahnSeries.C_apply, map_one, neg_one_mul] at hequality
      have hvanish : (column leftRationalNumerator 0 : LaurentSeries ℚ) = 0 := by
        have htwice : (2 : LaurentSeries ℚ) * (column leftRationalNumerator 0 :
            LaurentSeries ℚ) = 0 := by linear_combination hequality
        have hnotTwo : (2 : LaurentSeries ℚ) ≠ 0 := by
          have hcast : HahnSeries.C (2 : ℚ) = (2 : LaurentSeries ℚ) := by
            rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]
            ring
          rw [← hcast]
          exact HahnSeries.C_ne_zero (by norm_num)
        exact (mul_eq_zero.mp htwice).resolve_left hnotTwo
      simp only [← HahnSeries.C_apply, map_one, sub_self, zero_mul, hvanish]
    · have hcast : (index.toNat : ℤ) = index := Int.toNat_of_nonneg (by omega)
      have hpos : index.toNat ≠ 0 := by omega
      have hprevious := congrArg (HahnSeries.ofPowerSeries ℤ ℚ)
        (hpositiveEquation index.toNat hpos)
      rw [PowerSeries.coe_mul, PowerSeries.coe_sub, PowerSeries.coe_pow,
        PowerSeries.coe_X, PowerSeries.coe_one, HahnSeries.single_pow] at hprevious
      simp only [one_pow, nsmul_eq_mul, mul_one] at hprevious
      rw [← hpositiveColumn index.toNat hpos, hcast] at hprevious
      exact hprevious
  refine ⟨primitive, ⟨hsymmetry, hnormalized, hequation⟩, ?_⟩
  intro candidate hcandidate
  have hnonzeroColumn (index : ℤ) (hne : index ≠ 0) : column candidate index =
      column primitive index := by
    have hmultiplier : HahnSeries.single index (1 : ℚ) - 1 ≠ 0 := by
      intro hzero
      have hbad := congrArg (fun series : LaurentSeries ℚ => series.coeff index) hzero
      simp [hne] at hbad
    have hequality := (hcandidate.2.2 index).trans (hequation index).symm
    exact HahnSeries.ofPowerSeries_injective
      (mul_left_cancel₀ hmultiplier hequality)
  ext degree location
  by_cases hzero : location = 0
  · subst location
    let difference := PowerSeries.coeff degree candidate - PowerSeries.coeff degree primitive
    have hconstant : difference = LaurentPolynomial.C (difference.coeff 0) := by
      ext index
      by_cases hzero : index = 0
      · subst index
        simp
      · have hequality := congrArg (PowerSeries.coeff degree) (hnonzeroColumn index hzero)
        simp only [column, PowerSeries.coeff_mk] at hequality
        simp [difference, hequality, hzero]
    have hequality := congrArg (PowerSeries.coeff degree)
      (congrArg (fun series => series -
        PowerSeries.map (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1) primitive)
        hcandidate.2.1)
    rw [hnormalized] at hequality
    simp only [sub_zero, map_zero] at hequality
    have heval : LaurentPolynomial.eval₂ (RingHom.id ℚ) 1 difference = 0 := by
      simp only [difference, map_sub, ← PowerSeries.coeff_map, hequality, hnormalized,
        map_zero, sub_zero]
    rw [hconstant, LaurentPolynomial.eval₂_C] at heval
    change (PowerSeries.coeff degree candidate).coeff 0 -
      (PowerSeries.coeff degree primitive).coeff 0 = 0 at heval
    exact sub_eq_zero.mp heval
  · simpa only [column, PowerSeries.coeff_mk] using
      congrArg (PowerSeries.coeff degree) (hnonzeroColumn location hzero)

end D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftForcing
