/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Difference
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Difference
   mirror-E: none(waiver:formal-pearson-pole-cancellation)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Div]
   utility: none
   digest: Finite symmetric exponent pairs construct the pole-free formal difference action. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Polynomials
import Mathlib.Algebra.Polynomial.Div

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Difference

noncomputable def laurentShift {K : Type*} [Field K] (scale : Kˣ) :
    LaurentPolynomial K →+* LaurentPolynomial K :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C
    (Units.map LaurentPolynomial.C.toMonoidHom scale * unitOfInvertible (LaurentPolynomial.T 1))

noncomputable def differenceNumerator {K : Type*} [Field K] (rho : K) (q : Kˣ)
    (poly : LaurentPolynomial K) : LaurentPolynomial K :=
  let indeterminate : LaurentPolynomial K := LaurentPolynomial.T 1
  let scalar := LaurentPolynomial.C
  (1 - scalar rho * indeterminate) ^ 2 * (scalar (q : K) - indeterminate ^ 2) *
      (laurentShift q poly - poly) +
    (indeterminate - scalar rho) ^ 2 * indeterminate ^ 2 *
      (1 - scalar (q : K) * indeterminate ^ 2) * (laurentShift q⁻¹ poly - poly)

set_option maxHeartbeats 1200000 in
theorem symmetric_difference_construction {K : Type*} [Field K] [CharZero K]
    (rho : K) (q : Kˣ) (degree : ℕ) (poly : LaurentPolynomial K)
    (hsymmetric : LaurentPolynomial.invert poly = poly)
    (hbounded : ∀ location : ℤ, (degree : ℤ) < |location| → poly.coeff location = 0) :
    let indeterminate : LaurentPolynomial K := LaurentPolynomial.T 1
    let denominator := (1 - indeterminate ^ 2) *
      (1 - LaurentPolynomial.C (q : K) * indeterminate ^ 2) *
      (LaurentPolynomial.C (q : K) - indeterminate ^ 2)
    ∃! output : LaurentPolynomial K,
      denominator * output = differenceNumerator rho q poly ∧
      LaurentPolynomial.invert output = output := by
  classical
  let indeterminate : LaurentPolynomial K := LaurentPolynomial.T 1
  let scalar := LaurentPolynomial.C (R := K)
  let denominator := (1 - indeterminate ^ 2) * (1 - scalar (q : K) * indeterminate ^ 2) *
    (scalar (q : K) - indeterminate ^ 2)
  let first := (1 - scalar rho * indeterminate) ^ 2 * (scalar (q : K) - indeterminate ^ 2)
  let second := (indeterminate - scalar rho) ^ 2 * indeterminate ^ 2 *
    (1 - scalar (q : K) * indeterminate ^ 2)
  have hshift (scale : Kˣ) (location : ℤ) :
      laurentShift scale (LaurentPolynomial.T location) =
        scalar ((scale : K) ^ location) * LaurentPolynomial.T location := by
    have hunit (exponent : ℤ) :
        ((unitOfInvertible (LaurentPolynomial.T 1) ^ exponent :
          (LaurentPolynomial K)ˣ) : LaurentPolynomial K) =
            LaurentPolynomial.T exponent := by
      cases exponent with
      | ofNat index =>
          simp [zpow_natCast, unitOfInvertible, LaurentPolynomial.T_pow]
      | negSucc index =>
          simp [zpow_negSucc, unitOfInvertible, LaurentPolynomial.T_pow]
          congr 1
          omega
    simp only [laurentShift, LaurentPolynomial.eval₂_T, mul_zpow, Units.val_mul]
    rw [← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val, hunit]
    rfl
  have hshiftC (scale : Kˣ) (value : K) : laurentShift scale (scalar value) =
      scalar value := by simp [laurentShift, scalar]
  have hscalarAdd (left right : LaurentPolynomial K) :
      differenceNumerator rho q (left + right) =
        differenceNumerator rho q left + differenceNumerator rho q right := by
    simp only [differenceNumerator, map_add]
    ring
  have hscalarMul (value : K) (input : LaurentPolynomial K) :
      differenceNumerator rho q (scalar value * input) =
        scalar value * differenceNumerator rho q input := by
    simp only [differenceNumerator, map_mul, hshiftC]
    ring
  have hconstant (value : K) : differenceNumerator rho q (scalar value) = 0 := by
    simp only [differenceNumerator, hshiftC, sub_self, mul_zero, add_zero]
  have hpair (index : ℕ) :
      ∃ output : LaurentPolynomial K, denominator * output =
        differenceNumerator rho q
          (LaurentPolynomial.T (index : ℤ) + LaurentPolynomial.T (-(index : ℤ))) := by
    let forward : Polynomial K := ∑ earlier ∈ Finset.range index,
      Polynomial.C ((q : K) ^ earlier) * Polynomial.X ^ (2 * earlier)
    let reverse : Polynomial K := ∑ earlier ∈ Finset.range index,
      Polynomial.C ((q : K) ^ earlier) * Polynomial.X ^ (2 * (index - 1 - earlier))
    let numerator : Polynomial K :=
      Polynomial.X ^ 2 * (Polynomial.X - Polynomial.C rho) ^ 2 * reverse -
        (1 - Polynomial.C rho * Polynomial.X) ^ 2 * forward
    have heval (value : K) (hsquare : value ^ 2 = 1) : numerator.eval value = 0 := by
      have hpowers (earlier : ℕ) : value ^ (2 * earlier) = 1 := by
        rw [pow_mul, hsquare, one_pow]
      have hforward : forward.eval value = ∑ earlier ∈ Finset.range index,
          (q : K) ^ earlier := by
        simp only [forward, Polynomial.eval_finsetSum, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, hpowers, mul_one]
      have hreverse : reverse.eval value = ∑ earlier ∈ Finset.range index,
          (q : K) ^ earlier := by
        simp only [reverse, Polynomial.eval_finsetSum, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, hpowers, mul_one]
      simp only [numerator, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_one, hforward, hreverse, hsquare]
      calc
        _ = (value ^ 2 - 1) * (1 - rho ^ 2) *
            (∑ earlier ∈ Finset.range index, (q : K) ^ earlier) := by ring
        _ = 0 := by rw [hsquare]; ring
    obtain ⟨quotient, hquotient⟩ :=
      Polynomial.dvd_iff_isRoot.mpr (heval 1 (by simp))
    have hsecondRoot : quotient.eval (-1) = 0 := by
      have h := congrArg (Polynomial.eval (-1)) hquotient
      rw [heval (-1) (by simp)] at h
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
    obtain ⟨outputPolynomial, houtputPolynomial⟩ :=
      Polynomial.dvd_iff_isRoot.mpr hsecondRoot
    have hdivision : numerator = (1 - Polynomial.X ^ 2) * (-outputPolynomial) := by
      rw [hquotient, houtputPolynomial]
      simp only [Polynomial.C_1, map_neg]
      ring
    let forwardLaurent := forward.toLaurent
    let reverseLaurent := reverse.toLaurent
    have hforward (bound : ℕ) :
        (1 - scalar (q : K) * indeterminate ^ 2) *
          (∑ earlier ∈ Finset.range bound,
            scalar ((q : K) ^ earlier) * indeterminate ^ (2 * earlier)) =
            1 - scalar ((q : K) ^ bound) * indeterminate ^ (2 * bound) := by
      induction bound with
      | zero => simp
      | succ bound ih =>
          rw [Finset.sum_range_succ, mul_add, ih]
          simp only [pow_succ, show 2 * (bound + 1) = 2 * bound + 2 by omega,
            map_mul]
          ring
    have hreverse (bound : ℕ) :
        (scalar (q : K) - indeterminate ^ 2) *
          (∑ earlier ∈ Finset.range bound,
            scalar ((q : K) ^ earlier) * indeterminate ^ (2 * (bound - 1 - earlier))) =
            scalar ((q : K) ^ bound) - indeterminate ^ (2 * bound) := by
      induction bound with
      | zero => simp [scalar]
      | succ bound ih =>
          have hsum : (∑ earlier ∈ Finset.range (bound + 1),
              scalar ((q : K) ^ earlier) * indeterminate ^ (2 * (bound - earlier))) =
              indeterminate ^ 2 *
                (∑ earlier ∈ Finset.range bound,
                  scalar ((q : K) ^ earlier) *
                    indeterminate ^ (2 * (bound - 1 - earlier))) + scalar ((q : K) ^ bound) := by
            rw [Finset.sum_range_succ, Finset.mul_sum]
            simp only [Nat.sub_self, mul_zero, pow_zero, mul_one]
            congr 1
            apply Finset.sum_congr rfl
            intro earlier hearlier
            rw [Finset.mem_range] at hearlier
            rw [show 2 * (bound - earlier) = 2 + 2 * (bound - 1 - earlier) by omega,
              pow_add]
            ring
          rw [show bound + 1 - 1 = bound by omega, hsum]
          calc
            _ = indeterminate ^ 2 * ((scalar (q : K) - indeterminate ^ 2) *
                (∑ earlier ∈ Finset.range bound,
                  scalar ((q : K) ^ earlier) *
                    indeterminate ^ (2 * (bound - 1 - earlier)))) +
                (scalar (q : K) - indeterminate ^ 2) * scalar ((q : K) ^ bound) := by ring
            _ = scalar ((q : K) ^ (bound + 1)) - indeterminate ^ (2 * (bound + 1)) := by
              rw [ih, pow_succ (q : K), map_mul,
                show 2 * (bound + 1) = 2 * bound + 2 by omega, pow_add]
              ring
    have hforwardMap : forwardLaurent = ∑ earlier ∈ Finset.range index,
        scalar ((q : K) ^ earlier) * indeterminate ^ (2 * earlier) := by
      simp [forwardLaurent, forward, map_sum, map_mul, map_pow, scalar, indeterminate]
    have hreverseMap : reverseLaurent = ∑ earlier ∈ Finset.range index,
        scalar ((q : K) ^ earlier) * indeterminate ^ (2 * (index - 1 - earlier)) := by
      simp [reverseLaurent, reverse, map_sum, map_mul, map_pow, scalar, indeterminate]
    have hindeterminatePower : indeterminate ^ (2 * index) *
        LaurentPolynomial.T (-(index : ℤ)) = LaurentPolynomial.T (index : ℤ) := by
      simp only [indeterminate, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
      congr 1
      push_cast
      ring
    have hscalarPower : scalar ((q : K) ^ index) * scalar ((q : K) ^ (-(index : ℤ))) =
        1 := by
      rw [← map_mul, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ q.ne_zero),
        map_one]
    have hshiftForward :
        laurentShift q (LaurentPolynomial.T (index : ℤ) +
          LaurentPolynomial.T (-(index : ℤ))) -
            (LaurentPolynomial.T (index : ℤ) + LaurentPolynomial.T (-(index : ℤ))) =
          -(scalar ((q : K) ^ index - 1) * scalar ((q : K) ^ (-(index : ℤ))) *
            LaurentPolynomial.T (-(index : ℤ)) *
              (1 - scalar (q : K) * indeterminate ^ 2) * forwardLaurent) := by
      rw [hforwardMap, mul_assoc _ (1 - scalar (q : K) * indeterminate ^ 2), hforward]
      simp only [map_add, hshift, zpow_natCast, map_sub, map_one]
      linear_combination
        -(scalar ((q : K) ^ index) - 1) * hindeterminatePower +
        (LaurentPolynomial.T (-(index : ℤ)) -
          (scalar ((q : K) ^ index) - 1) * indeterminate ^ (2 * index) *
            LaurentPolynomial.T (-(index : ℤ))) * hscalarPower
    have hshiftReverse :
        laurentShift q⁻¹ (LaurentPolynomial.T (index : ℤ) +
          LaurentPolynomial.T (-(index : ℤ))) -
            (LaurentPolynomial.T (index : ℤ) + LaurentPolynomial.T (-(index : ℤ))) =
          scalar ((q : K) ^ index - 1) * scalar ((q : K) ^ (-(index : ℤ))) *
            LaurentPolynomial.T (-(index : ℤ)) *
              (scalar (q : K) - indeterminate ^ 2) * reverseLaurent := by
      rw [hreverseMap, mul_assoc _ (scalar (q : K) - indeterminate ^ 2), hreverse]
      simp only [map_add, hshift, Units.val_inv_eq_inv_val,
        zpow_natCast, zpow_neg, inv_pow, inv_inv, map_sub, map_one]
      simp only [zpow_neg, zpow_natCast] at hscalarPower
      linear_combination
        scalar (((q : K) ^ index)⁻¹) * (scalar ((q : K) ^ index) - 1) *
            hindeterminatePower +
          (LaurentPolynomial.T (index : ℤ) - (scalar ((q : K) ^ index) - 1) *
            LaurentPolynomial.T (-(index : ℤ))) * hscalarPower
    refine ⟨scalar ((q : K) ^ index - 1) * scalar ((q : K) ^ (-(index : ℤ))) *
      LaurentPolynomial.T (-(index : ℤ)) * (-outputPolynomial).toLaurent, ?_⟩
    have hmap := congrArg Polynomial.toLaurent hdivision
    simp only [numerator, map_sub, map_mul, map_pow, map_one,
      Polynomial.toLaurent_X, Polynomial.toLaurent_C] at hmap
    change indeterminate ^ 2 * (indeterminate - scalar rho) ^ 2 * reverseLaurent -
      (1 - scalar rho * indeterminate) ^ 2 * forwardLaurent =
        (1 - indeterminate ^ 2) * (-outputPolynomial).toLaurent at hmap
    simp only [differenceNumerator, hshiftForward, hshiftReverse]
    dsimp only [denominator]
    rw [show _ + _ =
      (1 - scalar (q : K) * indeterminate ^ 2) * (scalar (q : K) - indeterminate ^ 2) *
      (scalar ((q : K) ^ index - 1) * scalar ((q : K) ^ (-(index : ℤ))) *
        LaurentPolynomial.T (-(index : ℤ))) *
      (indeterminate ^ 2 * (indeterminate - scalar rho) ^ 2 * reverseLaurent -
        (1 - scalar rho * indeterminate) ^ 2 * forwardLaurent) by ring]
    rw [hmap]
    ring
  have hnegative (location : ℤ) : poly.coeff (-location) = poly.coeff location := by
    simpa only [LaurentPolynomial.invert_apply] using
      congrArg (fun input => input.coeff location) hsymmetric
  have hreconstruction : poly = scalar (poly.coeff 0) +
      ∑ earlier ∈ Finset.range degree,
        scalar (poly.coeff ((earlier + 1 : ℕ) : ℤ)) *
          (LaurentPolynomial.T ((earlier + 1 : ℕ) : ℤ) +
            LaurentPolynomial.T (-((earlier + 1 : ℕ) : ℤ))) := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro location
    dsimp only [scalar]
    simp only [mul_add, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single,
      LaurentPolynomial.C_apply, Finsupp.single_apply]
    by_cases hzero : location = 0
    · subst location
      simp only [if_true, left_eq_add]
      apply Finset.sum_eq_zero
      intro earlier _
      simp only [if_neg (show ((earlier + 1 : ℕ) : ℤ) ≠ 0 by omega),
        if_neg (show -((earlier + 1 : ℕ) : ℤ) ≠ 0 by omega), zero_add]
    · simp only [if_neg hzero, zero_add]
      by_cases hlarge : (degree : ℤ) < |location|
      · rw [hbounded location hlarge]
        apply Eq.symm
        apply Finset.sum_eq_zero
        intro earlier hearlier
        rw [Finset.mem_range] at hearlier
        have hpositive : ((earlier + 1 : ℕ) : ℤ) ≠ location := by
          intro heq
          rw [← heq, abs_of_nonneg (by omega)] at hlarge
          omega
        have hnegative : -((earlier + 1 : ℕ) : ℤ) ≠ location := by
          intro heq
          rw [← heq, abs_neg, abs_of_nonneg (by omega)] at hlarge
          omega
        simp only [if_neg hpositive, if_neg hnegative, zero_add]
      · let earlier := location.natAbs - 1
        have hindex : earlier ∈ Finset.range degree := by
          rw [Finset.mem_range]
          have habs : (location.natAbs : ℤ) = |location| := Int.natCast_natAbs location
          have hpos : 0 < location.natAbs := Int.natAbs_pos.mpr hzero
          dsimp only [earlier]
          omega
        rw [Finset.sum_eq_single_of_mem earlier hindex]
        · have habs : ((earlier + 1 : ℕ) : ℤ) = |location| := by
            have hpos : 0 < location.natAbs := Int.natAbs_pos.mpr hzero
            dsimp only [earlier]
            rw [Nat.sub_add_cancel hpos, Int.natCast_natAbs]
          rcases lt_or_gt_of_ne hzero with hneg | hpos
          · simp only [habs, abs_of_neg hneg, neg_neg,
              if_neg (show -location ≠ location by omega), if_true, zero_add, hnegative]
          · simp only [habs, abs_of_pos hpos,
              if_neg (show -location ≠ location by omega), if_true, add_zero]
        · intro other hother hne
          rw [Finset.mem_range] at hother
          have habs : (location.natAbs : ℤ) = |location| := Int.natCast_natAbs location
          have hpositive : ((other + 1 : ℕ) : ℤ) ≠ location := by
            intro heq
            have hpos : 0 ≤ location := by omega
            rw [abs_of_nonneg hpos] at habs
            dsimp only [earlier] at hne
            omega
          have hnegative : -((other + 1 : ℕ) : ℤ) ≠ location := by
            intro heq
            have hneg : location ≤ 0 := by omega
            rw [abs_of_nonpos hneg] at habs
            dsimp only [earlier] at hne
            omega
          simp only [if_neg hpositive, if_neg hnegative, zero_add]
  choose outputs houtputs using fun earlier : Fin degree =>
    hpair (earlier.val + 1)
  let output := ∑ earlier : Fin degree,
    scalar (poly.coeff ((earlier.val + 1 : ℕ) : ℤ)) * outputs earlier
  have hconstructed : denominator * output = differenceNumerator rho q poly := by
    rw [hreconstruction, hscalarAdd, hconstant, zero_add]
    dsimp only [output]
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    have hsum (inputs : Finset (Fin degree)) :
        differenceNumerator rho q (∑ earlier ∈ inputs,
          scalar (poly.coeff ((earlier.val + 1 : ℕ) : ℤ)) *
            (LaurentPolynomial.T ((earlier.val + 1 : ℕ) : ℤ) +
              LaurentPolynomial.T (-((earlier.val + 1 : ℕ) : ℤ)))) =
          ∑ earlier ∈ inputs,
            differenceNumerator rho q
              (scalar (poly.coeff ((earlier.val + 1 : ℕ) : ℤ)) *
                (LaurentPolynomial.T ((earlier.val + 1 : ℕ) : ℤ) +
                  LaurentPolynomial.T (-((earlier.val + 1 : ℕ) : ℤ)))) := by
      induction inputs using Finset.induction_on with
      | empty => simp [differenceNumerator]
      | @insert earlier inputs hnot ih =>
          rw [Finset.sum_insert hnot, Finset.sum_insert hnot, hscalarAdd, ih]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro earlier _
    rw [hscalarMul, ← mul_assoc, mul_comm denominator, mul_assoc, houtputs]
  have hnonzero : denominator ≠ 0 := by
    have hfirst : (1 - indeterminate ^ 2 : LaurentPolynomial K) ≠ 0 := by
      intro h
      have hcoeff := congrArg (fun input => input.coeff 2) h
      change (1 - LaurentPolynomial.T 1 ^ 2 : LaurentPolynomial K).coeff 2 = 0 at hcoeff
      rw [LaurentPolynomial.T_pow] at hcoeff
      change ((Finsupp.single 0 (1 : K) - Finsupp.single 2 1) : ℤ →₀ K) 2 = 0 at hcoeff
      simp at hcoeff
    have hsecond : (1 - scalar (q : K) * indeterminate ^ 2 : LaurentPolynomial K) ≠ 0 := by
      intro h
      have hcoeff := congrArg (fun input => input.coeff 0) h
      change (1 - LaurentPolynomial.C (q : K) * LaurentPolynomial.T 1 ^ 2).coeff 0 = 0
        at hcoeff
      rw [LaurentPolynomial.T_pow, ← LaurentPolynomial.single_eq_C_mul_T] at hcoeff
      change ((Finsupp.single 0 (1 : K) - Finsupp.single 2 (q : K)) : ℤ →₀ K) 0 = 0 at hcoeff
      simp at hcoeff
    have hthird : (scalar (q : K) - indeterminate ^ 2 : LaurentPolynomial K) ≠ 0 := by
      intro h
      have hcoeff := congrArg (fun input => input.coeff 2) h
      change (LaurentPolynomial.C (q : K) - LaurentPolynomial.T 1 ^ 2).coeff 2 = 0
        at hcoeff
      rw [LaurentPolynomial.T_pow] at hcoeff
      change ((Finsupp.single 0 (q : K) - Finsupp.single 2 1) : ℤ →₀ K) 2 = 0 at hcoeff
      simp at hcoeff
    exact mul_ne_zero (mul_ne_zero hfirst hsecond) hthird
  have hreflectShift (scale : Kˣ) (input : LaurentPolynomial K) :
      LaurentPolynomial.invert (laurentShift scale input) =
        laurentShift scale⁻¹ (LaurentPolynomial.invert input) := by
    induction input using LaurentPolynomial.induction_on' with
    | add left right hleft hright => simp only [map_add, hleft, hright]
    | C_mul_T location value =>
        change LaurentPolynomial.invert (laurentShift scale
          (scalar value * LaurentPolynomial.T location)) =
          laurentShift scale⁻¹
            (LaurentPolynomial.invert (scalar value * LaurentPolynomial.T location))
        have hscalar (value : K) : LaurentPolynomial.invert (scalar value) = scalar value :=
          LaurentPolynomial.invert_C value
        simp only [map_mul, hshift, hshiftC, hscalar,
          LaurentPolynomial.invert_T, Units.val_inv_eq_inv_val, inv_zpow, zpow_neg, inv_inv]
  have hreflectDenominator : LaurentPolynomial.invert denominator =
      -LaurentPolynomial.T (-6) * denominator := by
    dsimp only [denominator, indeterminate, scalar]
    simp only [map_mul, map_sub, map_one, map_pow, LaurentPolynomial.invert_C,
      LaurentPolynomial.invert_T]
    have hmonomial : LaurentPolynomial.T (-6) =
        (LaurentPolynomial.T (-1) : LaurentPolynomial K) ^ 6 := by
      rw [LaurentPolynomial.T_pow]; congr 1
    rw [hmonomial]
    ring_nf
    simp only [LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    norm_num [LaurentPolynomial.T_zero]
    ring
  have hreflectNumerator : LaurentPolynomial.invert (differenceNumerator rho q poly) =
      -LaurentPolynomial.T (-6) * differenceNumerator rho q poly := by
    have hfirst : LaurentPolynomial.invert first = -LaurentPolynomial.T (-6) * second := by
      dsimp only [first, second, scalar, indeterminate]
      simp only [map_mul, map_sub, map_one, map_pow, LaurentPolynomial.invert_C,
        LaurentPolynomial.invert_T]
      ring_nf
      simp only [LaurentPolynomial.T_pow, LaurentPolynomial.mul_T_assoc,
        ← LaurentPolynomial.T_add]
      norm_num [LaurentPolynomial.T_zero]
      ring
    have hsecond : LaurentPolynomial.invert second = -LaurentPolynomial.T (-6) * first := by
      dsimp only [first, second, scalar, indeterminate]
      simp only [map_mul, map_sub, map_one, map_pow, LaurentPolynomial.invert_C,
        LaurentPolynomial.invert_T]
      ring_nf
      simp only [LaurentPolynomial.T_pow, LaurentPolynomial.mul_T_assoc,
        ← LaurentPolynomial.T_add]
      norm_num [LaurentPolynomial.T_zero]
      ring
    have hform (input : LaurentPolynomial K) : differenceNumerator rho q input =
        first * (laurentShift q input - input) +
          second * (laurentShift q⁻¹ input - input) := rfl
    rw [hform, map_add,
      map_mul LaurentPolynomial.invert first (laurentShift q poly - poly),
      map_mul LaurentPolynomial.invert second (laurentShift q⁻¹ poly - poly), hfirst, hsecond]
    simp only [map_sub, hreflectShift, hsymmetric, inv_inv]
    ring
  have hreflection : LaurentPolynomial.invert output = output := by
    have h := congrArg LaurentPolynomial.invert hconstructed
    rw [map_mul, hreflectDenominator, hreflectNumerator] at h
    have hunit : (-LaurentPolynomial.T (-6) : LaurentPolynomial K) ≠ 0 := by
      exact neg_ne_zero.mpr (LaurentPolynomial.isUnit_T (-6)).ne_zero
    rw [mul_assoc] at h
    have hcancel := mul_left_cancel₀ hunit h
    rw [← hconstructed] at hcancel
    exact mul_left_cancel₀ hnonzero hcancel
  refine ⟨output, ⟨hconstructed, hreflection⟩, ?_⟩
  intro candidate hcandidate
  apply mul_left_cancel₀ hnonzero
  exact hcandidate.1.trans hconstructed.symm

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Difference
