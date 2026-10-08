/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207ThetaSpecialization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207ThetaSpecialization
   mirror-E: none(waiver:formal-exponential-theta-specialization)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Exp]
   utility: none
   digest: Finite energy fibres identify actual theta products with the parity lattice kernel. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207TripleProduct
import Mathlib.RingTheory.PowerSeries.Exp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207ThetaSpecialization

open InversionSeq207TripleProduct
open Finset.HasAntidiagonal

noncomputable def normalizedTheta {R : Type*} [CommRing R] [Algebra ℚ R]
    (direction : R) : PowerSeries (PowerSeries R) :=
  let character : Multiplicative ℤ →* PowerSeries R :=
    { toFun := fun index => PowerSeries.rescale (direction * (index.toAdd : R))
        (PowerSeries.exp R)
      map_one' := by simp [PowerSeries.rescale_zero, PowerSeries.constantCoeff_exp]
      map_mul' := by
        intro first second
        change PowerSeries.rescale (direction * ((first.toAdd + second.toAdd : ℤ) : R))
          (PowerSeries.exp R) = _
        rw [PowerSeries.exp_mul_exp_eq_exp_add]
        congr 1
        push_cast
        ring }
  let evaluate := AddMonoidAlgebra.liftNCRingHom
    (PowerSeries.C.comp (algebraMap ℚ R)) character (fun _ _ => Commute.all _ _)
  PowerSeries.C (PowerSeries.rescale
    (-direction * algebraMap ℚ R (1 / 2)) (PowerSeries.exp R)) *
    PowerSeries.map evaluate formalTheta

set_option maxHeartbeats 1600000 in
theorem theta_exponential_addition {R : Type*} [CommRing R] [Algebra ℚ R]
    (first second third fourth : R) :
    normalizedTheta (first + second) * normalizedTheta (first - second) *
          (normalizedTheta (third + fourth) * normalizedTheta (third - fourth)) -
        normalizedTheta (first + fourth) * normalizedTheta (first - fourth) *
          (normalizedTheta (third + second) * normalizedTheta (third - second)) =
      normalizedTheta (first + third) * normalizedTheta (first - third) *
        (normalizedTheta (second + fourth) * normalizedTheta (second - fourth)) := by
  classical
  let exponential := fun direction : R =>
    PowerSeries.rescale direction (PowerSeries.exp R)
  let scalar : PowerSeries (PowerSeries R) :=
    PowerSeries.map (PowerSeries.C.comp (algebraMap ℚ R))
      (PowerSeries.pentagonalSeries ℚ)
  let energy := fun index : ℤ =>
    if 0 ≤ index then index.toNat.choose 2 else (index.natAbs + 1).choose 2
  let sign := fun index : ℤ => (-1 : ℚ) ^ index.natAbs
  have hchoose (index : ℕ) : 2 * index.choose 2 = index * (index - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one index)
  have henergy (index : ℤ) : 2 * (energy index : ℤ) = index * (index - 1) := by
    by_cases hpositive : 0 ≤ index
    · simp only [energy, if_pos hpositive]
      by_cases hsmall : index.toNat < 2
      · have hindexSmall : index ≤ 1 := by omega
        interval_cases index <;> norm_num
      · have hcast := congrArg (fun value : ℕ => (value : ℤ)) (hchoose index.toNat)
        simp only [Nat.cast_mul, Nat.cast_ofNat] at hcast
        rw [Int.toNat_of_nonneg hpositive] at hcast
        rw [Int.natCast_sub (by omega), Int.toNat_of_nonneg hpositive] at hcast
        exact hcast
    · simp only [energy, if_neg hpositive]
      have hnat := hchoose (index.natAbs + 1)
      simp only [Nat.add_sub_cancel] at hnat
      have hcast := congrArg (fun value : ℕ => (value : ℤ)) hnat
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hcast
      have habs : (index.natAbs : ℤ) = -index := by
        rw [Int.natCast_natAbs, abs_of_neg (by omega)]
      rw [habs] at hcast
      nlinarith
  have hbound (degree : ℕ) (index : ℤ) (hle : energy index ≤ degree) :
      index ∈ Finset.Icc (-(degree : ℤ) - 1) (degree + 1) := by
    have henergy := henergy index
    have hcast : (energy index : ℤ) ≤ degree := by exact_mod_cast hle
    rw [Finset.mem_Icc]
    constructor <;> by_contra hbad
    · have hproduct := mul_nonneg_of_nonpos_of_nonpos
        (show index + (degree : ℤ) + 2 ≤ 0 by omega)
        (show index - (degree : ℤ) - 1 ≤ 0 by omega)
      nlinarith [sq_nonneg (degree : ℤ)]
    · have hproduct := mul_nonneg
        (show 0 ≤ index - (degree : ℤ) - 2 by omega)
        (show 0 ≤ index + (degree : ℤ) + 1 by omega)
      nlinarith [sq_nonneg (degree : ℤ)]
  let lattice : PowerSeries (LaurentPolynomial ℚ) :=
    PowerSeries.map LaurentPolynomial.C (PowerSeries.pentagonalSeries ℚ) * formalTheta
  have hlattice (degree : ℕ) (index : ℤ) :
      (PowerSeries.coeff degree lattice).coeff index =
        if energy index = degree then sign index else 0 := by
    have hcolumn := congrArg (PowerSeries.coeff degree) (formal_triple_product index)
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow] at hcolumn
    rw [PowerSeries.coeff_mul] at hcolumn
    simp only [PowerSeries.coeff_mk] at hcolumn
    dsimp only [lattice]
    rw [PowerSeries.coeff_mul]
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      PowerSeries.coeff_map]
    have hconstant (value : ℚ) (polynomial : LaurentPolynomial ℚ) :
        (LaurentPolynomial.C value * polynomial).coeff index =
          value * polynomial.coeff index := by
      exact AddMonoidAlgebra.coeff_single_zero_mul polynomial value index
    simp_rw [hconstant]
    rw [hcolumn]
    simp only [energy, sign, mul_ite, mul_one, mul_zero, eq_comm]
  have hexpMul (left right : R) :
      exponential left * exponential right = exponential (left + right) :=
    PowerSeries.exp_mul_exp_eq_exp_add left right
  have hfourier (direction : R) (degree : ℕ) :
      PowerSeries.coeff degree (scalar * normalizedTheta direction) =
        ∑ index ∈ Finset.Icc (-(degree : ℤ) - 1) (degree + 1),
          if energy index = degree then
            PowerSeries.C (algebraMap ℚ R (sign index)) *
              exponential (((index : R) - algebraMap ℚ R (1 / 2)) * direction)
          else 0 := by
    let character : Multiplicative ℤ →* PowerSeries R :=
      { toFun := fun index => exponential (direction * (index.toAdd : R))
        map_one' := by simp [exponential, PowerSeries.rescale_zero]
        map_mul' := by
          intro left right
          change exponential (direction * ((left.toAdd + right.toAdd : ℤ) : R)) = _
          rw [hexpMul]
          congr 1
          push_cast
          ring }
    let evaluate := AddMonoidAlgebra.liftNCRingHom
      (PowerSeries.C.comp (algebraMap ℚ R)) character (fun _ _ => Commute.all _ _)
    have hevaluateConstant (value : ℚ) :
        evaluate (LaurentPolynomial.C value) = PowerSeries.C (algebraMap ℚ R value) := by
      simpa using AddMonoidAlgebra.liftNCRingHom_single
        (PowerSeries.C.comp (algebraMap ℚ R)) character
          (fun _ _ => Commute.all _ _) 0 value
    have hevaluateMonomial (value : ℚ) (index : ℤ) :
        evaluate (LaurentPolynomial.C value * LaurentPolynomial.T index) =
          PowerSeries.C (algebraMap ℚ R value) * exponential (direction * (index : R)) := by
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      exact AddMonoidAlgebra.liftNCRingHom_single _ _ _ _ _
    have hmap : PowerSeries.map evaluate
        (PowerSeries.map LaurentPolynomial.C (PowerSeries.pentagonalSeries ℚ)) = scalar := by
      apply PowerSeries.ext
      intro degree
      simp only [scalar, PowerSeries.coeff_map]
      exact hevaluateConstant _
    have hnormalized : scalar * normalizedTheta direction =
        PowerSeries.C (exponential (-direction * algebraMap ℚ R (1 / 2))) *
          PowerSeries.map evaluate lattice := by
      change scalar * (PowerSeries.C
        (exponential (-direction * algebraMap ℚ R (1 / 2))) *
        PowerSeries.map evaluate formalTheta) = _
      dsimp only [lattice]
      rw [map_mul, hmap]
      ring
    have hexpansion : PowerSeries.coeff degree lattice =
        ∑ index ∈ Finset.Icc (-(degree : ℤ) - 1) (degree + 1),
          LaurentPolynomial.C
            (if energy index = degree then sign index else 0) *
              LaurentPolynomial.T index := by
      ext index
      rw [hlattice]
      simp only [← LaurentPolynomial.single_eq_C_mul_T,
        AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single]
      rw [Finset.sum_eq_single index]
      · simp
      · intro other _ hother
        simp [hother]
      · intro houtside
        have hne : energy index ≠ degree := by
          intro hequal
          exact houtside (hbound degree index (by omega))
        simp [hne]
    rw [hnormalized, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, hexpansion, map_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [hevaluateMonomial]
    by_cases hequal : energy index = degree
    · simp only [if_pos hequal]
      calc
        _ = PowerSeries.C (algebraMap ℚ R (sign index)) *
            (exponential (-direction * algebraMap ℚ R (1 / 2)) *
              exponential (direction * (index : R))) := by
              ring
        _ = _ := by rw [hexpMul]; congr 2; ring
    · simp [hequal]
  let pairSeries := fun (left right : R) => PowerSeries.mk fun degree =>
    ∑ pair ∈ (Finset.Icc (-(degree : ℤ) - 1) (degree + 1) ×ˢ
        Finset.Icc (-(degree : ℤ) - 1) (degree + 1)).filter
          (fun pair => pair.1 * (pair.1 - 1) + pair.2 * (pair.2 - 1) =
            2 * (degree : ℤ)),
      (if Even (pair.1 + pair.2) then (1 : PowerSeries R) else -1) *
        exponential ((pair.1 + pair.2 - 1 : ℤ) * left) *
          exponential ((pair.1 - pair.2 : ℤ) * right)
  have hpair (left right : R) :
      (scalar * normalizedTheta (left + right)) *
          (scalar * normalizedTheta (left - right)) = pairSeries left right := by
    apply PowerSeries.ext
    intro degree
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk]
    let indices := Finset.Icc (-(degree : ℤ) - 1) (degree + 1)
    let weight := fun (direction : R) (index : ℤ) =>
      PowerSeries.C (algebraMap ℚ R (sign index)) *
        exponential (((index : R) - algebraMap ℚ R (1 / 2)) * direction)
    have hpadding (direction : R) (smaller : ℕ) (hle : smaller ≤ degree) :
        PowerSeries.coeff smaller (scalar * normalizedTheta direction) =
          ∑ index ∈ indices, if energy index = smaller then weight direction index else 0 := by
      rw [hfourier]
      apply Finset.sum_subset
      · apply Finset.Icc_subset_Icc <;> omega
      · intro index _ houtside
        rw [if_neg]
        intro hequal
        exact houtside (hbound smaller index (by omega))
    have hdelta (firstIndex secondIndex : ℤ) :
        (∑ split ∈ antidiagonal degree,
          (if energy firstIndex = split.1 then weight (left + right) firstIndex else 0) *
            (if energy secondIndex = split.2 then weight (left - right) secondIndex else 0)) =
        if energy firstIndex + energy secondIndex = degree then
          weight (left + right) firstIndex * weight (left - right) secondIndex else 0 := by
      by_cases hsum : energy firstIndex + energy secondIndex = degree
      · rw [if_pos hsum]
        let selected := (energy firstIndex, energy secondIndex)
        rw [Finset.sum_eq_single selected]
        · simp [selected]
        · intro split _ hne
          by_cases hfirst : energy firstIndex = split.1
          · by_cases hsecond : energy secondIndex = split.2
            · exact False.elim (hne (Prod.ext hfirst.symm hsecond.symm))
            · simp [hsecond]
          · simp [hfirst]
        · intro houtside
          exact False.elim (houtside (mem_antidiagonal.mpr hsum))
      · rw [if_neg hsum]
        apply Finset.sum_eq_zero
        intro split hsplit
        have htotal := mem_antidiagonal.mp hsplit
        by_cases hfirst : energy firstIndex = split.1
        · by_cases hsecond : energy secondIndex = split.2
          · exact False.elim (hsum (by omega))
          · simp [hsecond]
        · simp [hfirst]
    have hconvolution :
        (∑ split ∈ antidiagonal degree,
          PowerSeries.coeff split.1 (scalar * normalizedTheta (left + right)) *
            PowerSeries.coeff split.2 (scalar * normalizedTheta (left - right))) =
        ∑ pair ∈ indices ×ˢ indices,
          if energy pair.1 + energy pair.2 = degree then
            weight (left + right) pair.1 * weight (left - right) pair.2 else 0 := by
      calc
        _ = ∑ split ∈ antidiagonal degree,
            (∑ index ∈ indices,
              if energy index = split.1 then weight (left + right) index else 0) *
            (∑ index ∈ indices,
              if energy index = split.2 then weight (left - right) index else 0) := by
          apply Finset.sum_congr rfl
          intro split hsplit
          have htotal := mem_antidiagonal.mp hsplit
          rw [hpadding _ split.1 (by omega), hpadding _ split.2 (by omega)]
        _ = ∑ firstIndex ∈ indices, ∑ secondIndex ∈ indices,
            ∑ split ∈ antidiagonal degree,
              (if energy firstIndex = split.1 then weight (left + right) firstIndex else 0) *
                (if energy secondIndex = split.2 then
                  weight (left - right) secondIndex else 0) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro index _
          rw [Finset.sum_comm]
        _ = _ := by simp_rw [hdelta]; rw [Finset.sum_product]
    rw [hconvolution, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro pair _
    have hequivalent : energy pair.1 + energy pair.2 = degree ↔
        pair.1 * (pair.1 - 1) + pair.2 * (pair.2 - 1) = 2 * (degree : ℤ) := by
      have hfirst := henergy pair.1
      have hsecond := henergy pair.2
      constructor
      · intro hequal
        have hcast := congrArg (fun value : ℕ => (value : ℤ)) hequal
        simp only [Nat.cast_add] at hcast
        omega
      · intro hequal
        have hcast : (energy pair.1 + energy pair.2 : ℤ) = degree := by omega
        exact_mod_cast hcast
    by_cases hequal : energy pair.1 + energy pair.2 = degree
    · rw [if_pos hequal, if_pos (hequivalent.mp hequal)]
      have hsign (index : ℤ) : sign index = if Even index then (1 : ℚ) else -1 := by
        simp [sign, neg_one_pow_eq_ite, Int.natAbs_even]
      have hsignMul : sign pair.1 * sign pair.2 =
          if Even (pair.1 + pair.2) then (1 : ℚ) else -1 := by
        rw [hsign, hsign]
        by_cases hfirst : Even pair.1 <;> by_cases hsecond : Even pair.2 <;>
          simp [hfirst, hsecond, Int.even_add]
      have hcastSign :
          PowerSeries.C (algebraMap ℚ R (sign pair.1)) *
            PowerSeries.C (algebraMap ℚ R (sign pair.2)) =
              if Even (pair.1 + pair.2) then (1 : PowerSeries R) else -1 := by
        rw [← map_mul, ← map_mul, hsignMul]
        split_ifs <;> simp
      dsimp only [weight]
      calc
        _ = (PowerSeries.C (algebraMap ℚ R (sign pair.1)) *
            PowerSeries.C (algebraMap ℚ R (sign pair.2))) *
            (exponential (((pair.1 : R) - algebraMap ℚ R (1 / 2)) * (left + right)) *
              exponential (((pair.2 : R) - algebraMap ℚ R (1 / 2)) * (left - right))) := by
                ring
        _ = _ := by
          rw [hcastSign, hexpMul, mul_assoc, hexpMul]
          congr 2
          push_cast
          have hhalf : 2 * algebraMap ℚ R (1 / 2) = 1 := by
            calc
              _ = algebraMap ℚ R (2 * (1 / 2)) := by simp only [map_mul, map_ofNat]
              _ = 1 := by norm_num
          linear_combination -(left * hhalf)
    · rw [if_neg hequal, if_neg (mt hequivalent.mpr hequal)]
  have hparity
      (firstWeight secondWeight thirdWeight fourthWeight : ℤ → (PowerSeries R)) :
      let pairSeries := fun (firstWeight secondWeight : ℤ → PowerSeries R) =>
        PowerSeries.mk fun degree =>
        ∑ pair ∈ (Finset.Icc (-(degree : ℤ) - 1) (degree + 1) ×ˢ
            Finset.Icc (-(degree : ℤ) - 1) (degree + 1)).filter
              (fun pair => pair.1 * (pair.1 - 1) + pair.2 * (pair.2 - 1) =
                2 * (degree : ℤ)),
          (if Even (pair.1 + pair.2) then (1 : (PowerSeries R)) else -1) *
            firstWeight (pair.1 + pair.2 - 1) * secondWeight (pair.1 - pair.2)
      pairSeries firstWeight secondWeight * pairSeries thirdWeight fourthWeight -
          pairSeries firstWeight fourthWeight * pairSeries thirdWeight secondWeight =
        pairSeries firstWeight thirdWeight * pairSeries secondWeight fourthWeight := by
    classical
    let pairSeries := fun (firstWeight secondWeight : ℤ → PowerSeries R) =>
      PowerSeries.mk fun degree =>
      ∑ pair ∈ (Finset.Icc (-(degree : ℤ) - 1) (degree + 1) ×ˢ
          Finset.Icc (-(degree : ℤ) - 1) (degree + 1)).filter
            (fun pair => pair.1 * (pair.1 - 1) + pair.2 * (pair.2 - 1) =
              2 * (degree : ℤ)),
        (if Even (pair.1 + pair.2) then (1 : (PowerSeries R)) else -1) *
          firstWeight (pair.1 + pair.2 - 1) * secondWeight (pair.1 - pair.2)
    change pairSeries firstWeight secondWeight * pairSeries thirdWeight fourthWeight -
        pairSeries firstWeight fourthWeight * pairSeries thirdWeight secondWeight =
      pairSeries firstWeight thirdWeight * pairSeries secondWeight fourthWeight
    have hdecomposition (firstWeight secondWeight : ℤ → (PowerSeries R)) :
        let evenFamily := fun weight : ℤ → (PowerSeries R) => PowerSeries.mk fun degree =>
          ∑ index ∈ Finset.Icc (-(degree : ℤ) - 1) (degree + 1),
            if index ^ 2 = (degree : ℤ) then weight (2 * index) else 0
        let oddFamily := fun weight : ℤ → (PowerSeries R) => PowerSeries.mk fun degree =>
          ∑ index ∈ Finset.Icc (-(degree : ℤ) - 1) (degree + 1),
            if index * (index + 1) = (degree : ℤ) then weight (2 * index + 1) else 0
        PowerSeries.mk (fun degree =>
          ∑ pair ∈ (Finset.Icc (-(degree : ℤ) - 1) (degree + 1) ×ˢ
              Finset.Icc (-(degree : ℤ) - 1) (degree + 1)).filter
                (fun pair => pair.1 * (pair.1 - 1) + pair.2 * (pair.2 - 1) =
                  2 * (degree : ℤ)),
            (if Even (pair.1 + pair.2) then (1 : (PowerSeries R)) else -1) *
              firstWeight (pair.1 + pair.2 - 1) * secondWeight (pair.1 - pair.2)) =
          oddFamily firstWeight * evenFamily secondWeight -
            evenFamily firstWeight * oddFamily secondWeight := by
      classical
      have hreindex (degree : ℕ) :
        (∑ pair ∈ (Finset.Icc (-(degree : ℤ) - 1) (degree + 1) ×ˢ
            Finset.Icc (-(degree : ℤ) - 1) (degree + 1)).filter
              (fun pair => pair.1 * (pair.1 - 1) + pair.2 * (pair.2 - 1) = 2 * (degree : ℤ)),
          (if Even (pair.1 + pair.2) then (1 : (PowerSeries R)) else -1) *
            firstWeight (pair.1 + pair.2 - 1) * secondWeight (pair.1 - pair.2)) =
        (∑ pair ∈ (Finset.Icc (-(degree : ℤ) - 1) (degree + 1) ×ˢ
            Finset.Icc (-(degree : ℤ) - 1) (degree + 1)).filter
              (fun pair => pair.1 * (pair.1 + 1) + pair.2 ^ 2 = (degree : ℤ)),
          firstWeight (2 * pair.1 + 1) * secondWeight (2 * pair.2)) -
        (∑ pair ∈ (Finset.Icc (-(degree : ℤ) - 1) (degree + 1) ×ˢ
            Finset.Icc (-(degree : ℤ) - 1) (degree + 1)).filter
              (fun pair => pair.1 ^ 2 + pair.2 * (pair.2 + 1) = (degree : ℤ)),
          firstWeight (2 * pair.1) * secondWeight (2 * pair.2 + 1)) := by
        classical
        let box := Finset.Icc (-(degree : ℤ) - 1) (degree + 1) ×ˢ
          Finset.Icc (-(degree : ℤ) - 1) (degree + 1)
        let source := box.filter fun pair =>
          pair.1 * (pair.1 - 1) + pair.2 * (pair.2 - 1) = 2 * (degree : ℤ)
        let positive := box.filter fun pair => pair.1 * (pair.1 + 1) + pair.2 ^ 2 = (degree : ℤ)
        let negative := box.filter fun pair => pair.1 ^ 2 + pair.2 * (pair.2 + 1) = (degree : ℤ)
        let weight := fun pair : ℤ × ℤ =>
          firstWeight (pair.1 + pair.2 - 1) * secondWeight (pair.1 - pair.2)
        have hconsecutive (index : ℤ) : 0 ≤ index * (index - 1) := by
          by_cases hnonpositive : index ≤ 0
          · exact mul_nonneg_of_nonpos_of_nonpos hnonpositive (by omega)
          · exact mul_nonneg (by omega) (by omega)
        have hbound (index : ℤ) (henergy : index * (index - 1) ≤ 2 * degree) :
            index ∈ Finset.Icc (-(degree : ℤ) - 1) (degree + 1) := by
          rw [Finset.mem_Icc]
          constructor
          · by_contra hsmall
            have hgap : index ≤ -(degree : ℤ) - 2 := by omega
            have hproduct := mul_nonneg_of_nonpos_of_nonpos
              (show index + (degree : ℤ) + 2 ≤ 0 by omega)
              (show index - (degree : ℤ) - 1 ≤ 0 by omega)
            nlinarith [sq_nonneg (degree : ℤ)]
          · by_contra hlarge
            have hgap : (degree : ℤ) + 2 ≤ index := by omega
            have hproduct := mul_nonneg
              (show 0 ≤ index - (degree : ℤ) - 2 by omega)
              (show 0 ≤ index + (degree : ℤ) + 1 by omega)
            nlinarith [sq_nonneg (degree : ℤ)]
        have htargetBound (index : ℤ) (henergy : index * (index + 1) ≤ degree) :
            index ∈ Finset.Icc (-(degree : ℤ) - 1) (degree + 1) := by
          have hprevious := hbound (-index) (by nlinarith)
          simp only [Finset.mem_Icc] at hprevious ⊢
          omega
        have hsquareBound (index : ℤ) (henergy : index ^ 2 ≤ degree) :
            index ∈ Finset.Icc (-(degree : ℤ) - 1) (degree + 1) := by
          rw [Finset.mem_Icc]
          constructor <;> by_contra hbad
          · have hgap : index ≤ -(degree : ℤ) - 2 := by omega
            have hproduct := mul_nonneg_of_nonpos_of_nonpos
              (show index + (degree : ℤ) + 2 ≤ 0 by omega)
              (show index - (degree : ℤ) - 2 ≤ 0 by omega)
            nlinarith [sq_nonneg (degree : ℤ)]
          · have hgap : (degree : ℤ) + 2 ≤ index := by omega
            have hproduct := mul_nonneg
              (show 0 ≤ index - (degree : ℤ) - 2 by omega)
              (show 0 ≤ index + (degree : ℤ) + 2 by omega)
            nlinarith [sq_nonneg (degree : ℤ)]
        have hpositive : (∑ pair ∈ positive,
            firstWeight (2 * pair.1 + 1) * secondWeight (2 * pair.2)) =
            ∑ pair ∈ source.filter (fun pair => Even (pair.1 + pair.2)), weight pair := by
          apply Finset.sum_bij (fun pair _ => (pair.1 + pair.2 + 1, pair.1 - pair.2 + 1))
          · intro pair hpair
            have henergy := (Finset.mem_filter.mp hpair).2
            change pair.1 * (pair.1 + 1) + pair.2 ^ 2 = degree at henergy
            have htotal : (pair.1 + pair.2 + 1) * (pair.1 + pair.2) +
                (pair.1 - pair.2 + 1) * (pair.1 - pair.2) = 2 * degree := by
              nlinarith
            apply Finset.mem_filter.mpr
            constructor
            · apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, by dsimp; nlinarith [htotal]⟩
              · exact hbound _ (by nlinarith [hconsecutive (pair.1 - pair.2 + 1)])
              · exact hbound _ (by nlinarith [hconsecutive (pair.1 + pair.2 + 1)])
            · exact ⟨pair.1 + 1, by dsimp; ring⟩
          · intro first _ second _ hequality
            have hfirst := congrArg Prod.fst hequality
            have hsecond := congrArg Prod.snd hequality
            apply Prod.ext <;> dsimp at hfirst hsecond ⊢ <;> omega
          · intro pair hpair
            rcases Finset.mem_filter.mp hpair with ⟨hsource, ⟨half, hhalf⟩⟩
            have henergy := (Finset.mem_filter.mp hsource).2
            change pair.1 * (pair.1 - 1) + pair.2 * (pair.2 - 1) = 2 * degree at henergy
            let candidate : ℤ × ℤ := (half - 1, pair.1 - half)
            have hcandidate : candidate.1 * (candidate.1 + 1) + candidate.2 ^ 2 = degree := by
              dsimp [candidate]
              have hsecond : pair.2 = 2 * half - pair.1 := by omega
              rw [hsecond] at henergy
              nlinarith
            refine ⟨candidate, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hcandidate⟩
              · exact htargetBound _ (by nlinarith [sq_nonneg candidate.2])
              · exact hsquareBound _ (by nlinarith [hconsecutive (-candidate.1)])
            · apply Prod.ext <;> dsimp [candidate] <;> omega
          · intro pair _
            dsimp [weight]
            congr 1 <;> congr 1 <;> omega
        have hnegative : (∑ pair ∈ negative,
            firstWeight (2 * pair.1) * secondWeight (2 * pair.2 + 1)) =
            ∑ pair ∈ source.filter (fun pair => ¬Even (pair.1 + pair.2)), weight pair := by
          apply Finset.sum_bij (fun pair _ => (pair.1 + pair.2 + 1, pair.1 - pair.2))
          · intro pair hpair
            have henergy := (Finset.mem_filter.mp hpair).2
            change pair.1 ^ 2 + pair.2 * (pair.2 + 1) = degree at henergy
            have htotal : (pair.1 + pair.2 + 1) * (pair.1 + pair.2) +
                (pair.1 - pair.2) * (pair.1 - pair.2 - 1) = 2 * degree := by
              nlinarith
            apply Finset.mem_filter.mpr
            constructor
            · apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, by dsimp; nlinarith [htotal]⟩
              · exact hbound _ (by nlinarith [hconsecutive (pair.1 - pair.2)])
              · exact hbound _ (by nlinarith [hconsecutive (pair.1 + pair.2 + 1)])
            · rintro ⟨half, hhalf⟩
              dsimp at hhalf
              omega
          · intro first _ second _ hequality
            have hfirst := congrArg Prod.fst hequality
            have hsecond := congrArg Prod.snd hequality
            apply Prod.ext <;> dsimp at hfirst hsecond ⊢ <;> omega
          · intro pair hpair
            rcases Finset.mem_filter.mp hpair with ⟨hsource, hodd⟩
            obtain ⟨half, hhalf⟩ := (Int.not_even_iff_odd.mp hodd)
            have henergy := (Finset.mem_filter.mp hsource).2
            change pair.1 * (pair.1 - 1) + pair.2 * (pair.2 - 1) = 2 * degree at henergy
            let candidate : ℤ × ℤ := (half, pair.1 - half - 1)
            have hcandidate : candidate.1 ^ 2 + candidate.2 * (candidate.2 + 1) = degree := by
              dsimp [candidate]
              have hsecond : pair.2 = 2 * half + 1 - pair.1 := by omega
              rw [hsecond] at henergy
              nlinarith
            refine ⟨candidate, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hcandidate⟩
              · exact hsquareBound _ (by nlinarith [hconsecutive (-candidate.2)])
              · exact htargetBound _ (by nlinarith [sq_nonneg candidate.1])
            · apply Prod.ext <;> dsimp [candidate] <;> omega
          · intro pair _
            dsimp [weight]
            congr 1 <;> congr 1 <;> omega
        simp only [mul_assoc]
        change (∑ pair ∈ source,
          (if Even (pair.1 + pair.2) then (1 : (PowerSeries R)) else -1) * weight pair) = _
        rw [hpositive, hnegative]
        rw [← Finset.sum_filter_add_sum_filter_not source
          (fun pair => Even (pair.1 + pair.2))]
        rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro pair hpair
          rw [if_pos (Finset.mem_filter.mp hpair).2, one_mul]
        · apply Finset.sum_congr rfl
          intro pair hpair
          rw [if_neg (Finset.mem_filter.mp hpair).2, neg_one_mul]
      
      let family := fun (energy : ℤ → ℤ) (weight : ℤ → PowerSeries R) =>
        PowerSeries.mk fun degree =>
        ∑ index ∈ Finset.Icc (-(degree : ℤ) - 1) (degree + 1),
          if energy index = (degree : ℤ) then weight index else 0
      have hconvolution (firstEnergy secondEnergy : ℤ → ℤ)
          (firstTerm secondTerm : ℤ → (PowerSeries R))
          (hfirstNonnegative : ∀ index, 0 ≤ firstEnergy index)
          (hsecondNonnegative : ∀ index, 0 ≤ secondEnergy index)
          (hfirstBound : ∀ (width : ℕ) index, firstEnergy index ≤ width →
            index ∈ Finset.Icc (-(width : ℤ) - 1) (width + 1))
          (hsecondBound : ∀ (width : ℕ) index, secondEnergy index ≤ width →
            index ∈ Finset.Icc (-(width : ℤ) - 1) (width + 1)) (degree : ℕ) :
          PowerSeries.coeff degree
              (family firstEnergy firstTerm * family secondEnergy secondTerm) =
            ∑ pair ∈ (Finset.Icc (-(degree : ℤ) - 1) (degree + 1) ×ˢ
                Finset.Icc (-(degree : ℤ) - 1) (degree + 1)).filter
                  (fun pair => firstEnergy pair.1 + secondEnergy pair.2 = (degree : ℤ)),
              firstTerm pair.1 * secondTerm pair.2 := by
        let indices := Finset.Icc (-(degree : ℤ) - 1) (degree + 1)
        have hpadding (energy : ℤ → ℤ) (weight : ℤ → (PowerSeries R))
            (hbound : ∀ (width : ℕ) index, energy index ≤ width →
              index ∈ Finset.Icc (-(width : ℤ) - 1) (width + 1))
            (smaller : ℕ) (hsmaller : smaller ≤ degree) :
            (∑ index ∈ Finset.Icc (-(smaller : ℤ) - 1) (smaller + 1),
              if energy index = (smaller : ℤ) then weight index else 0) =
            ∑ index ∈ indices, if energy index = (smaller : ℤ) then weight index else 0 := by
          apply Finset.sum_subset
          · apply Finset.Icc_subset_Icc <;> omega
          · intro index _ houtside
            rw [if_neg]
            intro hequality
            exact houtside (hbound smaller index (by omega))
        have hdelta (first second : ℤ) :
            (∑ split ∈ Finset.HasAntidiagonal.antidiagonal degree,
              (if firstEnergy first = (split.1 : ℤ) then firstTerm first else 0) *
                (if secondEnergy second = (split.2 : ℤ) then secondTerm second else 0)) =
            if firstEnergy first + secondEnergy second = (degree : ℤ) then
              firstTerm first * secondTerm second else 0 := by
          by_cases hsum : firstEnergy first + secondEnergy second = (degree : ℤ)
          · rw [if_pos hsum]
            let selected : ℕ × ℕ := ((firstEnergy first).toNat, (secondEnergy second).toNat)
            have hselected : selected ∈ Finset.HasAntidiagonal.antidiagonal degree := by
              rw [mem_antidiagonal]
              have hcast : ((selected.1 + selected.2 : ℕ) : ℤ) = degree := by
                simp only [selected, Nat.cast_add, Int.toNat_of_nonneg (hfirstNonnegative first),
                  Int.toNat_of_nonneg (hsecondNonnegative second), hsum]
              exact_mod_cast hcast
            rw [Finset.sum_eq_single selected]
            · simp [selected, Int.toNat_of_nonneg (hfirstNonnegative first),
                Int.toNat_of_nonneg (hsecondNonnegative second)]
            · intro split _ hother
              by_cases hfirst : firstEnergy first = (split.1 : ℤ)
              · by_cases hsecond : secondEnergy second = (split.2 : ℤ)
                · exfalso
                  apply hother
                  apply Prod.ext
                  · dsimp [selected]
                    rw [hfirst, Int.toNat_natCast]
                  · dsimp [selected]
                    rw [hsecond, Int.toNat_natCast]
                · simp only [if_neg hsecond, mul_zero]
              · simp only [if_neg hfirst, zero_mul]
            · exact fun houtside => False.elim (houtside hselected)
          · rw [if_neg hsum]
            apply Finset.sum_eq_zero
            intro split hsplit
            have htotal := mem_antidiagonal.mp hsplit
            by_cases hfirst : firstEnergy first = (split.1 : ℤ)
            · by_cases hsecond : secondEnergy second = (split.2 : ℤ)
              · exfalso
                apply hsum
                rw [hfirst, hsecond, ← Nat.cast_add, htotal]
              · simp only [if_neg hsecond, mul_zero]
            · simp only [if_neg hfirst, zero_mul]
        rw [PowerSeries.coeff_mul]
        simp only [family, PowerSeries.coeff_mk]
        calc
          _ = ∑ split ∈ Finset.HasAntidiagonal.antidiagonal degree,
              (∑ first ∈ indices,
                if firstEnergy first = (split.1 : ℤ) then firstTerm first else 0) *
              (∑ second ∈ indices,
                if secondEnergy second = (split.2 : ℤ) then secondTerm second else 0) := by
            apply Finset.sum_congr rfl
            intro split hsplit
            have htotal := mem_antidiagonal.mp hsplit
            rw [hpadding firstEnergy firstTerm hfirstBound split.1 (by omega),
              hpadding secondEnergy secondTerm hsecondBound split.2 (by omega)]
          _ = ∑ first ∈ indices, ∑ second ∈ indices,
              ∑ split ∈ Finset.HasAntidiagonal.antidiagonal degree,
                (if firstEnergy first = (split.1 : ℤ) then firstTerm first else 0) *
                (if secondEnergy second = (split.2 : ℤ) then secondTerm second else 0) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro first _
            rw [Finset.sum_comm]
          _ = ∑ first ∈ indices, ∑ second ∈ indices,
              if firstEnergy first + secondEnergy second = (degree : ℤ) then
                firstTerm first * secondTerm second else 0 := by
            apply Finset.sum_congr rfl
            intro first _
            apply Finset.sum_congr rfl
            intro second _
            exact hdelta first second
          _ = _ := by rw [Finset.sum_filter, Finset.sum_product]
      have hconsecutive (index : ℤ) : 0 ≤ index * (index - 1) := by
        by_cases hnonpositive : index ≤ 0
        · exact mul_nonneg_of_nonpos_of_nonpos hnonpositive (by omega)
        · exact mul_nonneg (by omega) (by omega)
      have hbound (width : ℕ) (index : ℤ) (henergy : index * (index - 1) ≤ 2 * width) :
          index ∈ Finset.Icc (-(width : ℤ) - 1) (width + 1) := by
        rw [Finset.mem_Icc]
        constructor <;> by_contra hbad
        · have hproduct := mul_nonneg_of_nonpos_of_nonpos
            (show index + (width : ℤ) + 2 ≤ 0 by omega)
            (show index - (width : ℤ) - 1 ≤ 0 by omega)
          nlinarith [sq_nonneg (width : ℤ)]
        · have hproduct := mul_nonneg
            (show 0 ≤ index - (width : ℤ) - 2 by omega)
            (show 0 ≤ index + (width : ℤ) + 1 by omega)
          nlinarith [sq_nonneg (width : ℤ)]
      have hoddBound (width : ℕ) (index : ℤ) (henergy : index * (index + 1) ≤ width) :
          index ∈ Finset.Icc (-(width : ℤ) - 1) (width + 1) := by
        have hprevious := hbound width (-index) (by nlinarith)
        simp only [Finset.mem_Icc] at hprevious ⊢
        omega
      have hevenBound (width : ℕ) (index : ℤ) (henergy : index ^ 2 ≤ width) :
          index ∈ Finset.Icc (-(width : ℤ) - 1) (width + 1) := by
        rw [Finset.mem_Icc]
        constructor <;> by_contra hbad
        · have hproduct := mul_nonneg_of_nonpos_of_nonpos
            (show index + (width : ℤ) + 2 ≤ 0 by omega)
            (show index - (width : ℤ) - 2 ≤ 0 by omega)
          nlinarith [sq_nonneg (width : ℤ)]
        · have hproduct := mul_nonneg
            (show 0 ≤ index - (width : ℤ) - 2 by omega)
            (show 0 ≤ index + (width : ℤ) + 2 by omega)
          nlinarith [sq_nonneg (width : ℤ)]
      apply PowerSeries.ext
      intro degree
      rw [PowerSeries.coeff_mk, map_sub]
      change _ = PowerSeries.coeff degree
          (family (fun index => index * (index + 1)) (fun index => firstWeight (2 * index + 1)) *
            family (fun index => index ^ 2) (fun index => secondWeight (2 * index))) -
        PowerSeries.coeff degree
          (family (fun index => index ^ 2) (fun index => firstWeight (2 * index)) *
            family (fun index => index * (index + 1)) (fun index => secondWeight (2 * index + 1)))
      rw [hconvolution _ _ _ _ (fun index => by nlinarith [hconsecutive (-index)])
          (fun index => sq_nonneg index) hoddBound hevenBound degree,
        hconvolution _ _ _ _ (fun index => sq_nonneg index)
          (fun index => by nlinarith [hconsecutive (-index)]) hevenBound hoddBound degree]
      exact hreindex degree
    
    dsimp only at hdecomposition
    dsimp only [pairSeries]
    rw [hdecomposition firstWeight secondWeight, hdecomposition thirdWeight fourthWeight,
      hdecomposition firstWeight fourthWeight, hdecomposition thirdWeight secondWeight,
      hdecomposition firstWeight thirdWeight, hdecomposition secondWeight fourthWeight]
    ring
  have haddition := hparity
    (fun index : ℤ => exponential ((index : R) * first))
    (fun index : ℤ => exponential ((index : R) * second))
    (fun index : ℤ => exponential ((index : R) * third))
    (fun index : ℤ => exponential ((index : R) * fourth))
  change pairSeries first second * pairSeries third fourth -
    pairSeries first fourth * pairSeries third second =
      pairSeries first third * pairSeries second fourth at haddition
  rw [← hpair first second, ← hpair third fourth, ← hpair first fourth,
    ← hpair third second, ← hpair first third, ← hpair second fourth] at haddition
  have hscalarUnit : IsUnit scalar := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    have hconstant : PowerSeries.constantCoeff (PowerSeries.pentagonalSeries ℚ) = 1 := by
      have hzero := PowerSeries.coeff_pentagonalSeries_pentagonal ℚ 0
      simpa [PowerSeries.coeff_zero_eq_constantCoeff, pentagonal] using hzero
    change IsUnit (PowerSeries.constantCoeff
      (PowerSeries.map (PowerSeries.C.comp (algebraMap ℚ R))
        (PowerSeries.pentagonalSeries ℚ)))
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hconstant]
    simp
  apply (hscalarUnit.pow 4).mul_left_cancel
  convert haddition using 1 <;> ring

end D5.S3.Combinatorics.InversionSeq.InversionSeq207ThetaSpecialization
