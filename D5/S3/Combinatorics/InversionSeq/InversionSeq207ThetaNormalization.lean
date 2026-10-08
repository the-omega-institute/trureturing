/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207ThetaNormalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207ThetaNormalization
   mirror-E: none(waiver:formal-theta-linear-normalization)
   anchors: []
   utility: none
   digest: Stabilized finite Euler products prove theta oddness and its exact linear term. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207ThetaSpecialization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207ThetaNormalization

open InversionSeq207Euler InversionSeq207TripleProduct InversionSeq207ThetaSpecialization
open Finset.HasAntidiagonal
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

set_option maxHeartbeats 1600000 in
theorem theta_exponential_normalization {R : Type*} [CommRing R] [Algebra ℚ R]
    (direction : R) :
    PowerSeries.map (PowerSeries.rescale (-1 : R)) (normalizedTheta direction) =
        -normalizedTheta direction ∧
    PowerSeries.map PowerSeries.constantCoeff (normalizedTheta direction) = 0 ∧
    PowerSeries.mk (fun degree =>
        PowerSeries.coeff 1 (PowerSeries.coeff degree (normalizedTheta direction))) =
      -PowerSeries.C direction *
        PowerSeries.map (algebraMap ℚ R) (PowerSeries.pentagonalSeries ℚ) ^ 2 ∧
    (∀ degree cutoff : ℕ, degree < cutoff →
      PowerSeries.coeff degree (normalizedTheta direction) =
        PowerSeries.coeff degree
          (PowerSeries.C (PowerSeries.rescale
              (-direction * algebraMap ℚ R (1 / 2)) (PowerSeries.exp R)) *
            (1 - PowerSeries.C (PowerSeries.rescale direction (PowerSeries.exp R))) *
            ∏ index ∈ Finset.range cutoff,
              (1 - PowerSeries.X ^ (index + 1) *
                PowerSeries.C (PowerSeries.rescale direction (PowerSeries.exp R))) *
              (1 - PowerSeries.X ^ (index + 1) *
                PowerSeries.C (PowerSeries.rescale (-direction) (PowerSeries.exp R))))) := by
  classical
  let exponential (value : R) := PowerSeries.rescale value (PowerSeries.exp R)
  let q : PowerSeries ℚ := PowerSeries.X
  let qVariable : PowerSeries (PowerSeries R) := PowerSeries.X
  let scalarMap := PowerSeries.map (PowerSeries.C.comp (algebraMap ℚ R))
  let finite (value : R) (shift cutoff : ℕ) : PowerSeries (PowerSeries R) :=
    ∏ earlier ∈ Finset.range cutoff,
      (1 - qVariable ^ (earlier + shift) * PowerSeries.C (exponential value))
  let expansion (value : R) (shift : ℕ) : PowerSeries (PowerSeries R) :=
    PowerSeries.mk fun degree => ∑ index ∈ Finset.range (degree + 2),
      PowerSeries.C (algebraMap ℚ R
          (PowerSeries.coeff degree (q ^ (shift * index) * eulerCoefficients index))) *
        exponential (value * (index : R))
  let polynomial (cutoff : ℕ) : Polynomial (PowerSeries ℚ) :=
    ∏ earlier ∈ Finset.range cutoff,
      (1 - Polynomial.C (q ^ earlier) * Polynomial.X)
  have hexpMul (first second : R) :
      exponential first * exponential second = exponential (first + second) :=
    PowerSeries.exp_mul_exp_eq_exp_add first second
  have hexpConstant (value : R) : PowerSeries.constantCoeff (exponential value) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [exponential]
  have hexpFirst (value : R) : PowerSeries.coeff 1 (exponential value) = value := by
    simp [exponential]
  have hexpPow (value : R) (index : ℕ) :
      exponential value ^ index = exponential (value * (index : R)) := by
    induction index with
    | zero => simp [exponential, PowerSeries.rescale_zero]
    | succ index ih =>
        rw [pow_succ, ih, hexpMul]
        congr 1
        push_cast
        ring
  have hpolyStep (cutoff : ℕ) : polynomial (cutoff + 1) = polynomial cutoff *
      (1 - Polynomial.C (q ^ cutoff) * Polynomial.X) :=
    Finset.prod_range_succ _ cutoff
  have hpolyStable (base extra degree index : ℕ) (hsmall : degree < base) :
      PowerSeries.coeff degree ((polynomial (base + extra)).coeff index) =
        PowerSeries.coeff degree ((polynomial base).coeff index) := by
    induction extra with
    | zero => simp
    | succ extra ih =>
        rw [show base + (extra + 1) = base + extra + 1 by omega, hpolyStep]
        rw [mul_sub, mul_one, Polynomial.coeff_sub, map_sub]
        have hzero : PowerSeries.coeff degree
            ((polynomial (base + extra) *
              (Polynomial.C (q ^ (base + extra)) * Polynomial.X)).coeff index) = 0 := by
          rw [show polynomial (base + extra) *
              (Polynomial.C (q ^ (base + extra)) * Polynomial.X) =
                Polynomial.C (q ^ (base + extra)) *
                  (polynomial (base + extra) * Polynomial.X) by ring,
            Polynomial.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [hzero, sub_zero, ih]
  have hcolumn (degree cutoff index : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree ((polynomial cutoff).coeff index) =
        PowerSeries.coeff degree (eulerCoefficients index) := by
    rw [euler_coefficient_construction.2.2.2.1 index, PowerSeries.coeff_mk]
    rw [show cutoff = degree + 1 + (cutoff - (degree + 1)) by omega]
    exact hpolyStable (degree + 1) _ degree index (by omega)
  have hfiniteStable (value : R) (shift base extra degree : ℕ) (hsmall : degree < base) :
      PowerSeries.coeff degree (finite value shift (base + extra)) =
        PowerSeries.coeff degree (finite value shift base) := by
    induction extra with
    | zero => simp
    | succ extra ih =>
        rw [show base + (extra + 1) = base + extra + 1 by omega]
        change PowerSeries.coeff degree
          ((∏ earlier ∈ Finset.range (base + extra + 1), _) :
            PowerSeries (PowerSeries R)) = _
        rw [Finset.prod_range_succ, mul_sub, mul_one, map_sub]
        have hzero : PowerSeries.coeff degree
            (finite value shift (base + extra) *
              (qVariable ^ (base + extra + shift) * PowerSeries.C (exponential value))) =
                0 := by
          rw [show finite value shift (base + extra) *
              (qVariable ^ (base + extra + shift) * PowerSeries.C (exponential value)) =
                qVariable ^ (base + extra + shift) *
                  (finite value shift (base + extra) * PowerSeries.C (exponential value))
              by ring]
          rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        change PowerSeries.coeff degree (finite value shift (base + extra)) - _ = _
        rw [hzero, sub_zero, ih]
  have hfiniteCoeff (value : R) (shift degree cutoff : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree (finite value shift cutoff) =
        PowerSeries.coeff degree (expansion value shift) := by
    have hdegree : (polynomial (degree + 1)).natDegree < degree + 2 := by
      have hbound : (polynomial (degree + 1)).natDegree ≤ degree + 1 := by
        apply (Polynomial.natDegree_prod_le _ _).trans
        calc
          _ ≤ ∑ _earlier ∈ Finset.range (degree + 1), 1 := by
            apply Finset.sum_le_sum
            intro earlier _
            exact (Polynomial.natDegree_sub_le _ _).trans
              (by simpa using Polynomial.natDegree_C_mul_le (q ^ earlier) Polynomial.X)
          _ = degree + 1 := by simp
      omega
    have heval : finite value shift (degree + 1) =
        (polynomial (degree + 1)).eval₂ scalarMap
          (qVariable ^ shift * PowerSeries.C (exponential value)) := by
      dsimp only [finite, polynomial]
      rw [Polynomial.eval₂_finsetProd]
      apply Finset.prod_congr rfl
      intro earlier _
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X]
      have hq : scalarMap q = qVariable := by
        apply PowerSeries.ext
        intro index
        simp [scalarMap, q, qVariable]
      rw [map_pow, hq, ← mul_assoc, ← pow_add]
    rw [show cutoff = degree + 1 + (cutoff - (degree + 1)) by omega,
      hfiniteStable value shift (degree + 1) _ degree (by omega), heval,
      Polynomial.eval₂_eq_sum_range' scalarMap hdegree, map_sum]
    dsimp only [expansion]
    rw [PowerSeries.coeff_mk]
    apply Finset.sum_congr rfl
    intro index _
    rw [mul_pow, ← pow_mul, ← map_pow, hexpPow]
    rw [show scalarMap ((polynomial (degree + 1)).coeff index) *
        (qVariable ^ (shift * index) *
          PowerSeries.C (exponential (value * (index : R)))) =
          qVariable ^ (shift * index) *
            scalarMap ((polynomial (degree + 1)).coeff index) *
              PowerSeries.C (exponential (value * (index : R))) by ring]
    rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X_pow_mul']
    split_ifs with hle
    · simp only [scalarMap, PowerSeries.coeff_map, RingHom.coe_comp, Function.comp_apply]
      rw [hcolumn _ (degree + 1) index (by omega)]
    · simp
  have hraw (value : R) : normalizedTheta value =
      PowerSeries.C (exponential (-value * algebraMap ℚ R (1 / 2))) *
        (expansion value 0 * expansion (-value) 1) := by
    let character : Multiplicative ℤ →* PowerSeries R :=
      { toFun := fun index => exponential (value * (index.toAdd : R))
        map_one' := by simp [exponential, PowerSeries.rescale_zero]
        map_mul' := by
          intro first second
          change exponential (value * ((first.toAdd + second.toAdd : ℤ) : R)) = _
          rw [hexpMul]
          congr 1
          push_cast
          ring }
    let evaluate := AddMonoidAlgebra.liftNCRingHom
      (PowerSeries.C.comp (algebraMap ℚ R)) character (fun _ _ => Commute.all _ _)
    have hevaluate (coefficient : ℚ) (index : ℤ) :
        evaluate (LaurentPolynomial.C coefficient * LaurentPolynomial.T index) =
          PowerSeries.C (algebraMap ℚ R coefficient) *
            exponential (value * (index : R)) := by
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      exact AddMonoidAlgebra.liftNCRingHom_single _ _ _ _ _
    change PowerSeries.C (exponential (-value * algebraMap ℚ R (1 / 2))) *
      PowerSeries.map evaluate formalTheta = _
    congr 1
    rw [formalTheta, map_mul]
    congr 1
    · apply PowerSeries.ext
      intro degree
      simp only [PowerSeries.coeff_map, eulerLaurentExpansion, PowerSeries.coeff_mk,
        map_sum, hevaluate, expansion, Nat.zero_mul, pow_zero, one_mul, Int.cast_natCast]
    · apply PowerSeries.ext
      intro degree
      simp only [PowerSeries.coeff_map, shiftedEulerFactor, PowerSeries.coeff_mk,
        map_sum, expansion, Nat.one_mul]
      apply Finset.sum_congr rfl
      intro index _
      change evaluate (LaurentPolynomial.invert
        (LaurentPolynomial.C _ * LaurentPolynomial.T (index : ℤ))) = _
      rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T, hevaluate]
      simp only [Int.cast_neg, Int.cast_natCast, neg_mul, mul_neg, q]
  have hthetaCoeff (value : R) (degree cutoff : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree (normalizedTheta value) =
        PowerSeries.coeff degree
          (PowerSeries.C (exponential (-value * algebraMap ℚ R (1 / 2))) *
            (finite value 0 cutoff * finite (-value) 1 cutoff)) := by
    rw [hraw, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro split hsplit
    have hsplitSum := mem_antidiagonal.mp hsplit
    rw [hfiniteCoeff value 0 split.1 cutoff (by omega),
      hfiniteCoeff (-value) 1 split.2 cutoff (by omega)]
  have hshifted (value : R) (cutoff : ℕ) :
      finite value 0 (cutoff + 1) =
        (1 - PowerSeries.C (exponential value)) * finite value 1 cutoff := by
    dsimp only [finite]
    rw [Finset.prod_range_succ']
    simp only [Nat.add_zero, pow_zero, one_mul]
    rw [mul_comm]
  have hfiniteReflection (value : R) (cutoff : ℕ) :
      PowerSeries.C (exponential (value * algebraMap ℚ R (1 / 2))) *
          (finite (-value) 0 (cutoff + 1) * finite value 1 cutoff) =
        -(PowerSeries.C (exponential (-value * algebraMap ℚ R (1 / 2))) *
          (finite value 0 (cutoff + 1) * finite (-value) 1 cutoff)) := by
    have hequal : exponential (value * algebraMap ℚ R (1 / 2)) *
        (1 - exponential (-value)) =
          -(exponential (-value * algebraMap ℚ R (1 / 2)) *
            (1 - exponential value)) := by
      rw [mul_sub, mul_one, hexpMul, mul_sub, mul_one, hexpMul]
      have hhalf : value * algebraMap ℚ R (1 / 2) + -value =
          -value * algebraMap ℚ R (1 / 2) := by
        have htwo : (2 : R) * algebraMap ℚ R (1 / 2) = 1 := by
          have heq := congrArg (algebraMap ℚ R) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)
          simpa only [map_mul, map_ofNat, map_one] using heq
        linear_combination value * htwo
      rw [hhalf, show -value * algebraMap ℚ R (1 / 2) + value =
          value * algebraMap ℚ R (1 / 2) by linear_combination -hhalf]
      ring
    rw [hshifted, hshifted]
    have hC := congrArg (PowerSeries.C (R := PowerSeries R)) hequal
    simp only [map_mul, map_sub, map_one, map_neg] at hC
    linear_combination hC * finite (-value) 1 cutoff * finite value 1 cutoff
  have hodd : normalizedTheta (-direction) = -normalizedTheta direction := by
    apply PowerSeries.ext
    intro degree
    rw [map_neg, hthetaCoeff (-direction) degree (degree + 2) (by omega),
      hthetaCoeff direction degree (degree + 2) (by omega)]
    have hreplace (value other : R) :
        PowerSeries.coeff degree
            (PowerSeries.C (exponential value) *
              (finite other 0 (degree + 2) * finite (-other) 1 (degree + 2))) =
          PowerSeries.coeff degree
            (PowerSeries.C (exponential value) *
              (finite other 0 (degree + 2) * finite (-other) 1 (degree + 1))) := by
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro split hsplit
      have hsum := mem_antidiagonal.mp hsplit
      rw [show degree + 2 = degree + 1 + 1 by omega,
        hfiniteStable (-other) 1 (degree + 1) 1 split.2 (by omega)]
    simp only [neg_neg]
    have hnegative := hreplace (direction * algebraMap ℚ R (1 / 2)) (-direction)
    simp only [neg_neg] at hnegative
    rw [hnegative, hreplace (-direction * algebraMap ℚ R (1 / 2)) direction]
    simpa only [map_neg] using congrArg (PowerSeries.coeff degree)
      (hfiniteReflection direction (degree + 1))
  have hconstant : PowerSeries.map PowerSeries.constantCoeff
      (normalizedTheta direction) = 0 := by
    apply PowerSeries.ext
    intro degree
    rw [PowerSeries.coeff_map, hthetaCoeff direction degree (degree + 2) (by omega)]
    rw [hshifted direction (degree + 1)]
    have hzero : PowerSeries.map PowerSeries.constantCoeff
        (PowerSeries.C (exponential (-direction * algebraMap ℚ R (1 / 2))) *
          ((1 - PowerSeries.C (exponential direction)) *
            finite direction 1 (degree + 1) * finite (-direction) 1 (degree + 2))) = 0 := by
      simp [map_mul, map_sub, hexpConstant]
    have hcoeff := congrArg (PowerSeries.coeff degree) hzero
    simpa only [PowerSeries.coeff_map, map_zero, mul_assoc] using hcoeff
  have hscale (value : R) :
      PowerSeries.rescale (-1 : R) (exponential value) = exponential (-value) := by
    change ((PowerSeries.rescale (-1 : R)).comp (PowerSeries.rescale value))
      (PowerSeries.exp R) = _
    rw [← PowerSeries.rescale_mul]
    simp only [mul_neg_one]
    rfl
  have hscaleExpansion (value : R) (shift : ℕ) :
      PowerSeries.map (PowerSeries.rescale (-1 : R)) (expansion value shift) =
        expansion (-value) shift := by
    apply PowerSeries.ext
    intro degree
    simp [expansion, map_sum, map_mul, hscale, neg_mul]
  have hscaleTheta :
      PowerSeries.map (PowerSeries.rescale (-1 : R)) (normalizedTheta direction) =
        normalizedTheta (-direction) := by
    rw [hraw, map_mul, PowerSeries.map_C, hscale, map_mul,
      hscaleExpansion, hscaleExpansion, hraw]
    simp only [neg_neg, neg_mul]
  let first (series : PowerSeries (PowerSeries R)) : PowerSeries R :=
    PowerSeries.mk fun degree => PowerSeries.coeff 1 (PowerSeries.coeff degree series)
  let constant := PowerSeries.map (PowerSeries.constantCoeff (R := R))
  have hfirstMul (left right : PowerSeries (PowerSeries R)) :
      first (left * right) = first left * constant right + constant left * first right := by
    apply PowerSeries.ext
    intro degree
    conv_lhs => dsimp only [first]; rw [PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_mul, map_sum]
    simp_rw [PowerSeries.coeff_one_mul]
    rw [map_add]
    conv_rhs => rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    simp only [first, constant, PowerSeries.coeff_mk, PowerSeries.coeff_map]
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro split _
    ring
  have hconstantFinite (value : R) (cutoff : ℕ) :
      constant (finite value 1 cutoff) =
        PowerSeries.map (algebraMap ℚ R) (eulerDenominator cutoff) := by
    simp [constant, finite, eulerDenominator, map_prod, map_sub, map_pow,
      qVariable, hexpConstant]
  have hnormalizedFinite (degree cutoff : ℕ) (hlarge : degree < cutoff) :
      PowerSeries.coeff degree (normalizedTheta direction) =
        PowerSeries.coeff degree
          (PowerSeries.C (exponential (-direction * algebraMap ℚ R (1 / 2))) *
            ((1 - PowerSeries.C (exponential direction)) *
              (finite direction 1 cutoff * finite (-direction) 1 cutoff))) := by
    rw [hthetaCoeff direction degree (cutoff + 1) (by omega), hshifted]
    rw [show (1 - PowerSeries.C (exponential direction)) * finite direction 1 cutoff *
        finite (-direction) 1 (cutoff + 1) =
          (1 - PowerSeries.C (exponential direction)) *
            (finite direction 1 cutoff * finite (-direction) 1 (cutoff + 1)) by ring]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    congr 1
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro split hsplit
    have hsum := mem_antidiagonal.mp hsplit
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro smaller hsmaller
    have hsmallSum := mem_antidiagonal.mp hsmaller
    rw [hfiniteStable (-direction) 1 cutoff 1 smaller.2 (by omega)]
  have hlinearFinite (cutoff : ℕ) :
      first (PowerSeries.C (exponential (-direction * algebraMap ℚ R (1 / 2))) *
        ((1 - PowerSeries.C (exponential direction)) *
          (finite direction 1 cutoff * finite (-direction) 1 cutoff))) =
        -PowerSeries.C direction *
          PowerSeries.map (algebraMap ℚ R) (eulerDenominator cutoff) ^ 2 := by
    have hfirstSub : first (1 - PowerSeries.C (exponential direction)) =
        -PowerSeries.C direction := by
      apply PowerSeries.ext
      intro degree
      by_cases hzero : degree = 0
      · subst degree
        simp [first, hexpFirst]
      · simp [first, PowerSeries.coeff_C, hzero]
    have hzero : constant (1 - PowerSeries.C (exponential direction)) = 0 := by
      simp [constant, hexpConstant]
    have hone : constant
        (PowerSeries.C (exponential (-direction * algebraMap ℚ R (1 / 2)))) = 1 := by
      simp [constant, hexpConstant]
    rw [hfirstMul, hfirstMul, hfirstSub, hzero, zero_mul, add_zero, hone, one_mul]
    simp only [map_mul, hzero, zero_mul, mul_zero, zero_add,
      hconstantFinite, pow_two]
  let : UniformSpace ℚ := ⊥
  let : DiscreteUniformity ℚ := ⟨rfl⟩
  have hlimit : Filter.Tendsto (fun cutoff => eulerDenominator cutoff ^ 2)
      Filter.atTop (nhds (PowerSeries.pentagonalSeries ℚ ^ 2)) :=
    ((PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℚ).tendsto_prod_nat).pow 2
  refine ⟨hscaleTheta.trans hodd, hconstant, ?_, ?_⟩
  swap
  · intro degree cutoff hlarge
    rw [hnormalizedFinite degree cutoff hlarge]
    dsimp only [finite, exponential, qVariable]
    rw [← Finset.prod_mul_distrib]
    congr 1
    ring
  apply PowerSeries.ext
  intro degree
  have heventually : ∀ᶠ cutoff : ℕ in Filter.atTop,
      PowerSeries.coeff degree (eulerDenominator cutoff ^ 2) =
        PowerSeries.coeff degree (PowerSeries.pentagonalSeries ℚ ^ 2) := by
    have hcoeff := (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℚ _ _ _).mp
      hlimit degree
    simpa only [nhds_discrete, Filter.tendsto_pure] using hcoeff
  obtain ⟨cutoff, hlarge, hequal⟩ :=
    Filter.Eventually.exists ((Filter.eventually_gt_atTop degree).and heventually)
  rw [PowerSeries.coeff_mk, hnormalizedFinite degree cutoff hlarge]
  have hlinear := congrArg (PowerSeries.coeff degree) (hlinearFinite cutoff)
  simp only [first, PowerSeries.coeff_mk] at hlinear
  rw [hlinear]
  simp only [neg_mul, map_neg, PowerSeries.coeff_C_mul, ← map_pow,
    PowerSeries.coeff_map, hequal]


end D5.S3.Combinatorics.InversionSeq.InversionSeq207ThetaNormalization
