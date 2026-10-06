/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Euler
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Euler
   mirror-E: none(waiver:formal-euler-coefficient-recursion)
   anchors: [mathlib/module/Mathlib.Combinatorics.Young.YoungDiagram]
   utility: none
   digest: Coefficient recursion constructs the normalized formal Euler solution. -/

import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiHeine
import Mathlib.Combinatorics.Young.YoungDiagram

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Euler

open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def eulerDenominator (index : ℕ) : PowerSeries ℚ :=
  ∏ earlier ∈ Finset.range index, (1 - PowerSeries.X ^ (earlier + 1))

noncomputable def eulerCoefficients (index : ℕ) : PowerSeries ℚ :=
  PowerSeries.C ((-1 : ℚ) ^ index) * PowerSeries.X ^ (index.choose 2) *
    PowerSeries.invOfUnit (eulerDenominator index) 1

noncomputable def eulerLaurentExpansion : PowerSeries (LaurentPolynomial ℚ) :=
  PowerSeries.mk fun degree =>
    ∑ index ∈ Finset.range (degree + 2),
      LaurentPolynomial.C (PowerSeries.coeff degree (eulerCoefficients index)) *
        LaurentPolynomial.T (index : ℤ)

theorem euler_coefficient_construction :
    (let series := PowerSeries.mk eulerCoefficients
     let q : PowerSeries ℚ := PowerSeries.X
     PowerSeries.constantCoeff series = 1 ∧
       series = (1 - PowerSeries.X) * PowerSeries.rescale q series) ∧
    (∀ candidate : PowerSeries (PowerSeries ℚ),
      PowerSeries.constantCoeff candidate = 1 →
      candidate = (1 - PowerSeries.X) *
        PowerSeries.rescale (PowerSeries.X : PowerSeries ℚ) candidate →
      candidate = PowerSeries.mk eulerCoefficients) ∧
    (∀ degree index : ℕ, degree < index.choose 2 →
      PowerSeries.coeff degree (eulerCoefficients index) = 0) ∧
    (∀ index : ℕ, eulerCoefficients index = PowerSeries.mk fun degree =>
      PowerSeries.coeff degree
        ((∏ earlier ∈ Finset.range (degree + 1),
          (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℚ) ^ earlier) *
            Polynomial.X)).coeff index)) ∧
    (letI : UniformSpace (LaurentPolynomial ℚ) := ⊥
     letI : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
     HasSum (fun index : ℕ =>
       PowerSeries.map LaurentPolynomial.C (eulerCoefficients index) *
         PowerSeries.C (LaurentPolynomial.T (index : ℤ))) eulerLaurentExpansion) := by
  classical
  have hdenominator (index : ℕ) :
      PowerSeries.constantCoeff (eulerDenominator index) = 1 := by
    simp [eulerDenominator, map_prod]
  have hinverse (index : ℕ) :
      eulerDenominator index * PowerSeries.invOfUnit (eulerDenominator index) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (hdenominator index)
  have hdenominatorStep (index : ℕ) :
      eulerDenominator (index + 1) =
        eulerDenominator index * (1 - PowerSeries.X ^ (index + 1)) := by
    exact Finset.prod_range_succ _ index
  have hinverseStep (index : ℕ) :
      (1 - PowerSeries.X ^ (index + 1)) *
        PowerSeries.invOfUnit (eulerDenominator (index + 1)) 1 =
          PowerSeries.invOfUnit (eulerDenominator index) 1 := by
    apply mul_left_cancel₀ (show eulerDenominator index ≠ 0 by
      intro hzero
      have hconstant := hdenominator index
      rw [hzero, map_zero] at hconstant
      exact zero_ne_one hconstant)
    rw [← mul_assoc, ← hdenominatorStep, hinverse, hinverse]
  have hzero : eulerCoefficients 0 = 1 := by
    have hunit : PowerSeries.invOfUnit (1 : PowerSeries ℚ) 1 = 1 := by
      simpa using PowerSeries.mul_invOfUnit (1 : PowerSeries ℚ) 1 (by simp)
    simp [eulerCoefficients, eulerDenominator, hunit]
  have hstep (index : ℕ) :
      (1 - PowerSeries.X ^ (index + 1)) * eulerCoefficients (index + 1) =
        -(PowerSeries.X ^ index * eulerCoefficients index) := by
    have hchoose : (index + 1).choose 2 = index + index.choose 2 := by
      simpa using Nat.choose_succ_succ index 1
    unfold eulerCoefficients
    rw [hchoose, pow_add, pow_succ (-1 : ℚ), mul_neg_one, map_neg]
    calc
      _ = -(PowerSeries.C ((-1 : ℚ) ^ index) *
          (PowerSeries.X ^ index * PowerSeries.X ^ index.choose 2) *
          ((1 - PowerSeries.X ^ (index + 1)) *
            PowerSeries.invOfUnit (eulerDenominator (index + 1)) 1)) := by ring
      _ = _ := by rw [hinverseStep]; ring
  have hsupport (degree index : ℕ) (hsmall : degree < index.choose 2) :
      PowerSeries.coeff degree (eulerCoefficients index) = 0 := by
    rw [eulerCoefficients, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]
  have hseries :
      PowerSeries.mk eulerCoefficients = (1 - PowerSeries.X) *
        PowerSeries.rescale (PowerSeries.X : PowerSeries ℚ)
          (PowerSeries.mk eulerCoefficients) := by
    apply PowerSeries.ext
    intro index
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_rescale]
    cases index with
    | zero => simp [PowerSeries.coeff_mk]
    | succ index =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_rescale]
        simp only [PowerSeries.coeff_mk]
        have hrec := hstep index
        linear_combination hrec
  have hfiniteProducts (index : ℕ) :
      eulerCoefficients index = PowerSeries.mk fun degree =>
        PowerSeries.coeff degree
          ((∏ earlier ∈ Finset.range (degree + 1),
            (1 - Polynomial.C ((PowerSeries.X : PowerSeries ℚ) ^ earlier) *
              Polynomial.X)).coeff index) := by
    let finiteProduct (cutoff : ℕ) : Polynomial (PowerSeries ℚ) :=
      ∏ earlier ∈ Finset.range cutoff,
        (1 - Polynomial.C (PowerSeries.X ^ earlier) * Polynomial.X)
    let column (index : ℕ) : PowerSeries ℚ :=
      PowerSeries.mk fun degree =>
        PowerSeries.coeff degree ((finiteProduct (degree + 1)).coeff index)
    have hpartialStep (cutoff : ℕ) : finiteProduct (cutoff + 1) = finiteProduct cutoff *
        (1 - Polynomial.C (PowerSeries.X ^ cutoff) * Polynomial.X) :=
      Finset.prod_range_succ _ cutoff
    have hstable (base extra degree index : ℕ) (hsmall : degree < base) :
        PowerSeries.coeff degree ((finiteProduct (base + extra)).coeff index) =
          PowerSeries.coeff degree ((finiteProduct base).coeff index) := by
      induction extra with
      | zero => simp
      | succ extra ih =>
          rw [show base + (extra + 1) = base + extra + 1 by omega, hpartialStep]
          rw [mul_sub, mul_one, Polynomial.coeff_sub, map_sub]
          have hterm : PowerSeries.coeff degree
              ((finiteProduct (base + extra) *
                (Polynomial.C (PowerSeries.X ^ (base + extra)) * Polynomial.X)).coeff
                  index) = 0 := by
            rw [show finiteProduct (base + extra) *
                (Polynomial.C (PowerSeries.X ^ (base + extra)) * Polynomial.X) =
                  Polynomial.C (PowerSeries.X ^ (base + extra)) *
                    (finiteProduct (base + extra) * Polynomial.X) by ring,
              Polynomial.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
          rw [hterm, sub_zero, ih]
    have hcolumn (degree cutoff index : ℕ) (hlarge : degree < cutoff) :
        PowerSeries.coeff degree ((finiteProduct cutoff).coeff index) =
          PowerSeries.coeff degree (column index) := by
      dsimp only [column]
      rw [PowerSeries.coeff_mk]
      have hcutoff : cutoff = degree + 1 + (cutoff - (degree + 1)) := by omega
      rw [hcutoff]
      exact hstable (degree + 1) _ degree index (by omega)
    have hshift (degree cutoff power index : ℕ) (hlarge : degree < cutoff) :
        PowerSeries.coeff degree
          (PowerSeries.X ^ power * (finiteProduct cutoff).coeff index) =
            PowerSeries.coeff degree (PowerSeries.X ^ power * column index) := by
      rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
      split_ifs
      · exact hcolumn _ _ _ (by omega)
      · rfl
    have hpartialShift (cutoff : ℕ) : finiteProduct (cutoff + 1) =
        (1 - Polynomial.X) * (finiteProduct cutoff).comp
          (Polynomial.C (PowerSeries.X : PowerSeries ℚ) * Polynomial.X) := by
      dsimp only [finiteProduct]
      rw [Finset.prod_range_succ']
      simp only [pow_zero, Polynomial.C_1, one_mul]
      rw [mul_comm]
      congr 1
      rw [Polynomial.prod_comp]
      apply Finset.prod_congr rfl
      intro earlier _hearlier
      simp only [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp,
        Polynomial.C_comp, Polynomial.X_comp]
      rw [pow_succ, map_mul]
      ring
    have hrec (index : ℕ) : column (index + 1) =
        PowerSeries.X ^ (index + 1) * column (index + 1) -
          PowerSeries.X ^ index * column index := by
      apply PowerSeries.ext
      intro degree
      have hfinite := congrArg (fun polynomial : Polynomial (PowerSeries ℚ) =>
        PowerSeries.coeff degree (polynomial.coeff (index + 1)))
          (hpartialShift (degree + 1))
      rw [sub_mul, one_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
        Polynomial.comp_C_mul_X_coeff, Polynomial.comp_C_mul_X_coeff,
        mul_comm ((finiteProduct (degree + 1)).coeff (index + 1)),
        mul_comm ((finiteProduct (degree + 1)).coeff index), map_sub,
        hcolumn degree (degree + 1 + 1) (index + 1) (by omega),
        hshift degree (degree + 1) (index + 1) (index + 1) (by omega),
        hshift degree (degree + 1) index index (by omega)] at hfinite
      simpa only [map_sub] using hfinite
    have hcolumnZero : column 0 = 1 := by
      apply PowerSeries.ext
      intro degree
      simp [column, finiteProduct, Polynomial.coeff_zero_prod]
    have hidentification : ∀ index : ℕ, column index = eulerCoefficients index := by
      intro index
      induction index with
      | zero => rw [hcolumnZero, hzero]
      | succ index ih =>
          have hactual := hstep index
          have hproduct := hrec index
          rw [ih] at hproduct
          have hnonzero : 1 - (PowerSeries.X : PowerSeries ℚ) ^ (index + 1) ≠ 0 := by
            intro hzeroFactor
            have hconstantFactor := congrArg PowerSeries.constantCoeff hzeroFactor
            simp at hconstantFactor
          apply mul_left_cancel₀ hnonzero
          linear_combination hproduct - hactual
    exact (hidentification index).symm
  refine ⟨⟨?_, hseries⟩, ?_, hsupport, hfiniteProducts, ?_⟩
  · exact hzero
  · intro candidate hconstant hequation
    have hcoeff (index : ℕ) : PowerSeries.coeff index candidate =
        eulerCoefficients index := by
      induction index with
      | zero =>
          simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hzero] using hconstant
      | succ index ih =>
          have hrec := congrArg (PowerSeries.coeff (index + 1)) hequation
          rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul,
            PowerSeries.coeff_rescale, PowerSeries.coeff_rescale, ih] at hrec
          have hunit : 1 - (PowerSeries.X : PowerSeries ℚ) ^ (index + 1) ≠ 0 := by
            intro hzeroFactor
            have hconstantFactor := congrArg PowerSeries.constantCoeff hzeroFactor
            simp at hconstantFactor
          apply mul_left_cancel₀ hunit
          have hactual := hstep index
          linear_combination hrec - hactual
    apply PowerSeries.ext
    intro index
    simpa only [PowerSeries.coeff_mk] using hcoeff index
  · let : UniformSpace (LaurentPolynomial ℚ) := ⊥
    let : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
    apply (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff
      (LaurentPolynomial ℚ)).mpr
    intro degree
    have hbound (index : ℕ) : index - 1 ≤ index.choose 2 := by
      induction index with
      | zero => simp
      | succ index ih =>
          rw [show (index + 1).choose 2 = index + index.choose 2 by
            simpa using Nat.choose_succ_succ index 1]
          omega
    have hfinite : HasSum (fun index : ℕ =>
        LaurentPolynomial.C (PowerSeries.coeff degree (eulerCoefficients index)) *
          LaurentPolynomial.T (index : ℤ))
        (∑ index ∈ Finset.range (degree + 2),
          LaurentPolynomial.C (PowerSeries.coeff degree (eulerCoefficients index)) *
            LaurentPolynomial.T (index : ℤ)) := by
      apply hasSum_sum_of_ne_finset_zero
      intro index houtside
      have hlarge : degree + 2 ≤ index := by simpa using houtside
      rw [hsupport degree index (by have := hbound index; omega), map_zero, zero_mul]
    simpa only [PowerSeries.coeff_mul_C, PowerSeries.coeff_map,
      eulerLaurentExpansion, PowerSeries.coeff_mk] using hfinite

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Euler
