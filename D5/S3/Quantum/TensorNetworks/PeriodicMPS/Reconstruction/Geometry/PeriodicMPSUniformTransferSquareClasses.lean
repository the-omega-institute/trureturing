/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferSquareClasses
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferSquareClasses
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Square-class independence in the periodic MPS transfer chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformTransferRadicals
import Mathlib.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Square-class independence in the periodic MPS transfer chart

The two copies of `RatFunc` supply independent indeterminates `k` and `U`.
The coefficients may lie in any field of characteristic different from two.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTransferRadicals

open Polynomial

variable {K : Type*} [Field K]

/-- The fraction field of the two independent chart parameters. -/
abbrev ChartFunctionField (K : Type*) [Field K] := RatFunc (RatFunc K)

/-- The archived first discriminant with the generic chart parameters. -/
def genericDeltaD (a b : K) : ChartFunctionField K :=
  deltaD (RatFunc.C (RatFunc.C a)) (RatFunc.C (RatFunc.C b)) RatFunc.X
    (RatFunc.C RatFunc.X)

/-- The archived second discriminant with the generic chart parameters. -/
def genericDeltaS (b c : K) : ChartFunctionField K :=
  deltaS (RatFunc.C (RatFunc.C b)) (RatFunc.C (RatFunc.C c)) RatFunc.X
    (RatFunc.C RatFunc.X)

private def shiftD (a b : K) : RatFunc K :=
  RatFunc.C (a - 2 * b) + RatFunc.X ^ 2

private def scaledH (b c : K) : RatFunc K :=
  RatFunc.C (c - b ^ 2) / RatFunc.X ^ 2

private def polyD (a b : K) : Polynomial (RatFunc K) :=
  C 16 * X ^ 2 + (C (8 * shiftD a b - 4) * X + C (shiftD a b ^ 2))

private def polyS (b c : K) : Polynomial (RatFunc K) :=
  C (-4 * scaledH b c) * X + C ((scaledH b c + RatFunc.C b) ^ 2)

private theorem map_polyD (a b : K) :
    algebraMap (Polynomial (RatFunc K)) (ChartFunctionField K) (polyD a b) =
      genericDeltaD a b := by
  simp [polyD, shiftD, genericDeltaD, deltaD, sumD, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X, map_ofNat]
  ring

private theorem map_polyS (b c : K) :
    algebraMap (Polynomial (RatFunc K)) (ChartFunctionField K) (polyS b c) =
      genericDeltaS b c := by
  simp [polyS, scaledH, genericDeltaS, deltaS, sumScaledE, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X, map_ofNat]
  ring

private theorem two_ne_zero_ratFunc (h₂ : (2 : K) ≠ 0) : (2 : RatFunc K) ≠ 0 := by
  simpa only [map_ofNat, map_zero] using (RatFunc.C_injective (K := K)).ne h₂

private theorem four_ne_zero_of_two {F : Type*} [Field F] (h₂ : (2 : F) ≠ 0) :
    (4 : F) ≠ 0 := by
  simpa only [show (2 : F) ^ 2 = 4 by norm_num] using pow_ne_zero 2 h₂

private theorem sixteen_ne_zero_of_two {F : Type*} [Field F] (h₂ : (2 : F) ≠ 0) :
    (16 : F) ≠ 0 := by
  simpa only [show (2 : F) ^ 4 = 16 by norm_num] using pow_ne_zero 4 h₂

private theorem one_sub_four_shiftD_ne_zero (a b : K) (h₂ : (2 : K) ≠ 0) :
    1 - 4 * shiftD a b ≠ 0 := by
  let p : Polynomial K := C (1 - 4 * (a - 2 * b)) - C 4 * X ^ 2
  have hcoeff : p.coeff 2 = -4 := by
    simp only [p, coeff_sub, coeff_C, coeff_C_mul_X_pow]
    norm_num
  have hp : p ≠ 0 := by
    intro hz
    rw [hz, coeff_zero] at hcoeff
    exact (neg_ne_zero.mpr (four_ne_zero_of_two h₂)) hcoeff.symm
  have heq : algebraMap (Polynomial K) (RatFunc K) p = 1 - 4 * shiftD a b := by
    simp [p, shiftD, RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_ofNat]
    ring
  rw [← heq]
  exact RatFunc.algebraMap_ne_zero hp

private theorem natDegree_polyD (a b : K) (h₂ : (2 : RatFunc K) ≠ 0) :
    (polyD a b).natDegree = 2 := by
  unfold polyD
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_C_mul_X_pow _ _ (sixteen_ne_zero_of_two h₂)]
  rw [natDegree_C_mul_X_pow _ _ (sixteen_ne_zero_of_two h₂)]
  exact lt_of_le_of_lt natDegree_linear_le (by decide)

private theorem natDegree_polyS (b c : K) (h₂ : (2 : RatFunc K) ≠ 0)
    (h : c - b ^ 2 ≠ 0) : (polyS b c).natDegree = 1 := by
  have hH : scaledH b c ≠ 0 :=
    div_ne_zero (by simpa only [map_zero] using (RatFunc.C_injective (K := K)).ne h)
      (pow_ne_zero 2 RatFunc.X_ne_zero)
  apply natDegree_linear
  exact mul_ne_zero (neg_ne_zero.mpr (four_ne_zero_of_two h₂)) hH

private theorem discr_polyD (a b : K) (hd : (polyD a b).natDegree = 2) :
    (polyD a b).discr = 16 * (1 - 4 * shiftD a b) := by
  rw [discr_of_degree_eq_two (by
    exact (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 2)).mpr hd)]
  simp only [polyD, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num
  ring

private theorem squarefree_polyD (a b : K) (h₂ : (2 : K) ≠ 0) :
    Squarefree (polyD a b) := by
  have h₂k := two_ne_zero_ratFunc h₂
  let p := polyD a b
  have hd : p.natDegree = 2 := natDegree_polyD a b h₂k
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hd
  have hderiv : p.derivative.natDegree = 1 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · simpa [hd] using natDegree_derivative_le p
    · have hcoeff : p.derivative.coeff 1 = 2 * 16 := by
        simp only [p, polyD, coeff_derivative, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X,
          coeff_C]
        norm_num
      rw [hcoeff]
      exact mul_ne_zero h₂k (sixteen_ne_zero_of_two h₂k)
  have hdiscr : p.discr ≠ 0 :=
    discr_polyD a b hd ▸
      mul_ne_zero (sixteen_ne_zero_of_two h₂k) (one_sub_four_shiftD_ne_zero a b h₂)
  have hresultant : p.resultant p.derivative ≠ 0 := by
    have hd' : p.derivative.natDegree = p.natDegree - 1 := by simp [hd, hderiv]
    rw [hd', resultant_deriv (natDegree_pos_iff_degree_pos.mp (by simp [hd]))]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (leadingCoeff_ne_zero.mpr hp)) hdiscr
  have hsep : p.Separable := by
    by_contra h
    exact hresultant (resultant_eq_zero_iff.mpr ⟨Or.inl hp, h⟩)
  exact hsep.squarefree

private theorem not_isSquare_map_of_squarefree {F : Type*} [Field F] {p : Polynomial F}
    (hp : Squarefree p) (hdeg : 0 < p.natDegree) :
    ¬ IsSquare (algebraMap (Polynomial F) (RatFunc F) p) := by
  intro h
  obtain ⟨r, hr⟩ := h.exists_sq
  have hi : IsIntegral (Polynomial F) (r ^ 2) := by
    rw [← hr]
    exact isIntegral_algebraMap
  obtain ⟨q, hq⟩ :=
    IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by decide : 0 < 2) hi
  have he : p = q * q := by
    apply RatFunc.algebraMap_injective F
    rw [map_mul, hq, ← pow_two, ← hr]
  have hq_unit : IsUnit q := hp q ⟨1, by rw [mul_one, he]⟩
  exact not_isUnit_of_natDegree_pos p hdeg (he.symm ▸ hq_unit.mul hq_unit)

private theorem not_isSquare_map_of_odd_natDegree {F : Type*} [Field F] {p : Polynomial F}
    (hp : p ≠ 0) (hdeg : Odd p.natDegree) :
    ¬ IsSquare (algebraMap (Polynomial F) (RatFunc F) p) := by
  rintro ⟨z, hz⟩
  have hz₀ : z ≠ 0 := by
    intro hz₀
    exact RatFunc.algebraMap_ne_zero hp (by simpa [hz₀] using hz)
  have hdeg' := congrArg RatFunc.intDegree hz
  rw [RatFunc.intDegree_polynomial, RatFunc.intDegree_mul hz₀ hz₀] at hdeg'
  obtain ⟨n, hn⟩ := hdeg
  omega

/-- The first discriminant is nonsquare for every choice of the spectral coefficients. -/
theorem genericDeltaD_not_isSquare (a b : K) (h₂ : (2 : K) ≠ 0) :
    ¬ IsSquare (genericDeltaD a b) := by
  have h₂k := two_ne_zero_ratFunc h₂
  rw [← map_polyD]
  exact not_isSquare_map_of_squarefree (squarefree_polyD a b h₂)
    (by rw [natDegree_polyD a b h₂k]; decide)

/-- All three nontrivial products of the two discriminant square classes are nonsquare. -/
theorem genericDiscriminants_squareClassIndependent (a b c : K) (h₂ : (2 : K) ≠ 0)
    (h : c - b ^ 2 ≠ 0) :
    ¬ IsSquare (genericDeltaD a b) ∧ ¬ IsSquare (genericDeltaS b c) ∧
      ¬ IsSquare (genericDeltaD a b * genericDeltaS b c) := by
  have h₂k := two_ne_zero_ratFunc h₂
  have hd := natDegree_polyD a b h₂k
  have hs := natDegree_polyS b c h₂k h
  have hd₀ : polyD a b ≠ 0 := by
    intro hz
    simp [hz] at hd
  have hs₀ : polyS b c ≠ 0 := by
    intro hz
    simp [hz] at hs
  refine ⟨genericDeltaD_not_isSquare a b h₂, ?_, ?_⟩
  · rw [← map_polyS]
    exact not_isSquare_map_of_odd_natDegree hs₀ (by rw [hs]; decide)
  · rw [← map_polyD, ← map_polyS, ← map_mul]
    apply not_isSquare_map_of_odd_natDegree (mul_ne_zero hd₀ hs₀)
    rw [natDegree_mul hd₀ hs₀, hd, hs]
    decide

private theorem not_isSquare_in_quadraticAlgebra {F : Type*} [Field F]
    {d s : F} (h₂ : (2 : F) ≠ 0) (hs : ¬ IsSquare s) (hds : ¬ IsSquare (d * s)) :
    ¬ IsSquare (algebraMap F (QuadraticAlgebra F d 0) s) := by
  rintro ⟨z, hz⟩
  have hre : s = z.re * z.re + d * (z.im * z.im) := by
    simpa only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_mul, mul_assoc] using
      congrArg QuadraticAlgebra.re hz
  have him : (2 : F) * (z.re * z.im) = 0 := by
    have hh := congrArg QuadraticAlgebra.im hz
    simp only [QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.im_mul, zero_mul, add_zero] at hh
    linear_combination -hh
  rcases mul_eq_zero.mp ((mul_eq_zero.mp him).resolve_left h₂) with hr | hi
  · apply hds
    refine ⟨d * z.im, ?_⟩
    rw [hre, hr]
    ring
  · exact hs ⟨z.re, by simpa [hi] using hre⟩

/-- Adjoin the first square root to the generic chart function field. -/
abbrev GenericDAlgebra (a b : K) :=
  QuadraticAlgebra (ChartFunctionField K) (genericDeltaD a b) 0

/-- The first quadratic algebra is a field for every choice of `a` and `b`. -/
theorem genericDAlgebra_isField (a b : K) (h₂ : (2 : K) ≠ 0) :
    IsField (GenericDAlgebra a b) := by
  let : Fact (¬ IsSquare (genericDeltaD a b)) := ⟨genericDeltaD_not_isSquare a b h₂⟩
  exact Field.toIsField (GenericDAlgebra a b)

/-- Adjoin the second square root over the first quadratic algebra. -/
abbrev GenericRadicalAlgebra (a b c : K) :=
  QuadraticAlgebra (GenericDAlgebra a b)
    (algebraMap (ChartFunctionField K) (GenericDAlgebra a b) (genericDeltaS b c)) 0

/-- The second discriminant remains nonsquare after adjoining the first root. -/
theorem genericDeltaS_not_isSquare_in_GenericDAlgebra (a b c : K) (h₂ : (2 : K) ≠ 0)
    (h : c - b ^ 2 ≠ 0) :
    ¬ IsSquare (algebraMap (ChartFunctionField K) (GenericDAlgebra a b)
      (genericDeltaS b c)) := by
  have h₂k := two_ne_zero_ratFunc h₂
  have h₂U := two_ne_zero_ratFunc h₂k
  obtain ⟨_, hs, hds⟩ := genericDiscriminants_squareClassIndependent a b c h₂ h
  exact not_isSquare_in_quadraticAlgebra h₂U hs hds

/-- The generic two-radical chart algebra is a field. -/
theorem genericRadicalAlgebra_isField (a b c : K) (h₂ : (2 : K) ≠ 0)
    (h : c - b ^ 2 ≠ 0) : IsField (GenericRadicalAlgebra a b c) := by
  let : Fact (¬ IsSquare (genericDeltaD a b)) := ⟨genericDeltaD_not_isSquare a b h₂⟩
  let : Fact (¬ IsSquare (algebraMap (ChartFunctionField K) (GenericDAlgebra a b)
    (genericDeltaS b c))) := ⟨genericDeltaS_not_isSquare_in_GenericDAlgebra a b c h₂ h⟩
  exact Field.toIsField (GenericRadicalAlgebra a b c)

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTransferRadicals
