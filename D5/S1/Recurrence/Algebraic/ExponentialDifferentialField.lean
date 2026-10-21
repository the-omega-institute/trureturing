/- GID: D5/S1/Recurrence/Algebraic/ExponentialDifferentialField
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/ExponentialDifferentialField
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.FieldTheory.RatFunc.AsPolynomial, mathlib/module/Mathlib.RingTheory.Localization.Integral, mathlib/module/Mathlib.RingTheory.PowerSeries.Log, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: The normalized logarithmic exponential series is transcendental over the rational differential field in the variable and its exponential. -/

import D5.S1.Recurrence.Algebraic.ExponentialTranscendence
import D5.S1.Recurrence.Algebraic.ExponentialPoleObstruction
import D5.S1.Recurrence.Algebraic.AlgebraicPrimitiveDescent
import D5.S1.Recurrence.Algebraic.FractionFieldDerivation
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.LogarithmicExponentialSeries

open PowerSeries

/-- The formal series `-log(2-exp X)`, with constant coefficient zero. -/
noncomputable def F : PowerSeries ℚ := -logOf (2 - exp ℚ)

private theorem denominator_constant : constantCoeff (2 - exp ℚ) = 1 := by
  norm_num only [map_sub, map_ofNat, constantCoeff_exp]

private theorem hasSubst_argument : HasSubst ((2 - exp ℚ : PowerSeries ℚ) - 1) :=
  HasSubst.of_constantCoeff_zero' (by
    norm_num only [map_sub, map_ofNat, map_one, constantCoeff_exp])

private theorem derivative_mul : derivative F * (2 - exp ℚ) = exp ℚ := by
  have hl := congrArg (subst ((2 - exp ℚ : PowerSeries ℚ) - 1))
    (derivative_log_mul_one_add_X (A := ℚ))
  have hs := hasSubst_argument
  rw [← coe_substAlgHom hs] at hl
  simp only [map_mul, map_add, map_one, coe_substAlgHom, subst_X hs] at hl
  have harg : (1 : PowerSeries ℚ) + (2 - exp ℚ - 1) = 2 - exp ℚ := by ring
  rw [harg] at hl
  unfold F logOf
  rw [map_neg, derivative_subst hs]
  have htwo : derivative (2 : PowerSeries ℚ) = 0 := by
    exact PowerSeries.derivative.map_natCast 2
  simp only [map_sub, derivative_exp, derivative_one, htwo, sub_zero, zero_sub]
  calc
    -((derivative (log ℚ)).subst (2 - exp ℚ - 1) * -exp ℚ) * (2 - exp ℚ) =
        ((derivative (log ℚ)).subst (2 - exp ℚ - 1) * (2 - exp ℚ)) * exp ℚ := by ring
    _ = exp ℚ := by rw [hl, one_mul]

/-- The logarithmic series is the unique normalized primitive of `exp X/(2-exp X)`. -/
theorem normalized_characterization :
    constantCoeff F = 0 ∧
      derivative F = exp ℚ * (2 - exp ℚ)⁻¹ ∧
      ∀ f : PowerSeries ℚ, constantCoeff f = 0 →
        derivative f = exp ℚ * (2 - exp ℚ)⁻¹ → f = F := by
  have hi : (2 - exp ℚ : PowerSeries ℚ) * (2 - exp ℚ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [denominator_constant]; norm_num)
  have hd : derivative F = exp ℚ * (2 - exp ℚ)⁻¹ := by
    calc
      derivative F = (derivative F * (2 - exp ℚ)) * (2 - exp ℚ)⁻¹ := by
        rw [mul_assoc, hi, mul_one]
      _ = exp ℚ * (2 - exp ℚ)⁻¹ := by rw [derivative_mul]
  have hc : constantCoeff F = 0 := by
    simp only [F, map_neg, constantCoeff_logOf denominator_constant, neg_zero]
  refine ⟨hc, hd, ?_⟩
  intro f hf hdf
  exact derivative.ext (hdf.trans hd.symm) (hf.trans hc.symm)

#print axioms normalized_characterization

end D5.S1.Recurrence.Algebraic.LogarithmicExponentialSeries


open Polynomial
open scoped Differential

namespace D5.S1.Recurrence.Algebraic.ExponentialDifferentialField

attribute [local instance 2000] Algebra.toSMul

/-- The ambient field of fractions of rational formal power series. -/
abbrev L := FractionRing (PowerSeries ℚ)

/-- The rational function field in the formal variable. -/
abbrev K := RatFunc ℚ

/-- The rational function field in the variable and its exponential. -/
abbrev H := RatFunc K

noncomputable local instance : Algebra ℤ K := Ring.toIntAlgebra _
noncomputable local instance : Algebra ℤ H := Ring.toIntAlgebra _
noncomputable local instance : Algebra ℤ L := Ring.toIntAlgebra _
noncomputable local instance : Algebra ℤ (PowerSeries ℚ) := Ring.toIntAlgebra _

/-- The image of the exponential in the ambient field. -/
noncomputable def expImage : L := algebraMap (PowerSeries ℚ) L (PowerSeries.exp ℚ)

/-- The image of the normalized logarithmic exponential series. -/
noncomputable def logImage : L :=
  algebraMap (PowerSeries ℚ) L LogarithmicExponentialSeries.F

noncomputable instance tPolynomialAlgebra : Algebra ℚ[X] L :=
  ((algebraMap (PowerSeries ℚ) L).comp Polynomial.coeToPowerSeries.ringHom).toAlgebra

instance tSeriesTower : IsScalarTower ℚ[X] (PowerSeries ℚ) L :=
  IsScalarTower.of_algebraMap_eq (R := ℚ[X]) (S := PowerSeries ℚ) (A := L) fun p => by
    change algebraMap (PowerSeries ℚ) L (p : PowerSeries ℚ) = _
    congr 1

instance tPolynomialFaithful : FaithfulSMul ℚ[X] L :=
  (faithfulSMul_iff_algebraMap_injective ℚ[X] L).mpr
    ((IsFractionRing.injective (PowerSeries ℚ) L).comp (Polynomial.coe_injective ℚ))

noncomputable instance kAlgebra : Algebra K L := RatFunc.liftAlgebra ℚ L

instance tKTower : IsScalarTower ℚ[X] K L := RatFunc.isScalarTower_liftAlgebra ℚ L

instance rationalKTower : IsScalarTower ℚ K L :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := K) (A := L) (Subsingleton.elim _ _)

private theorem expImage_transcendental : Transcendental K expImage := by
  have he : Transcendental ℚ[X] expImage :=
    (transcendental_algebraMap_iff (R := ℚ[X])
      (IsFractionRing.injective (PowerSeries ℚ) L)).mpr
        ExponentialTranscendence.exp_transcendental
  intro h
  exact he ((IsFractionRing.isAlgebraic_iff ℚ[X] K L).mpr h)

noncomputable instance exponentialPolynomialAlgebra : Algebra K[X] L :=
  (Polynomial.aeval expImage).toRingHom.toAlgebra

instance exponentialPolynomialFaithful : FaithfulSMul K[X] L :=
  (faithfulSMul_iff_algebraMap_injective K[X] L).mpr
    ((transcendental_iff_injective).mp expImage_transcendental)

instance kPolynomialTower : IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq (R := K) (S := K[X]) (A := L) fun k => by
    change algebraMap K L k = Polynomial.aeval expImage (Polynomial.C k)
    simp

noncomputable instance hAlgebra : Algebra H L := RatFunc.liftAlgebra K L

instance polynomialHTower : IsScalarTower K[X] H L := RatFunc.isScalarTower_liftAlgebra K L

instance kHTower : IsScalarTower K H L :=
  IsScalarTower.of_algebraMap_eq (R := K) (S := H) (A := L) fun k => by
    rw [IsScalarTower.algebraMap_apply K K[X] H]
    rw [← IsScalarTower.algebraMap_apply K[X] H L]
    change algebraMap K L k = Polynomial.aeval expImage (Polynomial.C k)
    simp

instance rationalHTower : IsScalarTower ℚ H L :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := H) (A := L) (Subsingleton.elim _ _)

instance rationalKHTower : IsScalarTower ℚ K H :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := K) (A := H) (Subsingleton.elim _ _)

/-- The rational variable maps to the formal power series variable. -/
theorem kX_image : algebraMap K L RatFunc.X =
    algebraMap (PowerSeries ℚ) L PowerSeries.X := by
  rw [← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply ℚ[X] K L]
  change algebraMap (PowerSeries ℚ) L ((Polynomial.X : ℚ[X]) : PowerSeries ℚ) = _
  simp

/-- The second rational variable maps to the exponential. -/
theorem hX_image : algebraMap H L RatFunc.X = expImage := by
  rw [← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply K[X] H L]
  change Polynomial.aeval expImage Polynomial.X = expImage
  simp

noncomputable instance seriesDifferential : Differential (PowerSeries ℚ) where
  deriv := PowerSeries.derivative.restrictScalars ℤ

noncomputable instance ambientDifferential : Differential L where
  deriv := FractionFieldDerivation.extend (R := PowerSeries ℚ) L Differential.deriv

instance seriesAmbientDifferential : DifferentialAlgebra (PowerSeries ℚ) L where
  deriv_algebraMap r := FractionFieldDerivation.extend_algebraMap L Differential.deriv r

noncomputable instance tPolynomialDifferential : Differential ℚ[X] where
  deriv := Polynomial.derivative'.restrictScalars ℤ

noncomputable instance kDifferential : Differential K where
  deriv := FractionFieldDerivation.extend (R := ℚ[X]) K Differential.deriv

instance kAmbientDifferential : DifferentialAlgebra K L where
  deriv_algebraMap x :=
    FractionFieldDerivation.extend_commutes (R := ℚ[X]) K L
      Differential.deriv Differential.deriv (by
      intro p
      rw [IsScalarTower.algebraMap_apply ℚ[X] (PowerSeries ℚ) L,
        deriv_algebraMap,
        IsScalarTower.algebraMap_apply ℚ[X] (PowerSeries ℚ) L]
      change algebraMap (PowerSeries ℚ) L
          (PowerSeries.derivative (p : PowerSeries ℚ)) =
        algebraMap (PowerSeries ℚ) L (p.derivative : PowerSeries ℚ)
      exact congrArg (algebraMap (PowerSeries ℚ) L) (PowerSeries.derivative_coe p)) x

noncomputable instance exponentialPolynomialDifferential : Differential K[X] where
  deriv := Differential.implicitDeriv (Polynomial.X : K[X])

noncomputable instance hDifferential : Differential H where
  deriv := FractionFieldDerivation.extend (R := K[X]) H Differential.deriv

private theorem expImage_derivative : expImage′ = expImage := by
  rw [expImage, deriv_algebraMap]
  change algebraMap (PowerSeries ℚ) L (PowerSeries.derivative (PowerSeries.exp ℚ)) = _
  rw [PowerSeries.derivative_exp]

private theorem exponentialPolynomial_derivative (p : K[X]) :
    (algebraMap K[X] L p)′ = algebraMap K[X] L p′ := by
  change (Polynomial.aeval expImage p)′ =
    Polynomial.aeval expImage (Differential.implicitDeriv Polynomial.X p)
  exact Differential.deriv_aeval_eq_implicitDeriv expImage Polynomial.X
    (by simpa using expImage_derivative) p

instance hAmbientDifferential : DifferentialAlgebra H L where
  deriv_algebraMap x :=
    FractionFieldDerivation.extend_commutes (R := K[X]) H L Differential.deriv Differential.deriv
      exponentialPolynomial_derivative x

private theorem denominator_ne_zero : (2 - expImage : L) ≠ 0 := by
  intro hz
  have h : (2 - PowerSeries.exp ℚ : PowerSeries ℚ) = 0 := by
    apply IsFractionRing.injective (PowerSeries ℚ) L
    simpa only [expImage, map_sub, map_ofNat, map_zero] using hz
  have hc := congrArg PowerSeries.constantCoeff h
  norm_num only [map_sub, map_ofNat, map_zero, PowerSeries.constantCoeff_exp] at hc

/-- The logarithmic image has derivative equal to the rational function
in the exponential variable. -/
theorem logImage_derivative : logImage′ =
    algebraMap H L (RatFunc.X / (2 - RatFunc.X)) := by
  rw [map_div₀, map_sub, map_ofNat, hX_image]
  apply (eq_div_iff denominator_ne_zero).mpr
  rw [logImage, deriv_algebraMap]
  change algebraMap (PowerSeries ℚ) L
      (PowerSeries.derivative LogarithmicExponentialSeries.F) *
      (2 - expImage) = expImage
  rw [LogarithmicExponentialSeries.normalized_characterization.2.1]
  have hden : (2 - expImage : L) =
      algebraMap (PowerSeries ℚ) L (2 - PowerSeries.exp ℚ) := by
    simp only [expImage, map_sub, map_ofNat]
  rw [hden, ← map_mul, mul_assoc,
    PowerSeries.inv_mul_cancel _ (by
      norm_num only [map_sub, map_ofNat, PowerSeries.constantCoeff_exp]), mul_one]
  rfl

/-- Evaluating the rational derivative in the exponential field gives
the embedded formal derivative of the logarithmic series. -/
theorem rational_image : algebraMap H L (RatFunc.X / (2 - RatFunc.X)) =
    algebraMap (PowerSeries ℚ) L
      (PowerSeries.derivative LogarithmicExponentialSeries.F) := by
  rw [← logImage_derivative, logImage, deriv_algebraMap]
  rfl

/-- The normalized logarithmic exponential series is transcendental over
the field generated by the variable and its exponential. -/
theorem logImage_transcendental : Transcendental H logImage := by
  intro halg
  obtain ⟨h, hh⟩ := AlgebraicPrimitiveDescent.exists_primitive_of_isAlgebraic
    logImage (RatFunc.X / (2 - RatFunc.X) : H) halg logImage_derivative
  exact ExponentialPoleObstruction.no_rational_primitive
    (Differential.implicitDeriv (Polynomial.X : K[X])) (by simp)
    (FractionFieldDerivation.extend (R := K[X]) H Differential.deriv)
    (FractionFieldDerivation.extend_algebraMap (R := K[X]) H Differential.deriv) h hh

#print axioms logImage_transcendental

end D5.S1.Recurrence.Algebraic.ExponentialDifferentialField
