/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorSpectralNorm
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Eval]
   utility: none
   digest: Literal real canonical spectral exclusion factors and the consumed actual ambiguity endpoint. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorSpectralNorm

open Matrix MvPolynomial
open OpenBoundaryMPSDensityGenericity (realCoeff imagCoeff coefficient_eval)
open OpenBoundaryMPSInteriorCommonCore (rawInterior)
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber
open D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial
open D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
open D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality (mpsState openBoundaryMPS)
open PeriodicMPSParentIntersection (Word)

abbrev CanonicalPoly := MvPolynomial (Fin 13) ℝ

def canonicalCorePoly (i : Fin 5) : MvPolynomial (Fin 13) ℂ :=
  coreVariable i

def canonicalEtaPoly : MvPolynomial (Fin 13) ℂ := etaVariable

def canonicalH : MvPolynomial (Fin 13) ℂ :=
  canonicalCorePoly 4 - canonicalCorePoly 1

def canonicalD : MvPolynomial (Fin 13) ℂ :=
  canonicalH ^ 2 + 4 * canonicalCorePoly 2 *
    canonicalCorePoly 3

def canonicalT0 : MvPolynomial (Fin 13) ℂ :=
  canonicalCorePoly 1 - canonicalCorePoly 0 * canonicalCorePoly 2

def canonicalT1 : MvPolynomial (Fin 13) ℂ :=
  1 + canonicalCorePoly 3 -
    canonicalCorePoly 0 * canonicalCorePoly 4

def canonicalU : MvPolynomial (Fin 13) ℂ :=
  canonicalH * canonicalT0 * canonicalT1 - canonicalCorePoly 2 * canonicalT1 ^ 2 +
    canonicalCorePoly 3 * canonicalT0 ^ 2

def canonicalHbase : MvPolynomial (Fin 13) ℂ :=
  canonicalCorePoly 2 * canonicalD * canonicalU * (canonicalU + canonicalD)

def canonicalJden : CanonicalPoly :=
  realCoeff canonicalHbase ^ 2 + imagCoeff canonicalHbase ^ 2

def canonicalW : MvPolynomial (Fin 13) ℂ :=
  canonicalCorePoly 2 * canonicalEtaPoly ^ 2 +
    (canonicalCorePoly 1 - canonicalCorePoly 4) * canonicalEtaPoly -
    canonicalCorePoly 3

def canonicalWnorm : CanonicalPoly :=
  realCoeff canonicalW ^ 2 + imagCoeff canonicalW ^ 2

def K0 (g : Fin 4 → CanonicalPoly) (A B : CanonicalPoly) : CanonicalPoly :=
  g 0 ^ 2 + (A ^ 2 + B ^ 2) * g 3 ^ 2 -
    C (1 / 2 : ℝ) * A * (g 1 ^ 2 - g 2 ^ 2) - B * g 1 * g 2

def H0 (g : Fin 4 → CanonicalPoly) : CanonicalPoly :=
  2 * g 0 * g 3 - C (1 / 2 : ℝ) * (g 1 ^ 2 + g 2 ^ 2)

def normg (g : Fin 4 → CanonicalPoly) (A B : CanonicalPoly) : CanonicalPoly :=
  K0 g A B ^ 2 - (A ^ 2 + B ^ 2) * H0 g ^ 2

def spectralCertificate (g : Fin 4 → CanonicalPoly) (A B : CanonicalPoly) : CanonicalPoly :=
  X 10 * canonicalJden * canonicalWnorm * normg g A B

section Characters
variable {T : Type*} [CommRing T] [Algebra ℂ T]

def character (g : Fin 4 → T) (E F : T) : T :=
  g 0 + algebraMap ℂ T (1/2) * g 1 * (E+F) -
    algebraMap ℂ T (Complex.I/2) * g 2 * (E-F) + g 3 * E * F

def pairK (g : Fin 4 → T) (a b : T) : T :=
  g 0 ^ 2 + (a ^ 2 + b ^ 2) * g 3 ^ 2 -
    algebraMap ℂ T (1/2) * a * (g 1 ^ 2 - g 2 ^ 2) - b * g 1 * g 2

def pairH (g : Fin 4 → T) : T :=
  2 * g 0 * g 3 - algebraMap ℂ T (1/2) * (g 1 ^ 2 + g 2 ^ 2)

/-- Opposite characters pair together; neither single-sign pair has this value. -/
theorem character_opposite (g : Fin 4 → T) (a b E F : T)
    (hE : E ^ 2 = a + algebraMap ℂ T Complex.I * b)
    (hF : F ^ 2 = a - algebraMap ℂ T Complex.I * b) :
    character g E F * character g (-E) (-F) = pairK g a b + pairH g * E * F := by
  have hi : algebraMap ℂ T Complex.I ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq]; simp
  have hh : algebraMap ℂ T (1/2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℂ T) 2, ← map_mul]; norm_num
  have hi2 : algebraMap ℂ T (Complex.I/2) =
      algebraMap ℂ T Complex.I * algebraMap ℂ T (1/2) := by
    rw [← map_mul]; congr 1; ring
  dsimp [character, pairK, pairH]
  rw [hi2]
  ring_nf
  simp only [hE, hF]
  ring_nf
  simp only [hi]
  have hh' : algebraMap ℂ T (1/2) = (algebraMap ℂ T (1/2))^2 * 2 := by
    linear_combination -(algebraMap ℂ T (1/2)) * hh
  have hh'' : (algebraMap ℂ T (1/2))^2 * 4 = 1 := by
    linear_combination (algebraMap ℂ T (1/2) * 2 + 1) * hh
  linear_combination (norm := ring_nf)
    (E*F*(g 1^2+g 2^2)+(g 1^2*a-g 2^2*a))*hh' -
    (g 1*g 2*b)*hh''


/-- The mixed opposite pair carries the negative EF coefficient. -/
theorem character_mixed (g : Fin 4 → T) (a b E F : T)
    (hE : E ^ 2 = a + algebraMap ℂ T Complex.I * b)
    (hF : F ^ 2 = a - algebraMap ℂ T Complex.I * b) :
    character g (-E) F * character g E (-F) = pairK g a b - pairH g * E * F := by
  simpa [sub_eq_add_neg] using character_opposite g a b (-E) F (by simpa using hE) hF

/-- The four-character product is a literal polynomial identity, with no domain assumption. -/
theorem character_four_factor (g : Fin 4 → T) (a b E F : T)
    (hE : E ^ 2 = a + algebraMap ℂ T Complex.I * b)
    (hF : F ^ 2 = a - algebraMap ℂ T Complex.I * b) :
    character g E F * character g (-E) F * character g E (-F) *
      character g (-E) (-F) = pairK g a b ^ 2 - (a ^ 2 + b ^ 2) * pairH g ^ 2 := by
  have hi : algebraMap ℂ T Complex.I ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq]; simp
  have hef : E ^ 2 * F ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hE, hF]; ring_nf; rw [hi]; ring
  calc
    _ = (character g E F * character g (-E) (-F)) *
        (character g (-E) F * character g E (-F)) := by ring
    _ = (pairK g a b + pairH g * E * F) *
        (pairK g a b - pairH g * E * F) := by
      rw [character_opposite g a b E F hE hF, character_mixed g a b E F hE hF]
    _ = pairK g a b ^ 2 - (a ^ 2 + b ^ 2) * pairH g ^ 2 := by
      linear_combination (norm := ring) -(pairH g)^2 * hef
end Characters

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorSpectralNorm
