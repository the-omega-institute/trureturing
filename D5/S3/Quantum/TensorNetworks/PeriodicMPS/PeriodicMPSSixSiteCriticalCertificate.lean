/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalCertificate
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Resultant.Basic]
   utility: none
   digest: A characteristic-zero coprimality certificate for the selected six-site critical minors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteProjectiveLine
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch0
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch8
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch16
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch24
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch32
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch40
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch48
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch56
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch64
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch72
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch80
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorBatch88

/-! Exact calculations at 94 residues identify both full-degree line restrictions. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCriticalCertificate

open Polynomial PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteProjectiveLine

private theorem point_values (t : Fin 94) :
    let q : F := (t : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  by_cases h8 : (t : ℕ) < 8
  · have h : 0 + ((t : ℕ) - 0) = (t : ℕ) := by omega
    have hval := PeriodicMPSSixSiteMinorBatch0.pointValues
      (⟨(t : ℕ) - 0, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h16 : (t : ℕ) < 16
  · have h : 8 + ((t : ℕ) - 8) = (t : ℕ) := by omega
    have hval := PeriodicMPSSixSiteMinorBatch8.pointValues
      (⟨(t : ℕ) - 8, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h24 : (t : ℕ) < 24
  · have h : 16 + ((t : ℕ) - 16) = (t : ℕ) := by omega
    have hval := PeriodicMPSSixSiteMinorBatch16.pointValues
      (⟨(t : ℕ) - 16, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h32 : (t : ℕ) < 32
  · have h : 24 + ((t : ℕ) - 24) = (t : ℕ) := by omega
    have hval := PeriodicMPSSixSiteMinorBatch24.pointValues
      (⟨(t : ℕ) - 24, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h40 : (t : ℕ) < 40
  · have h : 32 + ((t : ℕ) - 32) = (t : ℕ) := by omega
    have hval := PeriodicMPSSixSiteMinorBatch32.pointValues
      (⟨(t : ℕ) - 32, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h48 : (t : ℕ) < 48
  · have h : 40 + ((t : ℕ) - 40) = (t : ℕ) := by omega
    have hval := PeriodicMPSSixSiteMinorBatch40.pointValues
      (⟨(t : ℕ) - 40, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h56 : (t : ℕ) < 56
  · have h : 48 + ((t : ℕ) - 48) = (t : ℕ) := by omega
    have hval := PeriodicMPSSixSiteMinorBatch48.pointValues
      (⟨(t : ℕ) - 48, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h64 : (t : ℕ) < 64
  · have h : 56 + ((t : ℕ) - 56) = (t : ℕ) := by omega
    have hval := PeriodicMPSSixSiteMinorBatch56.pointValues
      (⟨(t : ℕ) - 56, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h72 : (t : ℕ) < 72
  · have h : 64 + ((t : ℕ) - 64) = (t : ℕ) := by omega
    have hval := PeriodicMPSSixSiteMinorBatch64.pointValues
      (⟨(t : ℕ) - 64, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h80 : (t : ℕ) < 80
  · have h : 72 + ((t : ℕ) - 72) = (t : ℕ) := by omega
    have hval := PeriodicMPSSixSiteMinorBatch72.pointValues
      (⟨(t : ℕ) - 72, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h88 : (t : ℕ) < 88
  · have h : 80 + ((t : ℕ) - 80) = (t : ℕ) := by omega
    have hval := PeriodicMPSSixSiteMinorBatch80.pointValues
      (⟨(t : ℕ) - 80, by omega⟩ : Fin 8)
    simpa only [h] using hval
  have h : 88 + ((t : ℕ) - 88) = (t : ℕ) := by omega
  have hval := PeriodicMPSSixSiteMinorBatch88.pointValues
    (⟨(t : ℕ) - 88, by have := t.isLt; omega⟩ : Fin 6)
  simpa only [h] using hval

/-- Both integral restrictions have full degree and their Sylvester determinant is nonzero. -/
theorem integral_certificate :
    (linePolynomial 0).natDegree = 93 ∧ (linePolynomial 1).natDegree = 93 ∧
      resultant (linePolynomial 0) (linePolynomial 1) 93 93 ≠ 0 :=
  integral_certificate_of_point_values (fun t => (point_values t).1) (fun t => (point_values t).2)

/-- The two line restrictions are coprime over every characteristic-zero field. -/
theorem coprime_restrictions {K : Type*} [Field K] [CharZero K] :
    IsCoprime (residualMinor (Polynomial.X : K[X]) 0) (residualMinor (Polynomial.X : K[X]) 1) :=
  charZero_certificate_of_integral integral_certificate.1 integral_certificate.2.1
    integral_certificate.2.2

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCriticalCertificate
