/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCriticalCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCriticalCertificate
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Resultant.Basic]
   utility: none
   digest: A characteristic-zero coprimality certificate for the selected five-site critical minors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteProjectiveLine
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch0
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch8
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch16
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch24
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch32
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch40
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch48
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch56
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch64
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch72

/-! Exact calculations at 76 residues identify both full-degree line restrictions. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalCertificate

open Polynomial PeriodicMPSFiveSiteLineBezout PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteProjectiveLine

private theorem point_values (t : Fin 76) :
    let q : F := (t : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  by_cases h8 : (t : ℕ) < 8
  · have h : 0 + ((t : ℕ) - 0) = (t : ℕ) := by omega
    have hval := PeriodicMPSFiveSiteMinorBatch0.pointValues (⟨(t : ℕ) - 0, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h16 : (t : ℕ) < 16
  · have h : 8 + ((t : ℕ) - 8) = (t : ℕ) := by omega
    have hval := PeriodicMPSFiveSiteMinorBatch8.pointValues (⟨(t : ℕ) - 8, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h24 : (t : ℕ) < 24
  · have h : 16 + ((t : ℕ) - 16) = (t : ℕ) := by omega
    have hval := PeriodicMPSFiveSiteMinorBatch16.pointValues (⟨(t : ℕ) - 16, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h32 : (t : ℕ) < 32
  · have h : 24 + ((t : ℕ) - 24) = (t : ℕ) := by omega
    have hval := PeriodicMPSFiveSiteMinorBatch24.pointValues (⟨(t : ℕ) - 24, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h40 : (t : ℕ) < 40
  · have h : 32 + ((t : ℕ) - 32) = (t : ℕ) := by omega
    have hval := PeriodicMPSFiveSiteMinorBatch32.pointValues (⟨(t : ℕ) - 32, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h48 : (t : ℕ) < 48
  · have h : 40 + ((t : ℕ) - 40) = (t : ℕ) := by omega
    have hval := PeriodicMPSFiveSiteMinorBatch40.pointValues (⟨(t : ℕ) - 40, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h56 : (t : ℕ) < 56
  · have h : 48 + ((t : ℕ) - 48) = (t : ℕ) := by omega
    have hval := PeriodicMPSFiveSiteMinorBatch48.pointValues (⟨(t : ℕ) - 48, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h64 : (t : ℕ) < 64
  · have h : 56 + ((t : ℕ) - 56) = (t : ℕ) := by omega
    have hval := PeriodicMPSFiveSiteMinorBatch56.pointValues (⟨(t : ℕ) - 56, by omega⟩ : Fin 8)
    simpa only [h] using hval
  by_cases h72 : (t : ℕ) < 72
  · have h : 64 + ((t : ℕ) - 64) = (t : ℕ) := by omega
    have hval := PeriodicMPSFiveSiteMinorBatch64.pointValues (⟨(t : ℕ) - 64, by omega⟩ : Fin 8)
    simpa only [h] using hval
  have h : 72 + ((t : ℕ) - 72) = (t : ℕ) := by omega
  have hval := PeriodicMPSFiveSiteMinorBatch72.pointValues
    (⟨(t : ℕ) - 72, by have := t.isLt; omega⟩ : Fin 4)
  simpa only [h] using hval

/-- Both integral restrictions have full degree and their Sylvester determinant is nonzero. -/
theorem integral_certificate :
    (linePolynomial 0).natDegree = 75 ∧ (linePolynomial 1).natDegree = 75 ∧
      resultant (linePolynomial 0) (linePolynomial 1) 75 75 ≠ 0 :=
  integral_certificate_of_point_values (fun t => (point_values t).1) (fun t => (point_values t).2)

/-- The two line restrictions are coprime over every characteristic-zero field. -/
theorem coprime_restrictions {K : Type*} [Field K] [CharZero K] :
    IsCoprime (residualMinor (Polynomial.X : K[X]) 0) (residualMinor (Polynomial.X : K[X]) 1) :=
  charZero_certificate_of_integral integral_certificate.1 integral_certificate.2.1
    integral_certificate.2.2

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalCertificate
