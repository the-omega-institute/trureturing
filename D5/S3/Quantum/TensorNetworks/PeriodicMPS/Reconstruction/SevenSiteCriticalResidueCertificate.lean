/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalResidueCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalResidueCertificate
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueComparison]
   utility: none
   digest: Two literal cofactor quotients have degree-46 affine restrictions with nonzero resultant modulo 1009. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueBatch0
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueBatch6
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueBatch12
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueBatch18
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueBatch24
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueBatch30
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueBatch36
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueBatch42
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteLiteralBatch0
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteLiteralBatch1
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteLiteralBatch2
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteLiteralBatch3
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteLiteralBatch4
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteLiteralBatch5
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteLiteralBatch6
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueComparison

/-! The certified affine-line quotients of the two seven-site critical cofactors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

open Polynomial

private theorem literal_values (t : Fin 7) (ab : Fin 4 × Fin 4) :
    slicedObservation imaginary (point ((t : ℕ) : F)) ab = valueAt ((t : ℕ) : F) ab := by
  fin_cases t

  · exact literal_value_at_0 ab
  · exact literal_value_at_1 ab
  · exact literal_value_at_2 ab
  · exact literal_value_at_3 ab
  · exact literal_value_at_4 ab
  · exact literal_value_at_5 ab
  · exact literal_value_at_6 ab

private theorem literal_partials (t : Fin 7) (r : Fin 10) (j : Fin 5) :
    partialValue imaginary (point ((t : ℕ) : F)) (observedRow r) j =
      partialAt ((t : ℕ) : F) r j := by
  fin_cases t

  · exact literal_partial_at_0 r j
  · exact literal_partial_at_1 r j
  · exact literal_partial_at_2 r j
  · exact literal_partial_at_3 r j
  · exact literal_partial_at_4 r j
  · exact literal_partial_at_5 r j
  · exact literal_partial_at_6 r j

private theorem cofactor_samples_0 (t : Fin 47) :
    (evaluatedRows (node t) 0).det = point (node t) 1 * quotientValue 0 (node t) := by
  fin_cases t
  · exact cofactor_at_0_0
  · exact cofactor_at_0_1
  · exact cofactor_at_0_2
  · exact cofactor_at_0_3
  · exact cofactor_at_0_4
  · exact cofactor_at_0_5
  · exact cofactor_at_0_6
  · exact cofactor_at_0_7
  · exact cofactor_at_0_8
  · exact cofactor_at_0_9
  · exact cofactor_at_0_10
  · exact cofactor_at_0_11
  · exact cofactor_at_0_12
  · exact cofactor_at_0_13
  · exact cofactor_at_0_14
  · exact cofactor_at_0_15
  · exact cofactor_at_0_16
  · exact cofactor_at_0_17
  · exact cofactor_at_0_18
  · exact cofactor_at_0_19
  · exact cofactor_at_0_20
  · exact cofactor_at_0_21
  · exact cofactor_at_0_22
  · exact cofactor_at_0_23
  · exact cofactor_at_0_24
  · exact cofactor_at_0_25
  · exact cofactor_at_0_26
  · exact cofactor_at_0_27
  · exact cofactor_at_0_28
  · exact cofactor_at_0_29
  · exact cofactor_at_0_30
  · exact cofactor_at_0_31
  · exact cofactor_at_0_32
  · exact cofactor_at_0_33
  · exact cofactor_at_0_34
  · exact cofactor_at_0_35
  · exact cofactor_at_0_36
  · exact cofactor_at_0_37
  · exact cofactor_at_0_38
  · exact cofactor_at_0_39
  · exact cofactor_at_0_40
  · exact cofactor_at_0_41
  · exact cofactor_at_0_42
  · exact cofactor_at_0_43
  · exact cofactor_at_0_44
  · exact cofactor_at_0_45
  · exact cofactor_at_0_46

private theorem cofactor_samples_1 (t : Fin 47) :
    (evaluatedRows (node t) 1).det = point (node t) 1 * quotientValue 1 (node t) := by
  fin_cases t
  · exact cofactor_at_1_0
  · exact cofactor_at_1_1
  · exact cofactor_at_1_2
  · exact cofactor_at_1_3
  · exact cofactor_at_1_4
  · exact cofactor_at_1_5
  · exact cofactor_at_1_6
  · exact cofactor_at_1_7
  · exact cofactor_at_1_8
  · exact cofactor_at_1_9
  · exact cofactor_at_1_10
  · exact cofactor_at_1_11
  · exact cofactor_at_1_12
  · exact cofactor_at_1_13
  · exact cofactor_at_1_14
  · exact cofactor_at_1_15
  · exact cofactor_at_1_16
  · exact cofactor_at_1_17
  · exact cofactor_at_1_18
  · exact cofactor_at_1_19
  · exact cofactor_at_1_20
  · exact cofactor_at_1_21
  · exact cofactor_at_1_22
  · exact cofactor_at_1_23
  · exact cofactor_at_1_24
  · exact cofactor_at_1_25
  · exact cofactor_at_1_26
  · exact cofactor_at_1_27
  · exact cofactor_at_1_28
  · exact cofactor_at_1_29
  · exact cofactor_at_1_30
  · exact cofactor_at_1_31
  · exact cofactor_at_1_32
  · exact cofactor_at_1_33
  · exact cofactor_at_1_34
  · exact cofactor_at_1_35
  · exact cofactor_at_1_36
  · exact cofactor_at_1_37
  · exact cofactor_at_1_38
  · exact cofactor_at_1_39
  · exact cofactor_at_1_40
  · exact cofactor_at_1_41
  · exact cofactor_at_1_42
  · exact cofactor_at_1_43
  · exact cofactor_at_1_44
  · exact cofactor_at_1_45
  · exact cofactor_at_1_46

/-- For either certified deletion, the supplied coefficients represent the
line restriction of the actual multivariate cofactor divided by the variable k. -/
theorem actual_line_quotient_eq (deleted : Fin 10) (hd : deleted = 0 ∨ deleted = 1)
    (p : Slice F) (hp : (criticalMatrix imaginary deleted).det = MvPolynomial.X 1 * p) :
    affineRestriction p = lineQuotient deleted := by
  apply identify_line_quotient deleted hd p hp literal_values literal_partials
  rcases hd with rfl | rfl
  · exact cofactor_samples_0
  · exact cofactor_samples_1

/-- The actual seven-site cofactor quotients have full degree and an explicit
Bézout identity after restriction to the chosen affine line over ZMod 1009. -/
theorem actual_line_quotients_certificate (p q : Slice F)
    (hp : (criticalMatrix imaginary 0).det = MvPolynomial.X 1 * p)
    (hq : (criticalMatrix imaginary 1).det = MvPolynomial.X 1 * q) :
    (affineRestriction p).natDegree = 46 ∧
    (affineRestriction q).natDegree = 46 ∧
    ofFn 46 bezout_0 * affineRestriction p + ofFn 46 bezout_1 * affineRestriction q = 1 ∧
    resultant (affineRestriction p) (affineRestriction q) ≠ 0 := by
  rw [actual_line_quotient_eq 0 (.inl rfl) p hp, actual_line_quotient_eq 1 (.inr rfl) q hq]
  exact ⟨lineQuotient_degree 0 (.inl rfl), lineQuotient_degree 1 (.inr rfl),
    concrete_bezout, concrete_resultant⟩

/-- There exist actual quotients with nonzero resultant on the affine line. -/
theorem seven_site_modular_resultant :
    ∃ p q : Slice F,
      (criticalMatrix imaginary 0).det = MvPolynomial.X 1 * p ∧
      (criticalMatrix imaginary 1).det = MvPolynomial.X 1 * q ∧
      (affineRestriction p).natDegree = 46 ∧
      (affineRestriction q).natDegree = 46 ∧
      resultant (affineRestriction p) (affineRestriction q) ≠ 0 := by
  obtain ⟨p, hp, _⟩ := critical_cofactor_quotient imaginary imaginary_sq
    (by decide : (6 : F) ≠ 0) 0
  obtain ⟨q, hq, _⟩ := critical_cofactor_quotient imaginary imaginary_sq
    (by decide : (6 : F) ≠ 0) 1
  obtain ⟨hdp, hdq, _, hres⟩ := actual_line_quotients_certificate p q hp hq
  exact ⟨p, q, hp, hq, hdp, hdq, hres⟩

#print axioms actual_line_quotients_certificate
#print axioms seven_site_modular_resultant

end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate
