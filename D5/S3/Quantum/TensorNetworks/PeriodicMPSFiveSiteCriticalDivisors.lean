/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCriticalDivisors
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCriticalDivisors
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalCertificate]
   utility: none
   digest: The two selected five-site Jacobian minors have no common nonunit divisor. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalCertificate
import D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedLineSpecialization

/-! Degree preservation extends the line certificate to the full critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalDivisors

open MvPolynomial PeriodicMPSFiveSiteLineMinors PeriodicMPSFiveSiteWeightedMinors
  PeriodicMPSFiveSiteProjectiveLine PeriodicMPSFiveSiteCriticalCertificate
  PeriodicMPSWeightedLineSpecialization

open private degree_line from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteWeightedMinors

noncomputable section

variable {K : Type*} [Field K]

/-- The selected weighted Jacobian minors with coefficients in a characteristic-zero field. -/
def minorOver (k : Fin 10) : MvPolynomial (Fin 10) K :=
  MvPolynomial.map (Int.castRingHom K) (symbolicMinor k)

private lemma minorOver_weight (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    (minorOver (K := K) k).IsWeightedHomogeneous weights 75 := by
  intro m hm
  apply symbolicMinor_weight k hk
  exact mem_support_iff.mp (support_map_subset _ _ (mem_support_iff.mpr hm))

private lemma specialized_minor (k : Fin 10) :
    eval₂Hom Polynomial.C (line (Polynomial.X : Polynomial K)) (minorOver k) =
      residualMinor (Polynomial.X : Polynomial K) k := by
  rw [minorOver, MvPolynomial.eval₂Hom_map_hom]
  have h : (Polynomial.C : K →+* Polynomial K).comp (Int.castRingHom K) =
      Int.castRingHom (Polynomial K) := RingHom.ext_int _ _
  exact h ▸ evaluated_symbolicMinor _ k

variable [CharZero K]

private lemma first_full_degree :
    (residualMinor (Polynomial.X : Polynomial K) 0).natDegree = 75 := by
  have h := map_minor (Polynomial.mapRingHom (Int.castRingHom K))
    (Polynomial.X : Polynomial ℤ) 0
  have hm : (linePolynomial 0).map (Int.castRingHom K) =
      residualMinor (Polynomial.X : Polynomial K) 0 := by
    simpa [linePolynomial] using h
  rw [← hm, Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
  exact integral_certificate.1

private theorem restricted_first_ne_zero :
    residualMinor (Polynomial.X : Polynomial K) 0 ≠ 0 := by
  intro h
  have hd := first_full_degree (K := K)
  rw [h, Polynomial.natDegree_zero] at hd
  omega

theorem first_minor_ne_zero : minorOver (K := K) 0 ≠ 0 := by
  intro h
  have he := specialized_minor (K := K) 0
  rw [h, map_zero] at he
  exact restricted_first_ne_zero he.symm

/-- The full weighted minors have no common nonunit polynomial divisor over
any characteristic-zero field, in particular over the complex numbers. -/
theorem relatively_prime_minors :
    IsRelPrime (minorOver (K := K) 0) (minorOver (K := K) 1) := by
  apply isRelPrime_of_full_degree_specialization weights
    (fun i => by fin_cases i <;> decide) (line (Polynomial.X : Polynomial K)) degree_line
    _ _ 75 (minorOver_weight 0 (.inl rfl))
  · rw [specialized_minor]
    exact first_full_degree
  · rw [specialized_minor]
    exact restricted_first_ne_zero
  · rw [specialized_minor, specialized_minor]
    exact coprime_restrictions

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalDivisors
