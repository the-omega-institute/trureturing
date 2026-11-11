/- GID: D5/S1/Dynamics/Symbolic/KhetanLaurentElimination
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Clear Laurent Bezout denominators over a coefficient fraction field. -/

import D5.S1.Dynamics.Symbolic.KhetanAnnihilator
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Ring

/-!
Clearing denominators precedes any configuration action. The resulting
coefficient is proved nonzero in the coefficient domain. The localized
coprimality required by `clear_laurent_bezout` is an algebraic intermediate
obligation; this module does not derive it from a line-factor restriction.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanLaurentElimination

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

private theorem coefficient_map_injective :
    Function.Injective (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K)) := by
  intro f g h
  ext j
  apply IsFractionRing.injective R K
  simpa using congrArg (fun F : AddMonoidAlgebra K ℤ => F.coeff j) h

/-- A finite Laurent filter has a nonzero common coefficient denominator.
The support is preserved while the coefficients are returned to the domain. -/
theorem clear_laurent_coefficients (f : AddMonoidAlgebra K ℤ) :
    ∃ d : R, d ≠ 0 ∧ ∃ F : AddMonoidAlgebra R ℤ,
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) F =
        AddMonoidAlgebra.single 0 (algebraMap R K d) * f := by
  classical
  have hfinite := f.coeff.finite_range
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors R) hfinite.toFinset
  have hex (j : ℤ) : ∃ a : R, algebraMap R K a = (d : R) • f.coeff j :=
    hd (f.coeff j) (hfinite.mem_toFinset.mpr ⟨j, rfl⟩)
  choose C hC using hex
  have hsupport : ∀ j : ℤ, C j ≠ 0 → j ∈ f.coeff.support := by
    intro j hj
    by_contra hn
    have he := hC j
    rw [Finsupp.notMem_support_iff.mp hn, smul_zero] at he
    exact hj ((IsFractionRing.injective R K) (he.trans (map_zero _).symm))
  let F : AddMonoidAlgebra R ℤ :=
    AddMonoidAlgebra.ofCoeff (Finsupp.onFinset f.coeff.support C hsupport)
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.property, F, ?_⟩
  ext j
  change algebraMap R K (C j) =
    (AddMonoidAlgebra.single 0 (algebraMap R K (d : R)) * f).coeff j
  rw [AddMonoidAlgebra.coeff_single_zero_mul]
  simpa only [Algebra.smul_def] using hC j

/-- A Bezout identity in the fraction-field Laurent ring clears to an identity
with a nonzero constant in the original coefficient domain. -/
theorem clear_laurent_bezout (P B : AddMonoidAlgebra R ℤ)
    (hcop : IsCoprime
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) P)
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) B)) :
    ∃ ρ : R, ρ ≠ 0 ∧ ∃ α β : AddMonoidAlgebra R ℤ,
      AddMonoidAlgebra.single 0 ρ = α * P + β * B := by
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨da, hda, A, hA⟩ := clear_laurent_coefficients (R := R) a
  obtain ⟨db, hdb, C, hC⟩ := clear_laurent_coefficients (R := R) b
  refine ⟨da * db, mul_ne_zero hda hdb,
    AddMonoidAlgebra.single 0 db * A, AddMonoidAlgebra.single 0 da * C, ?_⟩
  apply coefficient_map_injective (K := K)
  simp only [map_add, map_mul, AddMonoidAlgebra.mapRingHom_single, hA, hC]
  calc
    AddMonoidAlgebra.single 0 (algebraMap R K da * algebraMap R K db) =
        (AddMonoidAlgebra.single 0 (algebraMap R K da) *
          AddMonoidAlgebra.single 0 (algebraMap R K db)) * (a *
          AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) P + b *
          AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) B) := by
      rw [hab, mul_one, AddMonoidAlgebra.single_mul_single, zero_add]
    _ = _ := by ring

omit [IsDomain R] in
private theorem map_to_laurent {S : Type*} [CommRing S] (f : R →+* S)
    (p : Polynomial R) :
    AddMonoidAlgebra.mapRingHom ℤ f p.toLaurent = (p.map f).toLaurent := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.toLaurent_C_mul_T,
      Polynomial.toLaurent_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.mapRingHom_single]

/-- Monicity descends a hypothetical polynomial divisor from the coefficient
fraction field. Shifting the Laurent dividend only multiplies it by a unit,
so absence of this divisor in the original Laurent ring proves actual
localized Bezout coprimality. -/
theorem localized_coprime_of_monic_irreducible_not_dvd
    (P : LaurentPolynomial R) (g : Polynomial R) (hg : g.Monic)
    (hirr : Irreducible (g.map (algebraMap R K))) (hnot : ¬g.toLaurent ∣ P) :
    IsCoprime
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) P)
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) g.toLaurent) := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow P
  have hnd : ¬ g.map (algebraMap R K) ∣ p.map (algebraMap R K) := by
    intro hd
    obtain ⟨q, hq⟩ := (Polynomial.map_dvd_map (algebraMap R K)
      (IsFractionRing.injective R K) hg).mp hd
    apply hnot
    refine ⟨q.toLaurent * LaurentPolynomial.T (-(n : ℤ)), ?_⟩
    calc
      P = p.toLaurent * LaurentPolynomial.T (-(n : ℤ)) := by
        rw [hp, LaurentPolynomial.mul_T_assoc]
        simp
      _ = g.toLaurent * (q.toLaurent * LaurentPolynomial.T (-(n : ℤ))) := by
        rw [hq, map_mul, mul_assoc]
  have hc := (hirr.coprime_iff_not_dvd.mpr hnd).map
    (Polynomial.toLaurent : Polynomial K →+* LaurentPolynomial K)
  rw [← map_to_laurent, ← map_to_laurent, hp, map_mul] at hc
  exact hc.symm.of_mul_left_left

/-- A finite transverse factorization can discharge the coprimality premise
before denominator clearing. The supplied polynomials must be monic, remain
irreducible over the coefficient fraction field, and not divide `P` in the
original Laurent ring. This theorem does not assume a nonzero eliminant. -/
theorem clear_laurent_bezout_of_monic_factors
    (P B : LaurentPolynomial R) (factors : List (Polynomial R))
    (hB : B ∣ (factors.map Polynomial.toLaurent).prod)
    (hmonic : ∀ g ∈ factors, g.Monic)
    (hirr : ∀ g ∈ factors, Irreducible (g.map (algebraMap R K)))
    (hnot : ∀ g ∈ factors, ¬g.toLaurent ∣ P) :
    ∃ ρ : R, ρ ≠ 0 ∧ ∃ α β : LaurentPolynomial R,
      AddMonoidAlgebra.single 0 ρ = α * P + β * B := by
  have hcop : IsCoprime
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) P)
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K)
        (factors.map Polynomial.toLaurent).prod) := by
    rw [map_list_prod, List.map_map]
    clear hB
    revert hmonic hirr hnot
    induction factors with
    | nil => intros; exact isCoprime_one_right
    | cons g gs ih =>
      intro hmonic hirr hnot
      rw [List.map_cons, List.prod_cons]
      apply IsCoprime.mul_right
      · exact localized_coprime_of_monic_irreducible_not_dvd P g
          (hmonic g (by simp)) (hirr g (by simp)) (hnot g (by simp))
      · apply ih
        · intro q hq; exact hmonic q (by simp [hq])
        · intro q hq; exact hirr q (by simp [hq])
        · intro q hq; exact hnot q (by simp [hq])
  apply clear_laurent_bezout (K := K) P B
  exact (hcop.symm.of_isCoprime_of_dvd_left
    ((AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K)).map_dvd hB)).symm

end D5.S1.Dynamics.Symbolic.KhetanLaurentElimination
