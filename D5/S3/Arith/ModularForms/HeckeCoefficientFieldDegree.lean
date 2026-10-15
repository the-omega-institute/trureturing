/- GID: D5/S3/Arith/ModularForms/HeckeCoefficientFieldDegree
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/HeckeCoefficientFieldDegree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A normalized actual Hecke eigenform has coefficient field degree at most m. -/

import D5.S1.Eigenstructure.CommonEigenvalueFieldDegree
import D5.S3.Arith.ModularForms.FiniteHeckeArray

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups
open scoped BigOperators Matrix

namespace D5.S3.Arith.ModularForms

noncomputable section

private lemma coefficient_mem_of_first_miller
    (m s : ℕ) (hm : 1 ≤ m) (hs : MillerResidualWeight s)
    (f : CuspForm 𝒮ℒ (12 * m + s : ℕ)) (E : IntermediateField ℚ ℂ)
    (hfirst : ∀ j : Fin m, (qExpansion 1 f).coeff (j.val + 1) ∈ E) :
    ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ E := by
  classical
  intro n
  let coefficient : CuspForm 𝒮ℒ (12 * m + s : ℕ) →+ ℂ :=
    (PowerSeries.coeff n).toAddMonoidHom.comp
      ((ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL _).comp
        CuspForm.toModularFormₗ.toAddMonoidHom)
  have hsmul (a : ℂ) (g : CuspForm 𝒮ℒ (12 * m + s : ℕ)) :
      coefficient (a • g) = a * coefficient g := by
    change (qExpansion 1 (a • g)).coeff n = a * (qExpansion 1 g).coeff n
    rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
    rfl
  have hr := congrArg coefficient ((integralMillerBasis m s hm hs).sum_equivFun f)
  rw [map_sum] at hr
  simp_rw [hsmul] at hr
  change (∑ j : Fin m, millerCoefficientEquiv m s hm hs f j *
    (qExpansion 1 (integralMillerBasis m s hm hs j)).coeff n) =
      (qExpansion 1 f).coeff n at hr
  simp_rw [millerCoefficientEquiv_apply, integralMillerBasis_apply,
    millerForm_coefficient] at hr
  rw [← hr]
  exact E.sum_mem fun j _ => E.mul_mem (hfirst j) (E.intCast_mem _)

private lemma coefficient_mem_of_prime_eigenvalues
    {k : ℤ} (f : CuspForm 𝒮ℒ k)
    (hnorm : (qExpansion 1 f).coeff 1 = 1)
    (eigenvalues : {p : ℕ // p.Prime} → ℂ)
    (heig : ∀ p : {p : ℕ // p.Prime},
      letI : Fact p.val.Prime := ⟨p.property⟩
      primeHecke p.val k f = eigenvalues p • f)
    (E : IntermediateField ℚ ℂ) (hvalues : ∀ p, eigenvalues p ∈ E) :
    ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ E := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn₀ : n = 0
    · subst n
      rw [CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods_SL]
      exact E.zero_mem
    by_cases hn₁ : n = 1
    · subst n
      rw [hnorm]
      exact E.one_mem
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn₁
    let : Fact p.Prime := ⟨hp⟩
    have hr : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn₀) hp.one_lt
    have hrr : n / p / p < n := (Nat.div_le_self _ _).trans_lt hr
    have hcoef := primeHecke_qExpansion_coeff p k f (n / p)
    rw [heig ⟨p, hp⟩, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (eigenvalues ⟨p, hp⟩) f,
      PowerSeries.coeff_smul, smul_eq_mul, Nat.mul_div_cancel' hpn] at hcoef
    have hcorrection :
        (p : ℂ) ^ (k - 1) *
          (if p ∣ n / p then (qExpansion 1 f).coeff (n / p / p) else 0) ∈ E := by
      apply E.mul_mem (E.pow_mem (IntermediateField.natCast_mem E p) (k - 1))
      split_ifs
      · exact ih _ hrr
      · exact E.zero_mem
    have hm := E.mul_mem (hvalues ⟨p, hp⟩) (ih _ hr)
    have heq : (qExpansion 1 f).coeff n =
        eigenvalues ⟨p, hp⟩ * (qExpansion 1 f).coeff (n / p) -
          (p : ℂ) ^ (k - 1) *
            (if p ∣ n / p then (qExpansion 1 f).coeff (n / p / p) else 0) := by
      rw [hcoef]
      ring
    rw [heq]
    exact E.sub_mem hm hcorrection

/-- The first `m` coefficients generate exactly the coefficient field of the same
normalized actual prime-Hecke eigenform, and this field has degree at most `m`.
All primes enter the eigenform hypothesis; zero eigenvalues remain allowed. -/
theorem normalized_primeHecke_coefficient_field_degree
    (m s : ℕ) (hm : 1 ≤ m) (hs : MillerResidualWeight s)
    (f : CuspForm 𝒮ℒ (12 * m + s : ℕ))
    (hnorm : (qExpansion 1 f).coeff 1 = 1)
    (eigenvalues : {p : ℕ // p.Prime} → ℂ)
    (heig : ∀ p : {p : ℕ // p.Prime},
      letI : Fact p.val.Prime := ⟨p.property⟩
      primeHecke p.val (12 * m + s : ℕ) f = eigenvalues p • f) :
    let K := IntermediateField.adjoin ℚ
      (Set.range (fun j : Fin m => (qExpansion 1 f).coeff (j.val + 1)))
    FiniteDimensional ℚ K ∧ Module.finrank ℚ K ≤ m := by
  classical
  let K := IntermediateField.adjoin ℚ
    (Set.range (fun j : Fin m => (qExpansion 1 f).coeff (j.val + 1)))
  let Kvalues := IntermediateField.adjoin ℚ (Set.range eigenvalues)
  have hcoeff : ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ K :=
    coefficient_mem_of_first_miller m s hm hs f K
      (fun j => IntermediateField.subset_adjoin ℚ _ ⟨j, rfl⟩)
  have hvalue (p : {p : ℕ // p.Prime}) : eigenvalues p = (qExpansion 1 f).coeff p.val := by
    let : Fact p.val.Prime := ⟨p.property⟩
    have hp₁ : ¬ p.val ∣ 1 := by
      simpa using p.property.not_dvd_one
    have h := primeHecke_qExpansion_coeff p.val (12 * m + s : ℕ) f 1
    rw [heig p, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (eigenvalues p) f,
      PowerSeries.coeff_smul, smul_eq_mul, hnorm] at h
    simpa [hp₁] using h
  have hvalues_le : Kvalues ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    rw [hvalue]
    exact hcoeff _
  have hcoeff_values : ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ Kvalues :=
    coefficient_mem_of_prime_eigenvalues f hnorm eigenvalues heig Kvalues
      (fun p => IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩)
  have hK_le : K ≤ Kvalues := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact hcoeff_values _
  have hfields : K = Kvalues := le_antisymm hK_le hvalues_le
  let x := millerCoefficientEquiv m s hm hs f
  have hx : x ≠ 0 := by
    intro hzero
    let j : Fin m := ⟨0, by omega⟩
    have h := congrFun hzero j
    change millerCoefficientEquiv m s hm hs f j = 0 at h
    rw [millerCoefficientEquiv_apply] at h
    have hbad : (qExpansion 1 f).coeff 1 = 0 := by simpa [j] using h
    rw [hnorm] at hbad
    exact one_ne_zero hbad
  let M : {p : ℕ // p.Prime} → Matrix (Fin m) (Fin m) ℚ := fun p =>
    (integerMillerHeckeMatrix p.val m s).map (Int.castRingHom ℚ)
  have hpair (p : {p : ℕ // p.Prime}) :
      (M p).map (algebraMap ℚ ℂ) *ᵥ x = eigenvalues p • x := by
    let : Fact p.val.Prime := ⟨p.property⟩
    have hcast : (M p).map (algebraMap ℚ ℂ) =
        (integerMillerHeckeMatrix p.val m s).map (Int.castRingHom ℂ) := by
      ext i j
      simp [M]
    rw [hcast, ← millerHecke_conjugacy p.val m s hm hs f, heig p]
    exact (millerCoefficientEquiv m s hm hs).map_smul _ _
  have hdegree := D5.S1.Eigenstructure.CommonEigenvalueFieldDegree.common_eigenvalue_field_degree
    M eigenvalues x hx hpair
  change FiniteDimensional ℚ K ∧ Module.finrank ℚ K ≤ m
  rw [hfields]
  simpa [Kvalues] using hdegree

end
end D5.S3.Arith.ModularForms

#print axioms D5.S3.Arith.ModularForms.normalized_primeHecke_coefficient_field_degree
