import GRH.Lib.Cohomology.Etale.TestRings
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Multivariable Hensel lemma over an absolutely integrally closed local domain. -/

open IsLocalization.Away IsLocalRing MvPolynomial Algebra Localization PreSubmersivePresentation

/-- Hensel's lemma in several variables: over an absolutely integrally closed local domain `A`,
a system `X = p(X)` whose right sides vanish modulo the maximal ideal has a solution in `A`. -/
lemma IsAICLocal.multivariate_hensel {A} [CommRing A] [IsAICLocal A] {ι} [Fintype.{0} ι] {p : ι → _}
    (hp : ∀ i m, (p i).coeff m ∈ maximalIdeal A) : ∃ x : ι → A, ∀ i, x i = aeval x (p i) := by
  let Z := naive (v := X - p) _ Function.injective_id
  have := SubmersivePresentation.isStandardSmoothOfRelativeDimension ⟨(localizationAway
    (Away Z.jacobian) Z.jacobian).comp Z, by simp [smul_def, ↓algebraMap_isUnit]⟩ (tsub_self _)
  obtain ⟨f, hf, ⟨⟨P⟩⟩⟩ := IsEtaleAt.exists_isStandardEtale (R := A) (.comap (liftAlgHom (f :=
    Ideal.Quotient.liftₐ _ (aeval 0) ((RingHom.ker _).span_le.2 (by simp_all [Set.subset_def,
    constantCoeff]))) Z.jacobian (by erw [jacobian_eq_jacobiMatrix_det, (aeval 0).map_det,
    (_ : DFunLike.coe .. = 1)] <;> aesop (add simp [Matrix.one_apply, coeff_pderiv,
    constantCoeff])) : Away Z.jacobian →ₐ[A] ResidueField A) ⊥)
  obtain ⟨⟨a, h, e⟩, l⟩ :=
    (P.hasMap.map (liftAlgHom _ (.mk0 _ hf))).imp_left (IsAIC.exists_root_map_eq P.monic_f)
  exact ⟨_, (by simpa [↓comp_aeval_apply, Z, naive] using congr(((P.lift a ⟨h, by simp_all [← e,
    P.g.aeval_def]⟩).comp P.equivRing.toAlgHom).comp (algHom ..) $(Z.aeval_val_relation ·)))⟩
