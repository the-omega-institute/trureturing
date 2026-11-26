import GRH.Lib.General.Algebra.AdicRingHomExt
import GRH.Lib.ClassField.Places.LocalExtension
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Prime induced by a p-adic embedding; extension to the completion and finite adeles.
Unique unramified character with given value at Frobenius; uniform local constancy. -/

open ComplexConjugate IntermediateField IsDenseInducing Module NNReal NormedField NumberField
  Valuation Valued

variable {E : Type*} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] {F : Type _} [NormedField F]
  [IsUltrametricDist F] [CharZero F] [PadicField F p] (σ : E →+* F) {x : 𝔸f E}

section

omit [CharZero F]

lemma norm_le_one_of_isIntegral {R} [CommRing R] (ι : R →+* F) {x} : IsIntegral ℤ x → ‖ι x‖ ≤ 1 :=
    ((integer.integers (valuation.comap ι)).mem_of_integral ·.tower_top)

omit [NumberField E] in
lemma norm_ringOfIntegers_le (x : 𝓞 E) : ‖σ x‖ ≤ 1 := norm_le_one_of_isIntegral _ x.2

/-- The prime of E above p induced by an embedding σ of E into an ultrametric normed field F
over ℚ_p: the integers x of E with ‖σ x‖ < 1. -/
noncomputable def placeOfEmb : FinPlace E := ⟨centrePrime E (valuation.comap σ).valuationSubring,
  .comap _, (NeZero.ne ↑p <| ·.le ((mem_maximalIdeal_iff ..).2 (by simpa using! norm_p_lt_one)))⟩

lemma isEquiv_placeOfEmb : (valuation.comap σ).IsEquiv ((placeOfEmb σ).valuation E) :=
    (isEquiv_valuation_valuationSubring _).trans (IsPlaceOver.of_le_centrePrime le_rfl).isEquiv

/-- An integer x of the number field E lies in the prime `placeOfEmb` σ induced by an embedding σ
of E into an ultrametric normed field over ℚ_p if and only if ‖σ x‖ < 1. -/
@[simp] lemma mem_placeOfEmb x : x ∈ (placeOfEmb σ).1 ↔ ‖σ x‖ < 1 := mem_maximalIdeal_iff ..

end

attribute [irreducible] placeOfEmb

/-- The ring homomorphism from ℂ to ℂ_p obtained by composing an isomorphism ι from ℂ onto the
algebraic closure of ℚ_p with the inclusion into ℂ_p. -/
noncomputable abbrev complexToCp (ι : ℂ ≃+* PadicAlgCl p) := (algebraMap _ ℂ_[p]).comp ι.toRingHom

/-- The prime of E above p induced by the complex embedding σ followed by the isomorphism ιℓ
from ℂ to the algebraic closure of ℚ_p. -/
noncomputable abbrev inducedPrime [PadicIso p] (σ : E →+* ℂ) := placeOfEmb (ιℓ.toRingHom.comp σ)

omit [CharZero F] in
/-- The rational prime p lies in the prime of E induced by an embedding σ of E into an
ultrametric normed field F over ℚ_p. -/
@[simp high] lemma natCast_mem_placeOfEmb : ↑p ∈ (placeOfEmb σ).1 := by simp [norm_p_lt_one]

instance instFiniteDimensionalPadicSubtypeMemIntermediateFieldAdjoinRangeCoeRingHom_new
    : FiniteDimensional ℚ_[p] (adjoin ℚ_[p] (.range σ)) := rank_lt_aleph0_iff.1 (let :=
  σ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional
  (σ.toRatAlgHom.fieldRange.adjoin_rank_le_of_isAlgebraic_right _).trans_lt (rank_lt_aleph0 ..))

/-- An embedding σ of E into an ultrametric normed field over ℚ_p extends to a continuous
homomorphism φ on the completion at the induced prime, with values in ℚ_p(σ(E)) and ‖φ(x)‖ ≤
‖φ(y)‖ exactly when v(x) ≤ v(y). -/
lemma exists_placeOfEmb_extension : ∃ φ : LocField (placeOfEmb σ) →+* F, Continuous φ ∧
  (∀ x, φ (algebraMap E _ x) = σ x) ∧ (∀ x, φ x ∈ adjoin ℚ_[p] (.range σ)) ∧
  (valuation.comap φ).IsEquiv v := let := FiniteDimensional.complete ℚ_[p]
  have ⟨c, hc, h⟩ := (place (algebraMap E (LocField (placeOfEmb σ)))).isEquiv_iff_exists_rpow_eq
    (w := place σ).1 (by simpa [v_algebraMap_eq_valuation] using! (isEquiv_placeOfEmb σ).symm ·)
  let := SeminormedRing.induced E _ (FinitePlace.embedding (placeOfEmb σ))
  have u := uniformContinuous_of_tendsto_zero (f := σ.codRestrict (adjoin ℚ_[p] (.range σ))
    (by aesop)) (squeeze_zero_norm h.ge (tendsto_norm_zero.rpow_const_nhds_zero hc))
  have D := (placeOfEmb σ).denseRange_algebraMap E
  have := (uniformContinuous_uniformly_extend ⟨rfl⟩ D u).continuous
  ⟨(algebraMap ..).comp (extendRingHom ⟨rfl⟩ D u), by have := D.eq ?_ this.norm (.rpow_const
    (p := c) continuous_norm (by grind)) <;> simp_all [extendRingHom, extend_eq, u.continuous,
    funext_iff, Valuation.IsEquiv, ← coe_le_coe, Real.rpow_le_rpow_iff]; fun_prop⟩

/-- The ring homomorphism from the finite adeles of E to F: the component at the prime induced
by σ : E → F, followed by a continuous extension of σ to the completion. -/
noncomputable def adeleExtension := (exists_placeOfEmb_extension σ).choose.comp (evalAt _)

@[simp] lemma adeleExtension_algebraMap (x : E) : adeleExtension σ x = σ x :=
  (exists_placeOfEmb_extension σ).choose_spec.2.1 x

@[fun_prop] lemma continuous_adeleExtension :
  Continuous (adeleExtension σ) := (exists_placeOfEmb_extension σ).choose_spec.1.comp (by fun_prop)

lemma norm_adeleExtension_eq_iff y : ‖adeleExtension σ x‖ = ‖adeleExtension σ y‖ ↔
  v (x (placeOfEmb σ)) = v (y (placeOfEmb σ)) := coe_inj.trans
  (exists_placeOfEmb_extension σ).choose_spec.2.2.2.eq_iff

lemma norm_adeleExtension_le_one : x ∈ Ô E → ‖adeleExtension σ x‖ ≤ 1 :=
    (exists_placeOfEmb_extension σ).choose_spec.2.2.2.le_one_iff_le_one.2 ∘ (mem_Ô.1 · _)

variable [IsCMField E] {Γ Ω k : Type _} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω]
  [Algebra k Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [L : IsLocalGalois Γ k A]

omit [CharZero F] in
lemma placeOfEmb_comp_star : placeOfEmb (σ.comp conj) = star (placeOfEmb σ) := by aesop

/-- For a CM field E, the extension `adeleExtension` σ of a p-adic embedding σ to finite adeles
takes at the conjugate of x the value that the extension of σ ∘ conj takes at x. -/
lemma adeleExtension_star : ∀ x, adeleExtension σ (star x) = adeleExtension (σ.comp conj) x :=
  denseRange_algebraMap_finAdele.eq

variable {E : Type*} [Field E] [CMType E] {F : Type _} [NormedField F] [IsUltrametricDist F]
  [CharZero F] in
/-- For an infinite place v and ι : ℂ → F, the embedding x ↦ ι(Φ_v(x̄)) of E in F, with Φ the CM
type. -/
noncomputable abbrev weightEmbedding (ι : ℂ →+* F) v :=
  (ι.comp (Φ v)).comp (starRingEnd E)

/-- For a profinite group Γ, a compact space Y, a discrete space X and a continuous f : Γ × Y →
X, there is an open normal subgroup U of Γ with f(u, y) = f(1, y) for all u in U and all y. -/
lemma exists_openNormalSubgroup_apply_eq {Y X} [IsProGalois Γ k Ω] [TopologicalSpace Y]
  [CompactSpace Y]
  [TopologicalSpace X] [DiscreteTopology X] {f : Γ × Y → X} (hf : Continuous f) : ∃ U :
  OpenNormalSubgroup Γ, ∀ u ∈ U, ∀ y, f (u, y) = f (1, y) := by simpa [Set.subset_def]
  using ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isClosedMap_fst_of_compactSpace
  _ ((isClosed_discrete (.offDiag ⊤)).preimage (f := fun p ↦ (f p, f (1, p.2))) (by fun_prop))).1

/-- Let Γ be the absolute Galois group of a local field k and φ an arithmetic Frobenius. For
every r in ℚ/ℤ there is exactly one continuous character χ : Γ → ℚ/ℤ that is trivial on
inertia and has χ(φ) = r. -/
lemma existsUnique_unramified_char {φ} (hφ : IsFrob A (residueCard k A) φ) r :
    ∃! χ : QZChar Γ, (∀ g ∈ inertiaGroup Γ A, χ.1 g = 0) ∧ χ.1 φ = r := have := L.6
  let N : ℕ+ := ⟨residueCard k A ^ addOrderOf r - 1, by simp [this.one_lt_card, r.isAddTorsion]⟩
  have hN : A N = 1 := by simp [N, map_sub_eq_of_lt_right, pow_lt_one', r.isAddTorsion,
    valuation_residueCard_lt_one]
  (QZ.exists_extend (zmultiplesHom _ (Additive.ofMul (cycCharMod Ω N φ))) (zmultiplesHom _ r) (by
    simpa [Nat.dvd_iff_mod_eq_zero, Nat.sub_eq_iff_eq_add NeZero.one_le, N, this.one_lt_card.ne',
    ↓zmultiplesHom_ker_eq, Int.mem_zmultiples_iff, Int.ofNat_dvd] using! (((hφ.pow (orderOf
      (cycCharMod Ω N φ))).mem_ker_cycCharMod_iff hN).1 (by simp)).symm.dvd')).rec fun e he ↦
    .imp (fun b h ↦ ⟨h, fun ⟨_, a, _⟩ _ ↦ Subtype.ext ((L.frobenius_spec.2.1 hφ).equalizer a b.2.1
    (by ext ⟨n⟩; induction n <;> simp_all [pow_add, b.2.2]))⟩) ⟨⟨(e ∘ .ofMul) ∘ cycCharMod Ω N,
    .comp (by fun_prop) (.of_isOpen_ker _ Fact.out), by simp⟩,
    by simpa +contextual [cycCharMod_of_mem_inertiaGroup _ hN] using he 1⟩
