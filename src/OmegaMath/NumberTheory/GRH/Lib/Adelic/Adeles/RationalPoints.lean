import OmegaMath.NumberTheory.GRH.Lib.Adelic.Unitary.SpaceDefs
import OmegaMath.NumberTheory.GRH.Lib.General.Analysis.FundamentalDomain
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus
(known result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: Number field is a discrete cocompact lattice of covolume one in its adeles. Relative
different and discriminant of CM fields with 5040th roots; trace, norm, real embedding. Rational
points embed injectively and discretely in the adelic unitary group. -/

open NumberField InfinitePlace Algebra Classical Finset MeasureTheory Metric IsCMField
  IsTotallyComplex IsTotallyReal

variable {E : Type*} [Field E] [PlaceEmbedding E]

lemma Φ_eq_or (φ : E →+* ℂ) : Φ (.mk φ) = φ ∨ star (Φ (.mk φ)) = φ := mk_eq_iff.1 (mk_Φ _)

variable (E) [NumberField E] (m n : Type*) {B I} [AddCommGroup B] [AddCommGroup I]
  [TopologicalSpace B] (f : I →+ B) (C : Set B) [MeasureSpace B]

/-- The image of E in its adeles under the diagonal embedding, as an additive subgroup. -/
noncomputable def ratAdeles := toAdele (E := E).toAddMonoidHom.range

/-- The additive subgroup of adelic vectors indexed by n that is the image of E^n under the
coordinatewise diagonal embedding. -/
noncomputable def ratVectors (n : Type*) := (toAdele (E := E).toAddMonoidHom.compLeft n).range

/-- The additive subgroup of m×n adelic matrices that is the image of the m×n matrices over E
under the entrywise diagonal embedding. -/
noncomputable def ratMatrices := toAdele (E := E).toAddMonoidHom.mapMatrix (m := m) (n := n).range

/-- C is compact and contains a measurable set D of volume one such that every x in B has
exactly one a in I with f(a) + x in D. -/
def HasFundDomain := IsCompact C ∧ ∃ D ⊆ C, MeasurableSet D ∧ volume D = 1 ∧ ∀ x, ∃! a, f a + x ∈ D

/-- A lattice of covolume one: a discrete subgroup Λ of B whose translates of one compact set
cover B, with B/Λ compact and of quotient measure one. -/
class IsCovolOneLattice (Λ : AddSubgroup B) extends DiscreteTopology Λ, CompactSpace (B ⧸ Λ),
    IsProbabilityMeasure Λ.qms where exists_compact_cover (Λ) : Λ.Cocpt

variable {E n}

lemma mem_ratVectors {x} : x ∈ ratVectors E n ↔ ∀ i,
  x i ∈ ratAdeles E := by simp [ratVectors, ratAdeles, funext_iff, skolem]

lemma mem_ratMatrices {m n : Type*} {x} : x ∈ ratMatrices E m n ↔ ∀ i j, x i j ∈ ratAdeles E := by
  simp [ratMatrices, ratAdeles, ← Matrix.ext_iff, skolem]; rfl

@[simp, grind .] lemma toAdele_half_add_half : toAdele (2⁻¹ :
  E) + toAdele 2⁻¹ = 1 := by norm_num [← map_add]

@[grind .] lemma toAdele_inv_mul_cancel {x} : x ≠ 0 → x⁻¹ * toAdele (x :
  E) = 1 := by simp_all [← map_mul]

variable {f C} [Fintype n] [IsTopologicalAddGroup B] [SecondCountableTopology B]
  [T2Space B] [LocallyCompactSpace B] [(@volume B _).IsAddHaarMeasure] [IsTotallyComplex E]

omit [T2Space B] in
lemma HasFundDomain.pi : HasFundDomain f C → HasFundDomain (f.compLeft n) (.pi .univ fun _ ↦ C)
  | ⟨_, _, _, m, _, h⟩ => ⟨isCompact_univ_pi (by tauto), _, by gcongr, .univ_pi fun _ ↦ m,
    by simp_all [volume], (.imp (by simp; grind) <| skolem.1 <| h ∘' ·)⟩

/-- Let f: I → B be additive, B a second countable locally compact abelian group with Haar
measure. If a compact set contains a measurable D of volume one whose translates by the
f(a), a in I, partition B, then f(I) is a lattice of covolume one. -/
lemma HasFundDomain.isCovolOneLattice [BorelSpace B] :
    HasFundDomain f C → IsCovolOneLattice f.range :=
  fun ⟨c, D, s, m, v, h⟩ ↦
  have := discreteTopology_of_isOpen_singleton_zero ((⊥ : AddSubgroup f.range).isOpen_of_mem_nhds
    ((nhds_induced _ 0).le ⟨_, volume.sub_mem_nhds_zero_of_addHaar_pos D m (by aesop),
    fun ⟨_, a, rfl⟩ ⟨x, _, y, _⟩ ↦ by simp_all [sub_eq_iff_eq_add, (h y).unique (y₂ := 0)]⟩))
  @.mk _ _ _ _ _ _
    ⟨(top_unique (h ·.out |>.rec (by aesop))).subst (c.image_auto QuotientAddGroup.mk)⟩
  ⟨lintegral_one ▸ (lintegral_congr (h · |>.rec fun a _ ↦ by
    simp; rw [tsum_eq_single ⟨_, a, rfl⟩] <;> simp_all [f.range.vadd_def]; grind)).trans
  ((lintegral_addOrbitMeasure_lintegral
  (measurable_one.indicator m)).trans (by aesop))⟩ ⟨C, c, (h · |>.rec (by tauto))⟩

/-- For totally complex E with chosen embeddings Φ, some measure-preserving ℝ-linear isomorphism
from Minkowski space to ℂ^{infinite places} sends the mixed embedding of each x in E to
(Φ_w(x))_w. -/
lemma exists_mixedEquiv : ∃ e : _ ≃ₗ[ℝ] _, MeasurePreserving e ∧ ∀ x, e (mixedEmbedding E x) =
  (Φ · x) := have := Fintype.card_eq_zero_iff.1 (nrRealPlaces_eq_zero E)
  ⟨.uniqueProd ≪≫ₗ .funCongrLeft .. ≪≫ₗ .piCongrRight _, (volume_preserving_pi fun v ↦ (ite
    (v.embedding = _) 1 Complex.conjLIE).measurePreserving).comp ((volume_preserving_arrowCongr'
    (.subtypeUnivEquiv isComplex) (.refl _) (.id _)).comp ⟨measurable_snd, by simp [volume]⟩), by
    intro; ext v; have := (mk_Φ v ▸ embedding_mk_eq _).resolve_left; aesop⟩

/-- Let K be a number field, e a volume-preserving linear isomorphism from its Minkowski space
to V, j the diagonal map K → V × 𝔸_f. For some R > 0, the closed R-ball times Ô is compact
and contains a fundamental domain of volume one for j (`HasFundDomain`). -/
lemma exists_hasFundDomain {K V} [NormedRing V] [NormedSpace ℝ V] [ProperSpace V] [MeasureSpace V]
    [BorelSpace V] [Field K] [NumberField K] (φ : K →+* V)
    (h : ∃ e : _ ≃ₗ[ℝ] V, MeasurePreserving e ∧ ∀ a, e (mixedEmbedding K a) = φ a) :
    ∃ R > 0, HasFundDomain (φ.prod (algebraMap K _)).toAddMonoidHom (closedBall 0 R ×ˢ Ô K) :=
    (exists_fundDomain_prod _ (Ô K).toAddSubgroup 1 (by simp [@IsIntegralClosure.isIntegral_iff
  (𝓞 K)]) exists_sub_mem_Ô h).elim fun _ ⟨m, b, v, u⟩ ↦ (b.subset_closedBall_lt 0 0).imp fun _ r ↦
  ⟨r.1, (isCompact_closedBall ..).prod isCompact_Ô, _, by grind, m.prod isOpen_Ô.measurableSet, by
    simp [← ENNReal.toReal_eq_one_iff, Measure.volume_eq_prod, volÔ, field, discr_ne_zero, v], u⟩

/-- For E totally complex there is R > 0 such that the compact set (closed ball of radius R in
ℂ^f) × Ô contains a measurable fundamental domain of volume one for E acting on its adeles
by translation. -/
lemma exists_hasFundDomain_toAdele : ∃ R > 0, HasFundDomain toAdele.toAddMonoidHom
  (closedBall 0 R ×ˢ Ô E) := exists_hasFundDomain _ exists_mixedEquiv

/-- The field E is a lattice of covolume one in its adeles. -/
instance isCovolOneLattice_ratAdeles : IsCovolOneLattice (ratAdeles E) :=
  exists_hasFundDomain_toAdele.choose_spec.2.isCovolOneLattice

instance isCovolOneLattice_ratVectors : IsCovolOneLattice (ratVectors E n) :=
  exists_hasFundDomain_toAdele.choose_spec.2.pi.isCovolOneLattice

variable {m} [Fintype m] in
instance instLatMatrix𝔸RatM : IsCovolOneLattice (ratMatrices E m n) :=
  exists_hasFundDomain_toAdele.choose_spec.2.pi.pi.isCovolOneLattice

omit [SecondCountableTopology B] [LocallyCompactSpace B] [(@volume B _).IsAddHaarMeasure] in
lemma IsCovolOneLattice.finite_preimage (k : IsCompact C) (h : IsCovolOneLattice f.range) (i :
  (⇑f).Injective := by simp [injective_iff_map_eq_zero, funext_iff, ← Matrix.ext_iff]) : (f ⁻¹'
  C).Finite := by simpa using f.tendsto_coe_cofinite_of_isDiscrete i ⟨h.1⟩ k.compl_mem_cocompact

section

variable [StarAddMonoid B] [ContinuousStar B] {E : Type*} [Field E] [NumberField E] [IsCMField E]

instance : @IsClosed B _ (selfAdjoint B) := isClosed_fixedPoints (by fun_prop)

lemma mem_maximalRealSubfield_iff_star_eq {x} : x ∈ maximalRealSubfield E ↔ star x = x :=
  (complexConj_eq_self_iff ..).symm

lemma pair_complexConj_eq_univ : {1, complexConj E} = univ := by simp [eq_univ_of_card, ←
  IsGalois.card_aut_eq_finrank, ← (isQuadraticExtension E).2, (complexConj_ne_one E).symm]

lemma trace_maximalReal_eq_add_star (x : E) : trace (maximalRealSubfield E) E x = x + star x :=
    (trace_eq_sum_automorphisms x).trans
  (pair_complexConj_eq_univ.rec (sum_pair (complexConj_ne_one E).symm))

lemma norm_maximalRealSubfield_eq_mul_star (x : E) : norm (maximalRealSubfield E) x = x * star x :=
    (norm_eq_prod_automorphisms ..).trans
  (pair_complexConj_eq_univ.rec (prod_pair (complexConj_ne_one E).symm))

/-- If the CM field E satisfies `StablyUnram`, the relative different of E over its maximal real
subfield E⁺ is the unit ideal. -/
@[simp] lemma differentIdeal_eq_top [StablyUnram E] : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞
  E) = ⊤ := StablyUnram.exists_isUnit_sub_star.elim fun y ↦ Ideal.eq_top_of_isUnit_mem _
  (RingOfIntegers.coe_injective.mem_set_image.1 ((coeSubmodule_differentIdeal _ (maximalRealSubfield
  E) _).ge fun x k ↦ (skolem.1 (k _ <| Submodule.algebraMap_mem ·)).elim fun t h ↦ ⟨t y • 1 -
  t 1 • 1 * star y,
  .trans congr(($(h y) - $(h 1) * _) * _) (by simp [trace_maximalReal_eq_add_star]; ring!)⟩))

lemma abs_discr_eq_discr_sq [StablyUnram E] : |discr E| = discr (maximalRealSubfield E) ^ 2 :=
  Int.abs_eq_natAbs _ ▸ by simp [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
  (maximalRealSubfield E) (𝓞 (maximalRealSubfield E)) E (𝓞 E), (isQuadraticExtension E).2]

lemma volÔ_eq : volÔ E = ((rootDiscr E / 2) ^ numInfPlaces E)⁻¹ := by simp [volÔ, Norm.norm,
           abs_discr_eq_rootDiscr_pow, card_eq_nrRealPlaces_add_nrComplexPlaces, div_pow,
  (rootDiscr_pos E).le]

/-- There is a measure-preserving real-linear isomorphism from the Minkowski space of E⁺ to real
functions on the infinite places of E, sending the image of a in E⁺ to v ↦ Re Φ_v(a), Φ the
CM type. -/
lemma exists_mixedEquiv_maximalReal {E : Type*} [Field E] [CMType E] :
    ∃ e : _ ≃ₗ[ℝ] _, MeasurePreserving e ∧ ∀ a, e
    (mixedEmbedding (maximalRealSubfield E) a) = (Φ · a.1 |>.re) :=
  have := Fintype.card_eq_zero_iff.1 (nrComplexPlaces_eq_zero (maximalRealSubfield E))
  ⟨.prodUnique ≪≫ₗ .funCongrLeft .., (volume_measurePreserving_piCongrLeft _ ((equivInfinitePlace
    E).trans (.symm (.subtypeUnivEquiv isReal)))).symm.comp ⟨measurable_fst, by simp [volume]⟩,
    fun _ ↦ by ext; simpa [← comap_mk] using! congr(($(embedding_mk_eq_of_isReal
      (complexEmbedding_isReal ((Φ _).comp _))) _).re)⟩

instance : Nontrivial (𝔸f E) := (evalAt (IsDedekindDomain.HeightOneSpectrum.equivMaximalSpectrum
    (RingOfIntegers.not_isField E)).nonempty.some).domain_nontrivial

end

variable [BorelSpace B]

variable [StarAddMonoid B] [ContinuousStar B] {E : Type*} [Field E] [CMType E] {n : Type*}
  [Fintype n] {s} (V : Space E n s)

lemma Space.mat_ratEmbed γ : (V.ratEmbed γ).mat = V.x⁻¹ * γ.1.1.map toAdele * V.x := rfl

/-- For a space (J, x), the finite part x_f of x, in GL_n(𝔸_f). -/
@[local simp] noncomputable def Space.xFin := V.x.map (.snd ..)

lemma Space.coe_embFin γ :
    V.embFin γ = V.xFin⁻¹ * .map (algebraMap ..) γ.1 * V.xFin := by erw [Subtype.coe_mk]; aesop

@[simp] lemma stdSpace_embFin γ : ((stdSpace E n).embFin γ).1 =
  .map (algebraMap E _) γ := by simp [Space.coe_embFin]

namespace Space

instance fact_embFin_injective : Fact (Function.Injective V.embFin) :=
    ⟨by simp [Function.Injective, Gf.val_ext_iff, coe_embFin, Matrix.GeneralLinearGroup.ext_iff]⟩

lemma ratEmbed_injective : Function.Injective V.ratEmbed :=
  .of_comp (f := Prod.snd) V.fact_embFin_injective.1

/-- The rational points Γ of the unitary group form a discrete subgroup. -/
instance discreteTopology_Gamma : DiscreteTopology V.Γ := .of_continuous_injective (f := fun g ↦
  (⟨V.toRatCoords g, g.2.rec (⟨·, by simp [← ·, ratEmbed, U.map]⟩)⟩ : ratMatrices E n n))
  (by simp [toRatCoords, G.toUnitary, mkAdelicGL]; fun_prop) (by simp [Function.Injective,
  Units.val_inj])

instance {S} : DiscreteTopology (Subgroup.map V.ratEmbed S) :=
  .of_subset V.discreteTopology_Gamma (S.map_le_range _)
