/- GID: D5/S3/Zeros/GRH/Lib/Shimura/ThetaGroup/RigidFibres
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/ThetaGroup/RigidFibres
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.ThetaGroup.RigidFibres. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/ThetaGroup/RigidFibres.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.LiftedIsogenies
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: the theta group of an ample line bundle, with the span of sections, K(L) and
symmetric theta structures. Here it is stated for a given system of coordinates with a Heisenberg
law of odd order over a local ring. Spanning of the sections is proved by reduction from the complex
numbers, not by Riemann–Roch, and only the consequences for K(L) and uniqueness are drawn. Source:
D. Mumford, On the equations defining abelian varieties I, Invent. Math. 1 (1966), §§1–2; S. W.
Shin, Abelian varieties and Weil representations, Algebra Number Theory 6 (2012), Prop. 2.12 (over a
base); M. Bolognesi, A. Massarenti, Comment. Math. Helv. 91 (2016), Lemma 4.1 (odd type).

This file: Theta coordinates span the sections on fibres of a modelled abelian scheme. -/

open CategoryTheory AlgebraicGeometry Submodule LineBundle Set Nat IsLocalRing Spec
attribute [local simp] H0_smul ValuativeArc.genericPt_eq
attribute [local simp ←] Over.comp_left map_nsmul

/-- Rigidity of geometric fibres: if an object y over a valuation ring O with fraction field ℂ
is modelled on a complex torus, every pull-back of y along a homomorphism from O to an
algebraically closed field satisfies `ThetaObject.IsRigid`.

Known result: Theta group of an ample line bundle: span of sections, K(L), symmetric theta
structures. -/
lemma ThetaObject.TorusModel.isRigid_pullback {E O W} [Field E] [CMBase E] [CommRing O]
    [ValuativeArc O] [FinComplexSpace W] {D : PEL E} {Z τ} {X : ThetaFamily D Z τ} {y :
  ThetaObject X (Spec ⟨O⟩)} {g ℓ} {Y : PeriodMap D g ℓ W} (a :
  y.TorusModel Y) {k} [Field k] [IsAlgClosed k] (χ : O →+* k) {x₀ : ThetaObject X _}
  (h : specMap χ ≫ y = x₀) : x₀.IsRigid := fun B _ _ _ x ↦ map_surjective.forall.2 fun ϕ g ↦ by
  obtain ⟨h : x.IsPullbackAlong _ y, C, m, hN⟩ := (map_comp_assoc ..).trans (h ▸ g),
    hasConstFunctions_of_isPullback g.isGroupBaseChange.1, (eventually_span_coordSection
    x.groupScheme x₀.isProjEmbedding g.isGroupBaseChange.1).exists_forall_of_atTop
  have ⟨c, P, e⟩ : ∃ c > m, (c : k) ≠ 0 := by by_contra!; simpa [*] using @cast_succ k _ m.succ
  let M {S} (x : ThetaObject X S) := x.lineBundle.pull (c • 𝟙 x.groupScheme).1
  let Λ {R} [CommRing R] x := pullSections (.id R) (by simp) (refl (M x))
  let Q := pullSections _ h.schemeMap.w (by simp [M, h.lineBundle_eq_pull, ← pull_comp _,
    h.isGroupBaseChange.nsmul_id_comp] : M x = .pull (M y) _)
  obtain ⟨hΦ, hR, N⟩ := (isSectionLift_pullSections ..).comp (Θ := Q) (exists_isSectionLift (L :=
    .pow _ _) (𝟙 _) (picClass_pow .. ▸ pull_nsmul_eq_sq_smul y.hasClassLaws.1 c)).choose_spec,
    a.uniformisation.card_torsion P.ne_zero, P.ne_zero
  obtain ⟨⟨_, h'⟩, F, ⟨⟩⟩ := exists_isSectionLift (𝟙 _) (L := M x) hΦ.picClass_eq.symm,
    (equivFinOfCardPos (hR.trans_ne
    (by simp [N]))).symm, by exact_mod_cast x.finite_flat_surjective_smul (cast_ne_zero.2 N)
  let τ {B} [CommRing B] {x} (j : _ →+ _) := ∑ z, pullSections (.id B) (by simp) (by simp [M,
    ← pull_comp _, ← comp_nsmul _, (F z).2] : M x = (M x).pull (translation (j (F z).1)).1)
  refine ⟨C, top_unique fun σ _ ↦ (smul_mem_iff_of_isUnit _ ((e.isUnit.map ϕ.1).pow _)).1
    ((apply_mem_span_image_iff_mem_span (isSectionLift_pullSections ..).injective).1 (Eq.subst (by
    ext; simp [τ, Λ, ← comp_nsmul _, (F _).2, *]; rfl) (mem_comap.1 ((h'.injective.mem_set_image
    (a := Λ x σ)).1 (span_le.2 (range_subset_iff.2 fun j ↦
    (((isSectionLift_pullSections _ h.schemeMap.w rfl).exists_eq_smul C (h'.comp hΦ)).choose_spec
    (coordSection (a.hasThetaCoords.pow _).1 j)).symm.subst (smul_mem _ _ (mem_map_of_mem ((fun θ ↦
    by_contra fun hσ : τ h.isGroupBaseChange.pullSection (Q θ) ∉ span B (Λ x '' _) ↦ ?_) _))))
    ((h.lineBundle_pow_eq_pull _ ▸ g.lineBundle_eq_pull ▸
    hN (c ^ 2) (by nlinarith)) ((a.hasThetaCoords.pow _).1.pull _) ▸ ⟨⟩))))))⟩
  let ω := τ (.id _) θ; let v z := a.uniformisation.expMap ((c : ℂ)⁻¹ • z)
  have hv z : c • v z = a.uniformisation.expMap z := by simp [v, ← cast_smul_eq_nsmul ℂ, N]
  have J z : atGeneric v z ≫ (c • 𝟙 y.groupScheme).1 =
    atGeneric a.uniformisation.expMap z := by simp [atGeneric, ← hv]
  have s := a.hasThetaCoords.pull 1 (J · |>.symm) fun _ ↦ id
  obtain ⟨r, _, _⟩ := by simpa using (s.exists_theta_of_isSection (s.pow 0) (w :=
    (ω.1 ·.1)) (by simpa [IsSection, LineBundle.pow, inf_of_le_left] using! ω.2.1) (fun _ ↦
    (a.uniformisation.immersive _).1.comp (by fun_prop)) fun l _ _ _ ↦
    by simp [ω, τ]; apply Fintype.sum_equiv (F.symm.permCongr (.subtypeEquiv (.addLeft (v l)) _))
    <;> simp_all [v, atGeneric, add_assoc])
  have K (w : span O (range (coordSection a.hasThetaCoords.1))) b (p : ∀ i,
    _ := by simp +contextual [Λ, M, a.hasThetaCoords.4 .., *] <;> simp [atGeneric,
    field, *]) := have H : Λ y w = b • ω := H0_ext fun {i} ↦ ((isSeparatingFamily_atGeneric (s :=
      v) (a.uniformisation.4.comp (MulAction.surjective₀ (by simpa)))).pointFn_ext · · (p i))
    (⟨(residue_eq_zero_iff b).2 fun z ↦ hσ (Eq.subst (a := Q ω) (by ext; simp [Q, ω, τ,
      h.isGroupBaseChange.translation_comp]) (mem_comap.1 ((smul_mem_iff_of_isUnit _ z).1
      (((Λ y).map_span_le ..).2 (by simp [Λ, Q, pullSections_coordSection, mem_span_of_mem,
      ← range_comp', ↓forall_mem_range]) ⟨_, w.2, H⟩)))), H⟩ : _ ∧ _)
  obtain ⟨γ, _, n, p, G⟩ := exists_sections_of_translation_stable _ a.hasThetaCoords
    y.obj_isThetaStructure.4 a.exists_isTranslationLift_of_dualLattice (by bound)
    (by tauto) () (by simpa [·] using K 0 1)
  obtain ⟨g, e⟩ | ⟨g, e⟩ := ValuationRing.isInteger_or_isInteger O γ
  exact (K (n 0) g).elim fun k e ↦ G _ (_ ≫ (y.levelPoints 0).1) fun z _ _ i ↦ by
    simpa [Λ, hv, k] using congr($e.1 i _ (specMap (residue O) ≫ (v z).1))
  simpa using K (g • n 0) 1
