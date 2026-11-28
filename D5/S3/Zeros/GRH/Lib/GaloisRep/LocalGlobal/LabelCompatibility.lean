/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LabelCompatibility
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LabelCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.LocalGlobal.LabelCompatibility. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/LocalGlobal/LabelCompatibility.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange.BaseChangeLabel
import D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal.EigencharCompatibility
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Local-global compatibility at tame level, away from and at l. It is treated at
split places only, for sorted tame Iwahori eigencharacters and for depth-zero types induced from a
squarefree type and characters of the determinant. It is stated as polynomials killing Weil or
inertia elements, without local Langlands, and is reduced to the spherical case by cyclic base
change. Source: Harris, Taylor, The geometry and cohomology of some simple Shimura varieties (2001);
Taylor, Yoshida, J. Amer. Math. Soc. 20 (2007); Barnet-Lamb, Gee, Geraghty, Taylor, Local-global
compatibility for l = p, II (2014), Thm 1.1.

This file: Compatibility on inertia for squarefree depth-zero types induced with characters of the
determinant. -/

open NumberField Polynomial Ideal Finset Function Module Fin QZChar Fint
attribute [local simp] roots_prod prod_eq_zero_iff X_ne_C Polynomial.map_prod Units.ext_iff
  prod_ofFn prod_univ_add sum_univ_add Subtype.ext_iff Multiset.prod_nsmul roots_mul

/-- Let r be attached to an eigenform f (standard space, Weil data) with label c, χ_l, t_l at
split w, T injective. Above w, r has finite type, the jumps of κ, and `IsLabelledAt`
holds for c∏(X − x_{χ_l})^{t_l}, with determinants away from ℓ.

Known result: Local-global compatibility at tame level, away from and at l. -/
lemma Attached.isLabelledAt {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E n} [Nonempty n] [Field E] [CMType E]
  [EmbeddedNumberField E] [Fintype n] {κ f P} {r :
  GalRep ℓ E n} {w A hw K} [Field K] [Algebra (ResField w) K] {T} [IsFaithfulMulChar K T] {s
  d c} {χ : Fin s → MulChar (ResField w) ℂ} {t} [WeilData E] (hf : f ∈ (stdSpace E n).forms κ) (he :
  IsEigenform f P) (hr : Attached P r) (h : HasProductLabel f hw T d c χ t) (hA : IsPlaceOver A w) :
  IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (Fintype.card n)) ∧
  IsLabelledAt A T d.factorial (fun s Q ↦ PolyKillsAt r A s Q ∧ (A.valuation
  ℓ = 1 → (r s).1.det = Q.roots.prod)) (c * ∏ l, (X - C (charName T (χ l)).1) ^ t l) := by
  suffices ∀ ⦃σ a⦄ _, _ ∧ _ ∧ _ from .imp_right (⟨·.1, (@this · · · |>.2.2)⟩)
    (this (exists_isTameExponent T hA d).1.choose_spec)
  have (x : K) a := (h.1.root_pow_eq_one (x := x) a).1
  revert h this
  induction' d.factorial using induction_on_primes with p g hp ih generalizing E <;>
    intro ⟨h₁, h₂, h₃, h₄⟩ hq σ a Y@⟨_, hg, hσ, φ, π, _, _, k, hφ, _, hz⟩
  omega
  · obtain ⟨⟨x, v, u⟩, ψ, rfl⟩ := hA.exists_localArtin_eq (inv_mem hσ) 0,
      h₁.exists_eq_prod_of_splits T (by grind [pow_pred_eq_one_iff, card_ResField, w.one_lt_q])
    choose z hz ξ l o hξ using
      exists_sorted_of_detChar (ρ := localFormRep ..) (v_uniformizer w) isUnitary_localFormRep
      (Fintype.equivFin n) (.of_comp (f := (charName T · |>.1)) (g := append ψ χ) (by simpa [←
      separable_prod_X_sub_C_iff])) (m := append 1 t) (by simpa) (x := ⟨f, hf⟩) (by
      simpa [-Units.ext_iff] using! h₄.1) (surjInv_eq _) (by simpa [labelChar_X_sub_C] using! h₄.2)
    choose θ M using hr.exists_det_eq_avatar z.2 (he.of_mem_cyclicSpan hz l.1)
    rw [← congr(map ιℓ.toRingHom $(hξ _ v)).trans (c := Multiset.prod _)]
    simpa +contextual [M, v, hA.valuation_natCast_eq_one_iff, (θ.avatar_localArtin hA · u) ∘ .inl,
      (M.2.1 ..).1 v (.trans congr(rightRegular ℂ _ _ (atSplit hw $(by simp [reindexGL]))
      _) congr($((compactMean_eq_self _ (map_mem_levelSpace_of_commute l.2.1 fun _ ↦
      .map (by ext; simp [mul_comm]) _)).symm.trans (l.2.2 (fun _ ↦ x) monotone_const)).1)),
      torusChar, normAbsChar, Pi.monoidHomMulEquiv] using hr.local_global_of_eigencharacter l
      (he.of_mem_cyclicSpan hz l.1) o hA ⟨_, _⟩ _ 0 (inv_mem hσ) u v
    simp [aroots, Y.pow_apply_charName T v u, Multiset.map_bind, Multiset.map_nsmul]; rfl
  have := Fact.mk hp
  choose μ u _ _ hd hu hb B D G using exists_step_of_local_char hw hA hp (.mk' (.ofAdd <|
    .ofZMod p <| Valued.v ·.1 |>.log) (by simp)) (x₀ := uniformizer w) (by simp [map_eq_zero_iff])
    (by simp [← ofAdd_nsmul, ← map_nsmul]) (by simp +contextual)
  obtain ⟨⟨⟩, H⟩ := (hb u).2 rfl,
    (hA.artinAt_units_trivial_iff_unramified (symmetrise μ)).1 (by simp +contextual [G])
  let w := u.below E
  obtain ⟨a, ⟨j, hj⟩, i, e⟩ := (hA.ramification_in_tower _ B).2.1 H, exists_resField_hom w
    ((algebraMap (𝓞 (stepField μ)) (ResField u)).comp _) fun _ ↦ (algebraMap_ResField_eq_zero.2 ·),
    exists_resField_hom u (φ.comp (algebraMap ..)) (B.centrePrime_liesOver.1 ▸ fun _ ↦ (k ·))
  have hq' : w.q ^ p =
    u.q := by simp [← hd, ← u.ncard_above_mul_ef_eq_finrank, *, absNorm_pow_inertiaDeg]
  algebraize [j, i]
  obtain ⟨⟨⟩, _⟩ := by simpa [← hq', ↓card_ResField, w.one_lt_q.ne'] using
    @natCard_eq_pow_finrank (ResField w) (ResField u) _ _ _ _, IsScalarTower.of_algebraMap_eq
    ((algebraMap_ResField_surjective _).forall.2 (hφ · ▸ hj _ ▸ (e _).symm))
  choose _ n using by simpa using ((charName T).surjective <| .map j.1 <| charName T <| χ ·)
  obtain ⟨⟨f', hf', _, he', hs, hl⟩, hχ⟩ := exists_baseChange_hasLabel hw hu hb (by simp [D]) hj
    hd.symm hf (isChar_of_mem_virtualChars ((lift_labelChar_self T h₁).mul (prod_hom_rel .one fun _
    _ _ ↦ .mul (.rankPart_of_descendsTo (lift_detChar T
    rfl _)))).evalGL_mem_virtualChars) ((shintani_lift_labelChar hp T h₁).mul (prod_hom_rel .one
    fun l _ _ ↦ .mul (.rankPart_of_descendsTo (lift_detChar T (n _) _)))) h₄, h₂.map (f := j)
  simp [w, pow_mul, hq', ← (c * _).aroots_map K (S := ResField u), ← c.aeval_map_algebraMap
    (ResField u), ← n, j.algebraMap_toAlgebra, -FinPlace.q_bounds] at hg hz hq hχ ⊢
  exact (sphericalCompat_std u hf' he').1.rec fun _ r ↦
    ((hs.exists_attached_descent r he' he).2.1 hr A).rec fun a ⟨b, d⟩ ↦ .imp a (.imp (b _) ((d ⟨σ,
    H hσ, (hA.artinAt_trivial_iff_decompGroup_le _).1 D hσ.1⟩).rec fun d e ↦ .imp (e _) (d ▸ ·)))
    (ih hf' he' r B ⟨h₁.map _, hχ, h₃, hl⟩ hq ⟨B, hg.2, hσ, φ, algebraMap _ _ π, _, _, k,
    (e · ▸ rfl), by simp [w, B.isUniformiser_iff, hA.isUniformiser_iff.1, *, w.3,
    ← w.valuation_liesOver _, ramificationIdx'_eq_ramificationIdx], hz⟩)
