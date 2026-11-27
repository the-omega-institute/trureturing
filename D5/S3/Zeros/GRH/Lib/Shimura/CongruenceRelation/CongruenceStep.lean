/- GID: D5/S3/Zeros/GRH/Lib/Shimura/CongruenceRelation/CongruenceStep
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/CongruenceRelation/CongruenceStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.CongruenceRelation.CongruenceStep. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/CongruenceRelation/CongruenceStep.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.IntegralModel.UniversalPoints
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: the pointwise step of the Eichler–Shimura congruence relation for GU(1,n−1) at a
split place. Only the geometric step is treated, namely that at each geometric point of the special
fibre the Frobenius-twisted Hecke neighbour of a subspace depends only on its sum with one fixed
non-zero subspace. No ordinary locus is used, and the Möbius sum is taken with the model. Source:
Wedhorn, Congruence relations on some Shimura varieties, J. reine angew. Math. 524 (2000) 43–71; for
the method, Katz–Mazur 1985 ch. 13, Harris–Taylor 2001 III.4; for Weisner's theorem, Stanley, EC1
Cor. 3.9.3.

This file: Frobenius-twisted reduced Hecke neighbours of A depend only on A + W, some W ≠ 0. -/

open Matrix _root_.Module ThetaObject AddSubgroup AlgebraicGeometry CategoryTheory FiniteField
  IsGroupBaseChange QuadField NumberField Pic CartesianMonoidalCategory Category Over

/-- Let β = (1 + √−d₀)/2, let z and its Hecke neighbours z·g_A (A ⊆ k_wⁿ a subspace) have
V-points s, α(A), and let V → k be onto an algebraically closed field, with s reducing above
a safe, good split place w of norm q. Then for some subspace W ≠ 0, Frob_q^{n−dim A} of the
reduction of α(A) depends only on A + W.

Known result: Eichler–Shimura congruence relation for GU(1,n−1) at a split place: the pointwise
step. -/
lemma UniversalFamily.congruence_step {E k d d₀} [Field E] [CMBase E] {D R} [HasQuadSubfield d₀ E]
  (U : UniversalFamily D R) (hβ : D.β = algebraMap _ _ (c₀ d₀)) {V : ValuationSubring ℂ} {z :
  ModuliPoint E D.Index d} {s} (o : U.family.IsPointOf 1 z s) {w : SplitFinPlace E} [Field k]
  [IsAlgClosed k] {π : V →+* k} (hπ : (⇑π).Surjective) {x₀ : ThetaObject U.family _}
  (b₀ : x₀.IsPullbackAlong (specMap π) (s ≫ hom _)) (hk : w.1.1 = RingHom.ker x₀.baseHom) (hw :
  D.IsGoodAt w.1.1) (hG : IsSafe D.𝔑 w) {l} [Fact l.Prime] [CharP k l] {m α : Submodule .. →
  _} (hq : ∀ A, l ^ m A = w.1.q ^ (D.rank - finrank (ResField w.1) A)) (S : ∀ A,
  U.family.IsPointOf 1 (z.act ⟨_, heckeIsogeny_mem_GUPlus w A⟩ 1) (α A)) : ∃ W ≠ ⊥,
  (fun A ↦ specMap ((iterateFrobenius _ l (m A)).comp π) ≫ α A).FactorsThrough (· ⊔ W) := by
  obtain ⟨⟨e, rfl⟩, _, b, _, _, hb, co, _⟩ := o, hw.2
  choose y' _ _ _ S a using (ThetaFamily.isPointOf_iff .. |>.1 <| S ·)
  choose r ψ _ _ p o s using fun A ↦ e.exists_isogeny 1 (by simp [ratConj, ModuliPoint.act]) (S A)
    (by simp [ModuliPoint.act]) (heckeIsogeny_mem_GUPlus w A).2 isScalarFrame_heckeIsogeny
  choose σ hσ σ₂ _ K L using exists_residue_torsion_emb (n := D.Index) w.1
  have J {C v} := σ₂ ▸ heckeIsogeny_torsionClass C v hβ hG co hb
  have q := by simpa [← hβ,
    ← D.star_beta] using congr(algebraMap _ (𝓞 E) $(absNorm_span_eq_mul_star d₀ (c₀ d₀ - b)))
  simp_rw [hk, pointOf_hom] at hw hb σ₂ b₀
  obtain ⟨⟨_, ⟨_, ⟨t, rfl⟩, T, ht⟩, -⟩, ⟨_, c, h2⟩, i, j⟩ :=
    σ₂ ▸ exists_param_pow_card_eq_zero hw e.fullStructure b₀,
    co.pow (n := m ⊥), by simpa [CharP.intCast_eq_zero_iff] using Ideal.mem_of_dvd _ ⟨_, q⟩ hb
  let μ := l ^ m ⊥
  set υ' := (D.β - b) ^ m ⊥
  choose x hp using (y' · |>.exists_isPullbackAlong _)
  have hM B : l ^ m B * _ = μ := (by simpa [μ, hq] using pow_sub_mul_pow _ B.finrank_le)
  let F B : map (specMap ((iterateFrobenius _ l _).comp π)) ⟶ map (specMap π) := ⟨fun T ↦
    homMk _ (by simpa [specMap] using! (absFrobenius_comm ..).trans (T.3 ≫= comp_absFrobenius (m B)
    (.mk (𝟙 _)) (𝟙 _)) =≫ _), by simp [absFrobenius_comm, OverMorphism.ext_iff]⟩
  choose g Hg lg G using fun B ↦
    b₀.isGroupBaseChange.exists_hom_baseChange (hp B).isGroupBaseChange (F B) (ψ B)
  have cg B : pull (g B).1 (ThetaObject.lineBundle _).picClass = μ • _ := (by
    rw [← hM, mul_nsmul, picClass_pull_absFrobenius _ _ x₀.isProjEmbedding.1,
      (hp B).lineBundle_eq_pull, b₀.lineBundle_eq_pull]
    simpa [← pull_picClass, pull_comp,
      p] using! congr(pull $(Hg B (𝟙 _)).1 (ThetaObject.lineBundle _).picClass))
  have _ B := finite_flat_of_quasiFinite _ (locallyQuasiFinite_of_pull_picClass (isProjEmbedding _)
    NeZero.out (cg B)) ⟨fun z ↦ ((ψ B).1.surjective _).elim fun a e ↦
    (Scheme.exists_preimage_of_isPullback b₀.isGroupBaseChange.1 a _
    (by simpa [specMap, ← (ψ B).w, e, -Over.w] using! congr($((hp B).schemeMap.w) z))
    ).imp fun c k ↦ (IsClosedImmersion.isStableUnderBaseChange.1 (hp B).isGroupBaseChange.1.flip
    (.spec_of_surjective _ ((bijective_iterateFrobenius ..).2.comp hπ))).2.injective
    (by simpa [*, F, absFrobenius_apply, pointEquiv_apply] using congr($(Hg B (𝟙 _)).1 c))⟩
  have Δ C {v} := o C v ▸ map_eq_zero_iff _ (S C).fullStructure.injective
  have κ C x := K x ▸ (Δ C).trans (by erw [L _ (⟨_, (heckeIsogeny_mem_GUPlus w _).2 · ·⟩),
    heckeIsogeny_inv_at_eq_basicCosetRep hG, (basicCosetRep_spec _).2])
  have Z {C v} h : μ • torsionClass v = 0 :=
    (torsionClass_mulVec_eq_zero · ((@Δ C v).1 h)) |> fun H ↦ by
    rw [mulVec_mulVec, gram_inv_of_gram_eq isScalarFrame_heckeIsogeny.2.choose_spec] at H
    rw [← hM, mul_smul, smul_eq_zero_of_right]
    simpa [map_smul', ← map_nsmul, mul_mem, star_mem_Ô,
      (heckeIsogeny_mem_GUPlus w C).2, -coe_units_inv] using! H
  have K {B T} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] {t u} (hu : u ≫ g B = 0) :=
    (e.isRigid_pullback _ b₀).eq_zero_of_pairing_eq_zero (B :=
    T) (id_comp _) (u ≫ (μ • 𝟙 _)) 0 _ (b₀.isGroupBaseChange.pointEquiv.map_eq_zero_iff.1
    (by simpa [eq_zero_iff_factors_zero_section, pointEquiv_apply,
    b₀.isGroupBaseChange.nsmul_id_comp, -comp_nsmul] using! (ker_factors_of_torsionPoint
    e.fullStructure (ψ B) _ (torsionClass_induction (⟨𝟙 _, by simp [← map_nsmul, Hom.zero_def,
    @Z B · ·]⟩)) ((F B).1 (.mk t) ≫ b₀.isGroupBaseChange.pointEquiv u) (by simp [← Hg, hu]))))
    (by simp [← x₀.hasClassLaws.1.nsmul_class_pairing, cg B ▸ pairing_comp _, hu, pairing.eq_1])
  let Φ (A : Submodule (ResField w.1) _) : A →+ _ := .mk' (toUnit ((map (specMap π)) (specOver k
    k)) ≫ e.fullStructure.torsionPoint.comp σ ·.1) (by simp)
  have M A o : l ^ m A * .card (Φ A ⁻¹' {o}) = ite (o ∈ (Φ A).range) (μ / .card (Φ A).range) 0 := by
    split_ifs with h
    rw [← h.choose_spec, Nat.card_congr ((Φ A).fiberEquivKer _), ← hM A, ← card_ResField,
      ← index_ker, ← natCard_eq_pow_finrank, ← (Φ A).ker.card_mul_index]
    simp [← mul_assoc, index_ne_zero_of_finite]
    simp [Set.preimage_singleton_eq_empty.2 h]
  have Y {N} [AddCommGroup N] [Module (𝓞 E) N] {s : N} (h :
    μ • s = 0) := by simpa [← mul_comm i, j,
    (mod_cast h : (l : 𝓞 E) ^ m ⊥ • s = 0), mul_pow, mul_smul] using congr($q ^ m ⊥ • s).symm
  choose ν _ W using fun {A A'} (h : (Φ A').range = _) ↦
    exists_factor_through_isogeny (g A) _ fun B ↦ fun u hu ↦ by
    have H C := (exists_ker_parameter e.fullStructure b₀ hb co _ _ (Y (by
      simpa using congr(b₀.isGroupBaseChange.pointEquiv $(K hu)))) (nullstellensatz_exists_le_ker
      bot_ne_top).choose).choose_spec.2 (ψ C) ⟨_, hσ.injOn.injective.codRestrict
      fun x : C ↦ σ₂.le ⟨x, rfl⟩⟩ _ ((F C).1 (specOver k B)) (comp_absFrobenius _ (.mk _) (𝟙 _))
    simpa [← Hg, ← map_smul, ← ModuleObj.comp_smul, κ] using ((H A').2 · <| by erw [← pow_mul, M, h,
      ← M, pow_mul, (H A).1 _ _ rfl (torsionClass_induction fun v g ↦ Subtype.exists.2 <| by
     apply (J.2 _ (Y (Z g)) ((Δ A).1 _)).imp <;> simp +contextual [← κ, g]) (by simp [← Hg, hu])])
  have P {A B j} (a : 𝓞 E) (h : g A ≫ j = a • g B) := pairing_eq_of_fpqc_cover (.id_horiz _) (g A)
    (a • 𝟙 _) (g A) j (g B) (by simp [h, ← IsLinear.smul_comp, ← pairing_comp]; rw [cg, cg]; simp)
  use _ ∙ t, T ∘ by simp +contextual, fun A' A h ↦ ?_
  have hN : (Φ A').range = (Φ A).range := by simpa [Φ, SetLike.ext_iff, ht,
    Submodule.mem_span_singleton,
    (algebraMap_ResField_surjective _).exists] using congr((Φ $h).range)
  obtain ⟨j, _, hj⟩ := exists_factor_through_isogeny (g A') _ fun T ↦ fun y hy ↦ by
    simpa [add_smul, mul_smul, ← W hN.symm, reassoc_of% hy, ((S A).isRigid_pullback _ (hp
      A)).eq_zero_of_pairing_eq_zero (id_comp _) (y ≫ (υ' • g A)) _ (𝟙 _) (by simpa using _ ≫= K hy
      =≫ (υ' • g A)) fun _ i ↦ by simpa [pairing_comm _ (i ≫ _), pairing.eq_1 _ _ 0, υ', hy,
      pairing_pow_smul_adjoint] using (P _ (W hN) · (i ≫ y))] using congr(y ≫ ($h2 • g A)).symm
  open Fint in have ⟨t, q⟩ := ((S _).isRigid_pullback _ (hp _)).eq_of_hom (id_comp _) (by
    ext a; simpa [(hp _).baseHom_eq_comp, iterateFrobenius, ← card_ResField, r,
      ← algebraMap_ResField_eq_zero, b₀.baseHom_eq_comp, pow_card_pow, hq] using
      (congr(a ^ l ^ m A' - a ^ l ^ m A ∈ $hk))) j (hl := ⟨((epi_of_epi_left _).1 _ _ <| by
    simpa [← assoc, ← hj] using (lg A).2 ·)⟩) (pairing_eq_of_fpqc_cover (.id_horiz _) (g _) (𝟙
    _) (𝟙 _) j j (by simp [pairing_comm, hj, by simpa using P 1 (by simpa)])) (Subtype.forall.2
    (torsionClass_induction fun v h ↦ by simp [(hp _).levelPoints_eq_pullSection,
    (S _).fullStructure.eta_eq, ← G, hj, ← J.1 h ▸ o _ v]))
  simp [fibrePower_ext_iff, a, ModuliPoint.act, ↓← by simpa using s, -comp_left, ← comp_left_assoc,
    ← (hp _).isGroupBaseChange.pullSection_comp_assoc, ← G, (hp _).comp_toFamily, ← q, hj, hp, t]
