/- GID: D5/S3/Zeros/GRH/Lib/Shimura/IntegralModel/ModelExistence
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/IntegralModel/ModelExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.IntegralModel.ModelExistence. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/IntegralModel/ModelExistence.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.CongruenceRelation.CongruenceStep
import D5.S3.Zeros.GRH.Lib.Shimura.ThetaModuli.UniversalFamily
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation.
Here the smooth proper base is a closure of theta values with no moduli property, and the congruence
relation at good split places is part of the statement. The covers are reduced projective closures
of tuples of isogenous points, are Galois on points in characteristic zero, and are not claimed
smooth. Source: Harris, Taylor, The geometry and cohomology of some simple Shimura varieties, 2001,
III.4; Kottwitz, Points on some Shimura varieties over finite fields, JAMS 5 (1992), §5.

This file: Integral Kuga-Sato model with Hecke covers and congruence relation exists. -/

open Algebra _root_.RingHom CategoryTheory Classical ReducedClosure UniversalFamily Filter Finset
  Function IsLocalRing NumberField QuotientGroup AlgebraicGeometry.Spec Category

attribute [-simp] sup_of_le_left sup_of_le_right

attribute [local simp] datumPoint_eq_iff ModuliPoint.act ModuliPoint.isLevelIso_iff QuotientGroup.eq
  ratConj mul_assoc

/-- Given a universal family for D over R (`UniversalFamily`), if the level 𝔑 is neat, β = (1 +
√−d₀)/2 and every safe place is good for D, then for any positive finite number of marked
points there is a model of level 𝔑 over R (`Model`).

Known result: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation. -/
lemma exists_model {E} [Field E] [CMBase E] {d₀} [HasQuadSubfield _ E]
  {R} {D : PEL E} (U : UniversalFamily D R) (hN : IsNeat D.Index D.𝔑) (hβ : D.β =
  algebraMap _ _ (QuadField.c₀ d₀))
  (hG : ∀ w, IsSafe D.𝔑 w → D.IsGoodAt w.1) ν [NeZero ν] : Nonempty (Model D.Index d₀ D.𝔑 ν R) := by
  choose M hM using exists_level_conj_mem (n := D.Index) hN.1
  let Q i := _ ⧸ ((levelGU _ (M i)).subgroupOf (levelGU D.Index D.𝔑)).normalCore
  let γ i (j : Q i × ↥(insert (M i, 1) (insert 1 i))) :=
    (j.2.1.1, ⟨_, mem_GUPlus_of_mem_levelGU j.1.out.2⟩ * j.2.1.2)
  obtain ⟨⟨hs, sj, m, hm⟩, C⟩ := U.fibrePower_spec ν, (ofNonempty : ∀ i, U.GraphClosure (γ i) ν)
  have L {i x a} k := ((C i).point_comp_proj a (⟦k⟧, x)).trans (c := datumPoint x.1.1
    (a.act (⟨_, mem_GUPlus_of_mem_levelGU k.2⟩ * x.1.2))) (datumPoint_eq_iff.2 ⟨1, by
    simpa using! hM i _ x.2 _ (QuotientGroup.eq.1 (k : Q i).out_eq.symm 1)⟩)
  choose p P pp using fun {i} (κ : levelGU _ D.𝔑) ↦
    (C i).exists_lift (·.act ⟨_, mem_GUPlus_of_mem_levelGU κ⁻¹.2⟩)
    (fun j ↦ (C i).proj (κ⁻¹ * j.1, j.2)) fun _ ↦ (·.1.out_eq ▸ (L _).trans (by simp [γ]))
  choose u hu using fun i ↦ (@factorsThrough_iff (Σ' g f, ∀ a, (C i).point a ≫ f = U.datumPoint 1
    (a.act g)) (_ ⧸ levelGU D.Index D.𝔑) _ (·.1) (·.2.1) ⟨(C i).proj ⟨1, 1, by simp⟩⟩).1 fun p q e ↦
    (isSeparatingFamily _).hom_ext fun a ↦ by simpa [p.2.2, q.2.2] using ⟨1, by simpa using e.symm⟩
  let s i := {g | ∃ h, ∀ a, point _ a ≫ u i ⟦g⟧ = datumPoint 1 (a.act ⟨g, h⟩)}
  have o i : 1 ∈ s i := ⟨one_mem _, fun _ ↦ congr(_ ≫ $(hu i)
    ⟨1, (C i).proj ⟨⟦1⟧, 1, by simp⟩, by simp [↓L]⟩).symm.trans (by simp [↓L])⟩
  have hc {i} := by simpa using (o i).2
  have T {g k i j f} (h : ∀ a, (C i).point a ≫ f = (C j).point (a.act ⟨g, k⟩)) ⦃q⦄ (H : q ∈ s j) : f
    ≫ u j ⟦q⟧ = u i ⟦g * q⟧ := congr($(hu i) ⟨⟨_, mul_mem k H.1⟩, _, by simp [reassoc_of% h, H.2]⟩)
  refine ⟨_, _, s, u, o, fun j hg ↦ (eventually_all.2 fun x ↦ eventually_finset_mem_atTop ((γ j
    x).1, (⟨_, hg⟩ * (γ j x).2 :))).mono fun i h ↦ ((C j).exists_lift (·.act ⟨_, hg⟩) ((C i).proj
    ⟨⟦1⟧, _, mem_insert_of_mem <| mem_insert_of_mem <| h ·⟩ :) (by simp [↓L])).elim fun f h ↦
    ⟨⟨hg, by simp [← by simpa using T h.2 (o j), ← assoc, *]⟩, f, T h.2⟩, (.of <| Q ·), fun _ ↦
    lift _ ⟨⟨(.of <| p ·), End.ext ((isSeparatingFamily _).hom_ext (by simp [pp]))⟩, fun _ _ ↦
    End.ext ((isSeparatingFamily _).hom_ext (by simp [pp, ← assoc]))⟩ fun κ h ↦ End.ext <|
    hom_ext _ fun j ↦ by erw [P,
    mul_eq_right.2] <;> simp [h], fun _ ↦ Quot.ind (⟨·⁻¹, T (pp _)⟩), m, _, (C · |>.point_surjective
    hc), by simp [*], fun g α a h ↦ by simp [reassoc_of% h.2, *, -ModuliPoint.act], _,
    hs, fun i ↦ isGaloisCovering_of_complex_points (fun k _ _ f ↦ let := f.toAlgebra
    ((IsAlgebraic.trans _ (𝓞 E) _).tower_bot_of_injective Subtype.val_injective).injective_tower_top
      R Int.cast_injective) (Quot.ind fun _ ↦ (T (pp _) (o _)).trans (by congr 1; simp))
    (sj.surjective _ _ (congr($(hc ·).1))) (((C i).point_surjective hc).forall₂.2 fun x y e ↦
    existsUnique_of_exists_of_unique ((datumPoint_eq_iff.1 (hc x ▸ hc y ▸ e)).elim fun z r ↦
    ⟨⟦⟨_, r.mem_level.1⟩⟧, (pp ..).trans ((C i).exists_level_point_eq.choose_spec ⟨by simp,
    r.reflection_eq, by simpa using r.sub_mem_lattice⟩)⟩) (mk_surjective.forall₂.2 fun κ κ' e e' ↦
    QuotientGroup.eq.2 fun q ↦ (datumPoint_eq_iff.1 (L _ ▸ L _ ▸ (pp
    ..).symm.trans (e ▸ e' ▸ pp ..) =≫ (C i).proj ⟨⟦κ * q⁻¹⟧, _, mem_insert_self
    ..⟩)).elim fun z r ↦ ?_)), fun i g α a _ _ h x y z ↦ ?_, fun w H i _ N h l m _ f k _ _ x X ↦ ?_⟩
  · cases hN.2 x.isSignedFrame
      (by simpa [mul_mem_cancel_left] using mul_mem r.mem_level.1 q.2) r.reflection_eq
    simpa using r.mem_level.2
  · choose f h0 e _ hb using exists_ball_family a
    obtain ⟨⟨K, k⟩, σ, hσ⟩ := hb x y z, ((C i).holomorphicAt_point a.P 0 h0).exists_isJet .id
    have T x :
      IsJet (f.ballPoint a.P · |> (C i).point |>.left) 0 (.applyₗ x) (specMap (TrivSqZeroExt.map
      (.applyₗ x)).1 ≫ σ) := (by simp [PointFn.isRegularOn_ofSection _ _, hσ · · ·, LandsIn.comp])
    have S x := ((T x).comp_hom _).congr (.of_forall fun _ ↦ congr($(hc _).1))
    exact ⟨.of ℂ _, ⟨Over.homMk _ ((hσ.comp_base_eq fun _ ↦ Over.w _).trans (map_comp ..).symm)⟩,
      K, by simp [(f.torus 0).isPeriodMap.finrank_eq_abelianDim], congr(⟨$(Over.OverMorphism.ext
      (e ▸ hσ.fst_comp :))⟩), fun x y e ↦
      sub_eq_zero.1 ((U.isHolImmersionAt_datumPoint 0 h0).2 _ (isFirstOrderConst_iff.2 fun U f i ↦
      by simpa using! congr($((S x U f i).2.symm.trans (congr(PointFn.ofSection f _ $e.1.1).trans (S
      y U f i).2)).snd))), fun x ↦ ULift.up_inj.2 (Over.OverMorphism.ext (((isJet_comp_iff
      (ContinuousLinearMap.mk K).hasFDerivAt (U.isHolImmersionAt_datumPoint _ (by simpa)).1).2
      (K.map_zero ▸ S _)).unique (((T x).comp_hom _).congr (k.1.mono fun q r ↦ congr($(((reassoc_of%
      h.2) _ _).trans ((hm ..).trans (datumPoint_eq_iff.2 ⟨_, by simpa using r⟩))).1)))).symm), k.2⟩
  obtain ⟨z, ρ, ⟨⟩, -⟩ := exists_countable_residue_point (Over.hom _) x
  choose V α b ρ' r S using (C i).exists_arc z
  rcases ρ.charP ρ.injective, charP_of_injective_ringHom ρ'.injective, @Fintype.toLocallyFiniteOrder
  refine (U.congruence_step hβ (S (hc b)) residue_surjective rfl (w.1.isMaximal.eq_of_le (ker_ne_top
    _) fun a h ↦ ?_) (hG _ H) H (fun _ ↦ f ▸ pow_mul' ..) (S <| h · |>.2 b)).elim fun W G ↦ .mono
    (.mono ((FreeAbelianGroup.equivFinsupp _).injective (Finsupp.ext
    (IncidenceAlgebra.moebius_inversion_bot _ 0 (fun A ↦ by by_cases W ≤ A <;> simp [‹_›, sum_ite,
    ← @Int.cast_inj ℂ, prod_eq_zero (i := 0), q_binomial_submodule,
    zero_lt_iff, ne_bot_of_le_ne_bot G.1, ← card_ResField, Finsupp.single_apply, -zsmul_eq_mul,
    sum_fiberwise_eq_sum_filter, filter_filter]) · |>.trans (by simp)))) G.2) fun A B t ↦ ?_
  · erw [ThetaObject.baseHom, ← assoc, preimage_comp]
    simpa [← reassoc_of% r, ← (u i ⟦1⟧).w] using X _ (N a h)
  simp [specMap] at t
  simp [← reassoc_of% r, ← map_comp_assoc, ← CommRingCat.ofHom_comp, ← iterateFrobenius_comm] at t ⊢
  simpa [cancel_epi] using t
