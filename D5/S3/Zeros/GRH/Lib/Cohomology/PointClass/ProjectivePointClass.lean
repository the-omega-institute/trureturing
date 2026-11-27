/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/ProjectivePointClass
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/PointClass/ProjectivePointClass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.PointClass.ProjectivePointClass. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/PointClass/ProjectivePointClass.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.PointClass.LinePointClass
import D5.S3.Zeros.GRH.Lib.Cohomology.PointClass.PointClassProduct
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Hodge–Tate map does not kill the class of a point of projective space. -/

open CategoryTheory Finset CartesianMonoidalCategory CommAlgCat Fin Polynomial
set_option backward.isDefEq.respectTransparency false

seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
/-- For a field k with an embedding in Q̄_p and any k-point z of projective d-space
`projSpace`, the Hodge–Tate map of weight d does not kill the class cl(z) ∈ Hdg^d.

Known result: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles. -/
lemma projSpace.hodgeTateMap_pointClass_ne_zero {p k} [Field k] [EmbeddedInQpBar p k] {d} z :
  hodgeTateMap d (pointClass (X := projSpace k d) d z) ≠ 0
  := exists_hodgeTateMap_pointClass_line.rec fun η ⟨hη, P⟩ ↦ by
  have c {d} : ∀ z, pointClass d z = pointClass d (@affinePoint k _ d _ 0 0) :=
    Quot.ind fun ⟨⟨u⟩, h⟩ ↦ pointClass_eq_of_functions_eq fun g ↦
    have n {B C z} (ψ : B ⟶ C) x (e : z =
      _ := by erw [mk_eq_mk_iff_cross_mul]; simp [forall_fin_succ] at * <;>
     grind) := congr($((congrArg _ e).trans (g.naturality_apply ψ x)).1 0)
    if hj : _ then (eq_C_of_toLaurent_eq _ _ ((n (ofHom toLaurentAlg) (mk (cons X (C ∘ u ∘ succ))
    (Exists.rec span_eq_top_of_isUnit hj))).symm.trans
      (n (ofHom (LaurentPolynomial.invert.toAlgHom.comp toLaurentAlg)) (affinePoint 0
      (monomial 1 ∘ u ∘ succ)) rfl))).rec fun _ e ↦ (n (ofHom (aeval (u 0))) _).trans ((congr(
    aeval _ $e.1 = aeval _ $e.2).mpr (by simp)).trans (n (ofHom (aeval 0)) _).symm) else n (𝟙 _) _
  have M {d} (z := @affinePoint k _ d _ 0 0) : hodgeTateMap d.succ (.map (freeAb.map (lineProductMap
    k d)) (pointClass d.succ (affinePoint 0 0))) = 0 ↔ hodgeTateMap d (pointClass d z) = 0 := by
    obtain ⟨⟨ξ, hx⟩, δ, h⟩ := IsChartCovered.pairRestrictBijective.exists_hodgeTateMap_eq d
      (pointClass d z), exists_diagonal_local_terms (hasAtlas k _)
    have C : IsCoincidenceSet (𝟙 _) (constMap z) {z} := by simp [IsCoincidenceSet,
      ConstIfCoincident, constMap, @map_map_structureMap k]
    have S t : HodgeH.scale t (.map (freeAb.map (lift (𝟙 _) (constMap z))) δ.baseChange) = _ :=
      (H.map_comp ..).symm.trans (congr(H.map _ $freeAb.hom_ext _ _).trans (h _ _ _ t _ C fun _ _ A
      _ ↦ ⟨.scalar _ t, rfl, fun _ _ γ _ _ c ↦
      A.eq_comp_of_map_point_eq _ (C.1 _ c.symm) ▸ by simp; repeat erw [sub_zero]⟩).2)
    have w l (n : hodgeTateMap l (pointClass d z) ≠ 0) :=
      Nat.pow_right_injective .refl (EmbeddedInQpBar.toCharZero.1
      (by simpa [smul_left_inj n, hodgeTateMap_scale] using
      congr((2 : k) ^ l • hodgeTateMap l $(S 1) = hodgeTateMap l $(S 2))))
    have F {B v u} : lineProductMap k d B (v, u) = (projSpace ..).map structureMap
      (affinePoint 0 0) → ∀ [IsLocalRing B], ∃ j, (v, u) = _ := v.induction_on₂ u fun _ _ e _ ↦
      (exists_eq_single_of_mul_eq_zero _ _ (by simpa using mk_eq_mk_iff_cross_mul.1 e ·.succ 0)).2
    rw [(exists_diagonal_pointClass.choose_spec _).2.2 (lineProductMap ..) _ ⟨fun (_,
      _) e ↦ by rw [(F e).choose_spec, map_map_structureMap], forall_mem_image.2 fun _ _ ↦
      mk_eq_mk_iff_cross_mul.2 (by simp [forall_fin_succ]), fun _ K _ e ↦ let := K.toField
      exists_mem_image.2 ((F e).imp (⟨mem_univ ·, ·⟩))⟩]
    simp_rw [← IsPointSum.cup_pointClass, c, ← c z, map_sum, hodgeTateMap_map, hodgeTateMap_cup]
    rw [sum_eq_single d] <;> simp +contextual [Finset.ext_iff, hx, hη, Not.imp_symm (w _),
      ← Nat.cast_smul_eq_nsmul k, -Nat.cast_add]
    refine ⟨fun _ ↦ P ξ (IsChartCovered.pairRestrictBijective.injective_restrictToPairs.comp
      (IsCohomEquiv.of_isIso ..).1 ((restrictToPairs_map (freeAb.prod ..) _).trans
      ((congrArg _ ((congrArg _ (Comparison.pull_cup abTensor_hom_ext
      ..)).trans (TotalH.cup_of ..).symm)).trans (by simpa)))) ▸ map_zero _, (by simp [·])⟩
  refine mt (M z).2 (d.rec (mt (congrArg (PairH.map (freeAb.map (lift (constMap (affinePoint 0 0))
    (𝟙 _))))) fun e ↦ ?_) fun _ ↦ mt (by simp [hodgeTateMap_map, M.1 ·]))
  erw [← hodgeTateMap_map, ← HodgeH.map_comp, ← freeAb.map_comp, show _ ≫ _ = 𝟙
    _ by ext _ ⟨⟩; erw [mk_eq_mk_iff_cross_mul]; simp, freeAb.map_id, H.map_id, hη, map_zero,
    map_eq_zero_iff _ IsChartCovered.pairRestrictBijective.injective_restrictToPairs] at e
  simpa using PadicTest.eq_zero_of_algebraMap_genericRing ⟨Unit, _, Pi.constRingHom ..⟩ 1
    congr(($(show 𝟙 genericCoeff = 0 by simpa [cup, e] using P (.mk₀ _)).1 _ ⟨_⟩).1)
