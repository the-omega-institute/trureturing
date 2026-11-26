import OmegaMath.NumberTheory.GRH.Lib.Cohomology.Hodge.FixedPointFormula
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Hodge class of a point of a product is the product of point classes. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Functor relFreeAb Classical
set_option backward.isDefEq.respectTransparency false

-- `relFreeAb.map` is written in full: a bare `map` is ambiguous
/-- The product of point classes is a point class: over a field k of characteristic 0, if X and
Y have atlases of dimensions d and 1, then cl(z) × cl(w) = cl(z, w) in Hdg^{d+1}(X × Y) for
k-points z, w. -/
lemma IsPointSum.cup_pointClass {k} [Field k] [CharZero k] {d X Y} [HasAtlas d X] [HasAtlas 1 Y]
  z : .map (freeAb.prod X Y) (cup (@exteriorAlg k _).mulPairing (pointClass d z.1)
  (pointClass 1 z.2) (add_comm ..)) = pointClass _ z := by
  have m {R X Y U W T S} s t h l x y := (HodgeH.map_comp (relFreeAb.map (@pointMap _ _ (X ⊗ Y) R (s,
    t)) (sup_le_sup h l)) (relFreeAb.prod U W) _).symm.trans (cup_map (γ' :=
    (@HodgeTest.sqZeroExt k _).whiskerLeft (relFreeAb.map (lift (𝟙 _) (𝟙 _)) le_rfl ≫ relFreeAb.prod
    T S)) (mulPairing _) x y (add_comm 1 d) (whiskerLeft _ (relFreeAb.map (pointMap s) h))
    (whiskerLeft _ (relFreeAb.map (pointMap t) l)) (hom_ext (U := (T ⊔ S).whisker _)))
  obtain ⟨⟨a, g, ez, e⟩, b, g', ew, e'⟩ := epsilon_spec (exists_diagonal_pointClass.choose_spec _).1
    z.1 rfl, epsilon_spec (exists_diagonal_pointClass.choose_spec _).1 z.2 rfl
  have ⟨ξ, L, G⟩ := (a.prod b).exists_isLocalSymbol (g := Fin.snoc (g · ⊗ₜ 1) (1 ⊗ₜ g' 0))
    (fun _ α ↦ .symm (exists_eq_left.trans (Prod.ext_iff.trans (by simpa -dsimp [ComesFromPoints,
    Ideal.span_le, Set.subset_def, and_comm] using! ((e.1 _ (_ ≫ α)).and (e'.1 _ (_ ≫ α))).symm))))
    ((range_pointMap_prod ..).ge _ ⟨ez, ew⟩)
  use have hU := by rintro _ _ (h | h) _ _ l ⟨_, ⟨⟩, e⟩ <;> use h _ _ l ⟨_, rfl, by injections⟩
    (cup_map _ _ _ _ (whiskerLeft _ (π _)) (whiskerLeft _ (π _)) rfl).symm.trans ((HodgeH.map_comp
      (π _) (relFreeAb.prod ..) _).trans ((hodge_excision (a.prod b).isOpenSub (fun _ l _ n ↦ by
    obtain ⟨_, h⟩ | ⟨_, h⟩ := (not_and_or.1 (range_pointMap_prod a b ▸ n)).imp
      (exists_isOpenSub_le_offPoints ez l ·) (exists_isOpenSub_le_offPoints ew
    l ·) <;> exact ⟨_, h.1.preimage _, by tauto⟩) rfl _).1 ((m ..).trans ((congrArg _
    (congrArg₂ (cup _ · · _) (e.map _).2.2 (e'.map _).2.2)).trans (by
    erw [one_smul, one_smul, ← m]
    simpa -dsimp [(symbolClass_succ ..).2, ← HodgeH.map_comp, pointMap_comp] using!
      congr($(L.2.2).map (relFreeAb.map (𝟙 (reprBy _)) fun x _ ↦ (hU x ·))).symm)) : _ = (ξ.map
      (relFreeAb.map (𝟙 _) hU)).map _) ▸ by simp [← HodgeH.map_comp, π_map,
      G.map_eq_smul_pointClass]))
