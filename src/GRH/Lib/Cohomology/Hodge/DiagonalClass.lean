import GRH.Lib.Cohomology.Hodge.PointClass
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Class of the diagonal in Hodge cohomology, glued from local Grothendieck symbols. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor


open CategoryTheory MonoidalCategory Ideal Set EtaleChart
attribute [-simp] Fin.natAdd_eq_addNat IsScalarTower.coe_toAlgHom'

/-- Class of the diagonal: if X has an atlas of dimension d, some δ in Hdg^d(X × X, complement
of the diagonal) is, near each diagonal field point, the symbol [df/f], where f_i = x_i ⊗ 1
− 1 ⊗ x_i for chart coordinates x cut out the diagonal.

Known result: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols). -/
lemma exists_diagonal_class {k} [Field k] [CharZero k] {X d} : @HasAtlas k _ d X → ∃ δ : HodgeH
  (relFreeAb (offDiagonal X)) d, ∀ K z, IsField K.1 → ∃ a O, IsOpenSub (X := X ⊗ X) O ∧ (z, z) ∈ O
  K ∧ ∀ᵉ (B) (p ∈ O B), ∃ φ ψ, X.map φ (point a) = p.1 ∧ X.map ψ a.point = p.2 ∧ IsLocalSymbol δ p
  (fun _ x ↦ x.1 = x.2) (fun i ↦ φ (a.coordinate i) - ψ (a.coordinate i)) 1 := fun ⟨_, a, ha⟩ ↦ by
  choose e h using exists_eq_iff_coordinate_eq ∘' a
  let V i := away (.prod ..) (e i)
  let l {i} : _ ⟶ (V i).R := CommAlg.toAway _
  have Q {n W V} (e : locus (d := n) V = W) := hodge_excision (U := (offDiagonal X).preimage W.ι)
    (V.comap W.ι ⟨_, e ▸ V.point_mem_locus⟩ rfl).isOpenSub (e ▸ by rintro _ _ ⟨_, _, ⟨⟩⟩; tauto) rfl
  choose x E using fun i ↦
    ((Q rfl d).2 _).imp (q := (IsLocalSymbol (X := (V i).locus.toFunctor) · ⟨_, point_mem_locus _⟩
    (fun _ x ↦ x.1.1 = x.1.2) _ 1)) fun _ ↦ (⟨fun C α ↦ by simpa [span_le, -map_sub] using! ((h i _
    (l ≫ α)).trans (and_iff_right ((CommAlg.exists_toAway_comp_iff ..).1 ⟨α, rfl⟩))).symm, _, ·⟩)
  have G {i B p χ} h : IsLocalSymbol (R := B) (x i) ⟨p, χ, h⟩ .. := h.rec ((E i).map _)
  have N {K} k z : ∃ i, (z, z) ∈ (V i).locus _ := (ha K k z).imp fun i m ↦
    ((range_pointMap_prod ..).ge _ ⟨m,
    m⟩).elim fun _ E ↦ E.subst ((mem_locus_away ..).2 ((h ..).1 (E ▸ mem_diagonal z :)).1)
  refine (relFreeAb.exists_glued_class _ {A | ∃ i c, (locus c).whisker _ = A ∧ c.locus ≤
    (V i).locus} (fun _ ⟨i, c, e, h⟩ _ ⟨_, b, E, _⟩ ↦ (c.exists_locus_eq_inf b).elim (⟨i, ·, · ▸
    ⟨congr($e ⊓ $E), by order⟩⟩)) (fun _ ⟨i, c, E, h⟩ m n ↦ E ▸ (h _ c.point_mem_locus).elim fun _
    e ↦ ⟨fun _ _ ↦ ((c.isCohomEquiv_univPoint.choose_spec.2 ((G e).1.preimage_fieldLocus_not.trans
    (by simp [EtaleChart.restrict, Pi.sub_def, away, EtaleChart.prod, ← map_sub]
        rfl))).2.comp_iff.2 (Q rfl) _).1 ((hodge_vanishing_along_diagonal (EtaleChart.restrict _ e
    c.injective c.isOpenSub).etale n).1 ..)⟩) _ (⟨·, _, rfl, le_rfl⟩)
    (hasZariskiDescent_hodgeCoeff (isLocallyEverything_of_open_cover fun _ k ⟨z, _⟩ ↦ by_cases
    (· ▸ (N k z).elim (⟨_, isOpenSub <| V ·, ·, le_sup_of_le_left (le_sSup ⟨_, rfl⟩)⟩)) (⟨_,
    isOpenSub_offDiagonal, mem_offDiagonal_of_ne k ·, le_sup_right⟩))) x fun i j ↦
    ((V i).exists_locus_eq_inf (V j)).elim fun c e ↦ (e ▸ c.point_mem_locus
    :).elim fun ⟨_, m⟩ ⟨_, n⟩ ↦ ?_).imp fun δ H K z k ↦ (N k z).elim (⟨a ·, _, isOpenSub _, ·,
    fun | _, _, ⟨⟨χ⟩, rfl⟩ => ⟨tensorInl ≫ l ≫ χ, tensorInr ≫ l ≫ χ, ?_⟩⟩)
  simpa [← map_sub] using ⟨rfl, rfl, by peel 2 G rfl; erw [← H,
    ← δ.map_comp _ (relFreeAb.map _ le_rfl), relFreeAb.map_comp] at this; tauto⟩
  obtain ⟨⟨D, _, u⟩, F, _, v⟩ := G m, G n
  refine (Q e _).1 (.trans ?_ (u.trans (c.symbolClass_eq_of_cutsOutLocus D F ▸ v ▸ ?_))) <;>
    erw [← (x _).map_comp _ (relFreeAb.restrict _ (by simp)), relFreeAb.map_comp] <;> rfl
