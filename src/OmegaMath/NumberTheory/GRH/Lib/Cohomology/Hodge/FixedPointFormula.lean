import OmegaMath.NumberTheory.GRH.Lib.Cohomology.Hodge.DiagonalClass
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols). The setting here is smooth separated varieties with a finite atlas in characteristic 0,
with cohomology taken as Ext of functors. These files give only surjectivity of the Künneth map for
X×X, and the pull-back of the diagonal class along reduced coincidences as a weighted sum of point
classes. Source: Stacks Project, tags 0BEC (Künneth) and 0G82 (Gysin maps); A. Chatzistamatiou, K.
Rülling, Higher direct images of the structure sheaf in positive characteristic, Algebra & Number
Theory 5 (2011) 693-775, sections 2-3; V. Srinivas, Gysin maps and cycle classes for Hodge
cohomology, Proc. Indian Acad. Sci. Math. Sci. 103 (1993) 209-247; Hartshorne, Residues and Duality
(1966) III.9 for the symbol.

Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles (known
result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Pull-back of the diagonal class is a weighted sum of point classes. -/

open CategoryTheory CommAlgCat Field H HodgeTest Ideal RingHom CartesianMonoidalCategory
  MonoidalCategory

variable {k} [Field k] [CharZero k] {d} {W X : CommAlg k ⥤ Type 1} [HasAtlas d X]

/-- For t in k and u, c: W → X, the map W(A ⊕ M) → (X × X)(A ⊕ M), w ↦ (u(s_t w), c(w)), with
s_t induced by (a,m) ↦ (a,tm). -/
def scaledGraph t (u c : W ⟶ X) :=
  lift (scaleModule t _ ≫ sqZeroExt.whiskerLeft u) (sqZeroExt.whiskerLeft c)

/-- For a k-point z of X, the constant map W → X sending every A-point of W to the image of z in
X(A). -/
def constMap (z : X (of k k)) : W ⟶ X where app A := ↾fun _ ↦ X.map structureMap z

seal H.map

/-- Fixed point formula: X with an atlas of dimension d has δ in Hdg^d(X × X) such that for E
over k, W separated and covered by charts, u, c: W → X_E with finite reduced coincidence set
s and ratios n_w as in `HasJacobianRatio`, (u s_t, c)^*δ = ∑_{w∈s} n_w cl(w).

Known result: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols). -/
lemma exists_diagonal_local_terms {d} (hX : HasAtlas d X) : ∃ δ : HodgeH (freeAb.obj (X ⊗ X)) d,
  ∀ {E} [Field E] [CharZero E] [Algebra k E] {W} [IsSepFunctor W] [IsChartCovered d W] (u c :
  W ⟶ _) s t (n : _ → E), IsCoincidenceSet u c s → (∀ w ∈ s, HasJacobianRatio u c d t (n w) w) →
  (∃ ξ : HodgeH (_root_.relFreeAb (offPoints s)) d, IsPointSum s n ξ) ∧ H.map _ (freeAb.map
  (scaledGraph t u c)) d δ.baseChange = ∑ w ∈ s, n w • pointClass d w := (exists_diagonal_class
  hX).imp' (.map (relFreeAb.π _)) fun δ hδ E _ _ _ W _ _ u c s t n ⟨hr, h, hs⟩ hJ ↦ by
  have N {U} (h : IsOpenSub U) : (U.preimage (lift u c)).whisker _ ≤
    (U.whisker _).preimage (scaledGraph t u c) := fun C _ m ↦ h.mem_of_isSquareZero C.baseProj
    fst_surjective_and_kerIdeal_sq _ (congr(($((X.map_comp_apply ..).trans
    (congrArg _ (u.naturality_apply ..).symm)), _) ∈ _).mp (U.map C.baseProj m))
  refine ⟨⟨H.map _ (relFreeAb.map (U' := (offPoints s).whisker _) _ fun C _ _ ↦
    N (@isOpenSub_offDiagonal _ _ X _).whisker_restrictAlg C
    ((isOpenSub_offDiagonal.whisker_restrictAlg.preimage _).fieldLocus_le _ fun _ _ ↦
    (mem_offDiagonal_of_ne (X := X) · (by tauto)))) d _, ?I⟩, IsPointSum.map_eq_sum_pointClass ?I
    rfl ▸ by erw [HodgeH.baseChange_map, ← map_comp, eq_comm, ← map_comp]; rfl⟩
  refine fun w hw ↦ (hδ _ (c _ w) (toIsField E)).elim fun A ⟨O, hO, hw', L⟩ ↦ ?_
  obtain ⟨⟨Q, hQ, hT⟩, a, ⟨⟨ζ : _ ⟶ _⟩, rfl⟩, ha, v⟩ := hJ w hw A (by have := L _ _ hw'; tauto),
    ((hO.whisker_restrictAlg.preimage (lift u c :)).inf (isOpenSub_offPoints (s :=
    s \ {w}))).exists_chart_le (toIsField E)
    ⟨congr(($(h w hw), _)) ▸ hw', by simp [mem_offPoints_iff, toIsField, ComesFromPoints]⟩
  obtain ⟨⟨φ, ψ, hφ, hψ, Z, -⟩, ν, F, V⟩ := L _ _ ha, a.isCohomEquiv_univPoint
  have M {v : W ⟶ restrictAlg k E ⋙ X} {B C φ y} h (α : B ⟶ C) :=
    (X.map_comp_apply φ _ A.point).trans ((congrArg _ h).trans (v.naturality_apply α y).symm)
  let f := (φ ∘ A.coordinate : _ → a.R) - by exact ψ ∘ A.coordinate
  have Z {C} (α : a.R ⟶ C) : span _ ≤ ker α.hom ↔ _ := (Z ..).trans (eq_comm.trans
    ((c.naturality_apply α a.point).congr (u.naturality_apply α a.point) :).symm)
  obtain ⟨b, o, hb⟩ := exists_mem_colon_of_tangent rfl ((Z ζ).2 (by tauto)) fun p _ l r ↦
    congr(($(a.eq_comp_of_map_point_eq _ (hr _ ((Z _).1 l))) r).2)
  have hk := by simpa using (map_eq_top_iff_fields _ (𝟙 _)).2 fun K κ i l ↦ v K κ i ((hs
    K i _ ((Z _).1 (le_colon.trans l))).imp fun z ⟨m, e⟩ ↦ ⟨⟨m, fun q ↦ hb (by
    simpa [a.eq_comp_of_map_point_eq _ (q ▸ e), i.nontrivial] using l o)⟩, e⟩)
  refine ⟨a, f, ⟨_, rfl⟩, ?D, fun C p l K κ hK ⟨z, hz, e⟩ ↦ (offPoints _).map _ v K κ hK
    ⟨z, ⟨hz, (l K κ hK ⟨z, ·, e⟩)⟩, e⟩, ((V (CutsOutLocus.preimage_fieldLocus_not ?D)).2 _).1 ?_⟩
  exact fun C α ↦ ⟨(by simp [ComesFromPoints, eq_comp_structureMap_of_ker_le <| hk.trans ·]; rfl),
    (Z α).2 ∘ by simp_all [ComesFromPoints]⟩
  obtain ⟨_, _, h₁, h₂, Y, _, e'⟩ := L _ _ (N hO.whisker_restrictAlg _ (Subfunctor.map _ ν ha))
  obtain ⟨rfl, rfl, e'⟩ := A.injective _ ((M (M hφ _) _).trans h₁.symm),
    A.injective _ ((M hψ _).trans h₂.symm), by simpa -dsimp using congr(($e').baseChange (k := E))
  have eF i : _ = f i := congr($(F _) - $(F _))
  erw [eq_comm, map_push, ← map_comp, eq_comm, ← map_comp, ← map_comp]
  refine (congrArg (H.map _ · d _) (relFreeAb.hom_ext fun C σ ↦ ?_)).trans ((map_comp ..).trans
    ((congrArg (H.map _ (relFreeAb.map (U' := someUnitLocus _) (U := .whisker (.preimage _
    (pointMap _)) (sqZeroExt ⋙ _)) (pointMap ⟨𝟙 _⟩) fun C σ ⟨i, e⟩ ↦ Y.preimage_fieldLocus_not.ge _
    (projSpace.span_eq_top_of_isUnit i (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (eF i ▸ e :)))) d)
    e').trans ((map_comp ..).symm.trans ((congrArg _ (witnessed.pull_cocycleClass
    exists_jouanolouRel_of_unimodular exists_jouanolouRel_of_unimodular _ (𝟙 _) {app _ := ↾(·.2)} ?_
    ?_ ?_)).trans (symbolClass_transformation (by tauto) ?_ (funext eF)
    (1 : Matrix (Fin d) _ _) (Q.map (algebraMap ..))
    _ (by ext; simp; erw [F]) (fun i j ↦ hk ?_) (hQ ▸ by simp [map_det]))))))
  exact congr(relFreeAb.mk _ $(W.map_comp_apply .. ▸ (scaledGraph ..).naturality_apply ..))
  (iterate 4 tauto); show ζ (t • (ν _).snd j - (ν _).snd j - _) = 0
  let μ := (withIndex _ ⋙ sqZeroExt).map ζ ≫ ofHom (TrivSqZeroExt.map (.proj j))
  have S y : (μ y).2 = ζ _ := zero_add _
  simpa [← S, f] using! congr($(hT _ _ _ (W.map_comp_apply .. ▸
    by congr with _; exact (add_zero _).trans congr(ζ $(F _))) (by tauto) (M hψ (ν ≫ μ))) i)

lemma exists_diagonal_pointClass : ∃ δ, ∀ z, (∃ ξ : HodgeH (_root_.relFreeAb (offPoints {z})) d,
  IsPointSum {z} 1 ξ) ∧ .map (freeAb.map (lift (constMap z) (𝟙 X))) δ = pointClass d z ∧
  ∀ {W} [IsSepFunctor W] [IsChartCovered d W] (u : W ⟶ X) s, IsCoincidenceSet (constMap z) u
  s → .map (freeAb.map u) (pointClass d z) = ∑ w ∈ s, pointClass d w :=
  (exists_diagonal_local_terms ‹_›).imp' _ fun δ h z ↦ by
  have h W [IsSepFunctor W] [IsChartCovered d W] :=
    (h (W := W) (constMap z) · · 1 1 · fun _ _ _ _ ↦ ⟨1, by simp⟩)
  have e :=
    h X (𝟙 _) {z} ⟨fun | _, rfl => (map_map_structureMap ..).symm, by simp [constMap]; tauto⟩
  simp at *
  use Finset.coe_singleton z ▸ e.1, e.2; peel h; erw [← this.2, ← e.2, ← map_comp]
  congr; exact freeAb.hom_ext (Y := _ ⋙ _)

/-- If X has an atlas of dimension d and the k-points z, z' take the same value under every map
from X to the affine line, then cl(z) = cl(z') in Hdg^d(X). -/
lemma pointClass_eq_of_functions_eq {z z'} (e : ∀ g : X ⟶ affineSpace k 1, (g _ z).1 0 =
  (g _ z').1 0) : pointClass d z = pointClass d z' := by
  repeat rw [← (exists_diagonal_pointClass.choose_spec _).2.1]
  apply AddMonoidHom.eqOn_closureM _ (kunneth _)
  rintro _ ⟨a, n, h, x, y, rfl⟩
  have ⟨_, r⟩ := @projective_and_eval_bijective _ _ (@sqZeroExt k _ ⋙ 𝟙_ _) hodgeCoeff ⟨_, Empty⟩ ⟨⟩
    fun _ ↦ ⟨fun ⟨_⟩ ⟨_⟩ _ ↦ congrArg _ (hom_ext (by ext) nofun), fun _ ↦ ⟨⟨structureMap, 0⟩, rfl⟩⟩
  repeat erw [← map_comp, cup_map _ x y h (freeAb.map (sqZeroExt.whiskerLeft (constMap _))) (𝟙 _)
    (γ' := freeAb.map (λ_ _).inv ≫ freeAb.prod (_ ⋙ 𝟙_ _) (_ ⋙ X)) freeAb.hom_ext]
  congr 2; cases a <;> [rw [← x.mk₀_homEquiv₀_apply]; subsingleton]
  repeat erw [H.map, Abelian.Ext.bilinearComp_apply_apply, Abelian.Ext.mk₀_comp_mk₀]
  exact congrArg _ (r.1 (ULift.down_injective (formBasis.ext_elem fun i ↦
    e (freeAb.homEquiv X _ ((𝟭 _).whiskerRight (H := _ ⋙ sqZeroExt) ⟨fun _ ↦
    ofHom (TrivSqZeroExt.inlAlgHom ..), by intros; ext; exact TrivSqZeroExt.ext rfl (by ext ⟨⟩)⟩
    (freeAb X) ≫ (withIndex _).whiskerLeft (Abelian.Ext.homEquiv₀ x)) ≫ ⟨fun A ↦ ↾(⟨fun _ ↦
    formBasis.repr ·.1 i⟩), by intros; ext; congrm ⟨fun _ ↦ $(repr_withIndex_map ..)⟩⟩))))
