import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.CechDescent
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Commutation of cohomology with filtered limits descends along Čech covers. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

noncomputable section


open CategoryTheory Limits Function Functor AddCommGrpCat MorphismProperty colimit Arrow
  LongExactSeq H Comparison
variable {C} [Category C] {F : AbFunctor C} {J} [SmallCategory.{0} J] [IsFiltered J]
  {D : Jᵒᵖ ⥤ C ⥤ Type 1} {T} [Category* T]

/-- A cocone of abelian groups is a filtered colimit elementwise: an element mapping to 0 in the
vertex dies at a later stage, and every element of the vertex comes from some stage. -/
def IsFilteredColimit {X : J ⥤ Ab} (c : Cocone X) :=
  (∀ j x, c.ι j x = 0 → ∃ i f, @X.map j i f x = 0) ∧ ∀ y : c.pt, ∃ j x, c.ι j x = y

/-- The contravariant functor sending Φ: T → (functors from C to abelian groups) to the
contravariant functor t ↦ Ext^n(Φ(t),F) from T to abelian groups. -/
abbrev cohFunctor F n := opHom T (AbFunctor C) ⋙ (whiskeringRight ..) ⟨_, (ofHom <| map F ·.unop n),
  by aesop, fun _ _ ↦ ext (map_comp _ _)⟩

/-- For a cone over a cofiltered system D_j and a level r, the condition `BijectiveUpTo` at
level r for the canonical maps colim_j H^n(D_j,F) → H^n(vertex,F). -/
def ContinuousUpTo F (c : Cone D) := BijectiveUpTo fun n ↦
  desc _ ((cohFunctor F n ⟨freeAb⟩).mapCocone (coconeRightOpOfCone c))

attribute [local instance] preservesSmallestFilteredColimits_of_preservesFilteredColimits

/-- For a diagram X of abelian groups over a small filtered category, a cocone c satisfies the
elementwise conditions `IsFilteredColimit` if and only if the induced map from the colimit of X
to the vertex of c is bijective. -/
lemma isFilteredColimit_iff_bijective {X : J ⥤ Ab.{2}} {c} : IsFilteredColimit c ↔
  Bijective (desc X c) := by
  have z := by simpa using Concrete.from_union_surjective_of_isColimit X (isColimit _)
  simp [IsFilteredColimit, Bijective, injective_iff_map_eq_zero, Surjective, z.forall, z.exists,
    Sigma.forall, by simpa using ((isColimit X).eq_iff' (i := ·) · 0)]

/-- Take a cone over a cofiltered system of covers E_j → Y_j whose vertex is a cover. If
`ContinuousUpTo` holds at level r+1 for the E_j and at level r for all fibre powers with at least
one factor, it holds at level r+1 for the Y_j. -/
lemma ContinuousUpTo.of_cech {A : Jᵒᵖ ⥤ _} (a : Cone A) (hp : ∀ j, IsCover F (A j).hom) (hq :
  IsCover F a.pt.hom) {r} (h₀ : ContinuousUpTo F (leftFunc.mapCone a) r) (h : ∀ m,
  ContinuousUpTo F ((cechFunctor m).mapCone a) (r - 1)) :
  ContinuousUpTo F (rightFunc.mapCone a) r := let G := (whiskeringLeft ..) A.rightOp ⋙ colim
  let η : G ⟶ (evaluation ..) _ :=
    ⟨(desc _ <| ·.mapCocone (coconeRightOpOfCone a)), by simp [G, colimit.hom_ext_iff]⟩
  let k := ((toArrowFunctor ⋙ whiskeringLeft ..).flip.op ⋙ cohFunctor F ·)
  (BijectiveUpTo.congr (fun n ↦
    (colim.mapIso (isoOfAppBijective _ (hp ⟨·⟩ n))).addCommGroupIsoToAddEquiv.bijective)
    hq fun n x ↦ (η.naturality_apply ((k n).map ⟨freeAb.map (Subfunctor.range leftToRight).ι⟩)
    x).symm).2 (cech_descent_step _ (f := fun N n ↦ η (k n ⟨N⟩)) ⟨fun {S _} x ↦ by
    let L {t} := contravariant (x.map_of_exact ((whiskeringLeft ..) (toArrowFunctor t))) F
    refine LongExactSeq.Hom.four_lemma (by constructor <;> intro <;> apply η.naturality_apply :
      Hom ⟨(k · ⋙ G |>.map S.g.op |>.hom), (k · ⋙ G |>.map S.f.op |>.hom),
      fun n ↦ (G.map ⟨fun t ↦ @ofHom (L.C n) (L.A _) _ _ (L.δ n), fun _ _ f ↦ .symm (ext
      ?n)⟩).hom, (AddCommGrpCat.mono_iff_injective _).1 ((monomorphisms _).colimMap _ fun _ ↦
      ConcreteCategory.mono_of_injective _ L.injective_f), ?_, ?_, ?_⟩ L ..)
    case n => simpa only [id_pull] using! (pull_hom_contravariant (x.map_of_exact _) _ (.id F)
      (S.mapNatTrans ((whiskeringLeft ..).map _))).comm_delta n
    all_goals exact fun _ ↦ exact_of_shortComplex_exact ((exact_of_app fun _ ↦ by
      apply_rules [L.exact_f_g, L.exact_g_delta, L.exact_delta_f]).2.map G)⟩ h₀ h)
