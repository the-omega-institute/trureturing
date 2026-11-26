import GRH.Lib.Cohomology.Etale.AcyclicTests
import GRH.Lib.Cohomology.Etale.Partitions
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Descent of torsion étale cohomology along v-covers, with excision, transfer and
limits. Here cohomology is defined as Ext of presheaves on rings whose local rings are valuation
rings of algebraically closed fields. Descent, excision, transfer and limits are proved from this
definition, and equality with étale cohomology is neither proved nor used. Source: Scholze,
Berkovich Motives, arXiv 2412.03382 (2024), Thm 4.1 and Lemmas 4.7, 4.8 (descent and limits from
finitary functors on test rings); Bhatt, Mathew, The arc-topology, Duke Math. J. 170 (2021), Prop
5.2, Thm 5.4; Stacks project, Tag 09YQ; Scholze, Étale cohomology of diamonds, 7.15-7.16.

This file: Cohomology turns filtered limits of relatively affine functors into colimits; base change
functors. -/

open CategoryTheory Limits IsLimit colimit Functor essImage Over Comma Subfunctor Subalgebra Algebra
  CostructuredArrow.CreatesConnected Types FilteredColimit Preorder


attribute [local simp] OverMorphism.ext_iff fibreProd
variable {X Y W : PointFunctor} (u : W ⟶ X) (s : X ⟶ Y)

lemma HV.map_comp {Λ n} x : map Λ (u ≫ s) n x = map Λ u n (map Λ s n x) := by simp [H.map]

lemma baseChangeOf.ext {A R s φ B} {x y : @baseChangeOf X R s A φ B} (h : x.1.1 = y.1.1) (e : ∀ a,
  x.1.2.1.hom a = y.1.2.1.hom a) : x = y := congr(⟨($h, ⟨$(by aesop)⟩), _⟩)

set_option backward.isDefEq.respectTransparency false

/-- For s: X → Y, the base change functor from functors over Y to functors over X, sending E → Y
to X ×_Y E → X. -/
def pullbackOver : Over Y ⥤ Over X := .mk (.mk <| fibreProd.fst s ·.3)
  fun f ↦ homMk (.mk fun _ ↦ ↾(⟨(_, f.1 _ _), congr(($f.w) _ _) ▸ ·.2⟩))

instance : (pullbackOver s).IsRightAdjoint := ⟨_, ⟨(mapPullbackAdj s).ofNatIsoRight
  (NatIso.ofComponents fun _ ↦ isoMk isPullback_fibreProd.isoPullback).symm⟩⟩

/-- Continuity over X: for every filtered inverse system of functors relatively representable
(affine) over X, the Λ-cohomology on test rings of the limit is the colimit of the cohomologies. -/
def IsCohomContinuous Λ X := ∀ ⦃J⦄ [SmallCategory J] [IsFiltered J] ⦃D⦄ ⦃c : Cone D⦄,
  IsLimit ((forget X).mapCone c) → (∀ j : Jᵒᵖ, IsRelAffine (D j).hom) → ∀ r,
  ContinuousUpTo (locConstCoeff Λ) ((forget X ⋙ onTests).mapCone c) r

variable {Λ R} {S : CommRingCat} (s : X ⟶ reprBy R) {T} {q : X ⟶ Y} {α} [Preorder α]
  {V : α → Subfunctor Y} (hV : Antitone V)

/-- If q: X → Y is relatively representable (affine) and Λ-cohomology is continuous over Y, that is,
turns filtered limits of functors affine over Y into colimits (`IsCohomContinuous`), then it is
continuous over X. -/
lemma IsCohomContinuous.of_isRelAffine (h : IsRelAffine q) (hY : IsCohomContinuous Λ Y) :
  IsCohomContinuous Λ X := fun _ _ _ _ c ↦ (hY (c := (map q).mapCone c) · ∘ (· · |>.comp h))

/-- For a decreasing family V of subfunctors of Y, the direct system a ↦ H^n(V_a, Λ) with
restriction maps, computed on test rings with locally constant Λ-valued coefficients. -/
noncomputable abbrev HV.antitoneFamily Λ n :=
  .mk _ (hV ·.le |> homOfLe |>.op) ⋙ onTests.op ⋙ cohFunctor (locConstCoeff Λ) n ⟨freeAb⟩

lemma IsCohomContinuous.isFilteredColimit_antitoneFamily {J} [SmallCategory J] [IsFiltered J] {D :
  J ⥤ α} (h : IsCohomContinuous Λ Y) (ht : ∀ j, IsRelAffine (V j).ι) {m : Cocone D} (e : ∀ {A x},
  (∀ j, x ∈ V (D j) A) → x ∈ V m.1 A) {n} : IsFilteredColimit ((HV.antitoneFamily hV Λ n).mapCocone
  m) := isFilteredColimit_iff_bijective.2 (forall_bijective_iff_bijectiveUpTo.2
  (h (isLimitOfPreserves _ (isLimitOfPreserves ((equivalenceMonoOver _).1 ⋙ MonoOver.forget _)
  (isLimitOfIsGLB _ (mapCone ((orderDualEquivalence _).2 ⋙ hV.dual_left.functor) m.op)
  ⟨conePt_mem_lowerBounds .., fun _ _ _ _ ↦ by aesop⟩))) (by tauto)) n)

/-- For s: X → h_R, the contravariant functor sending an R-algebra S to the functor X ×_{h_R}
h_S, forgetting its projection to X. -/
def baseChangeFunctor := ((opEquivOpUnder R).2 ⋙ post uliftCoyoneda ⋙ pullbackOver s) ⋙ forget X

/-- For X over h_R and a homomorphism f: S → T of R-algebras, the induced map of base changes
X_T → X_S. -/
abbrev baseChangeTransition {a b} (f : S ⟶ T) (h : a ≫ f = b) : baseChangeOf s b ⟶ baseChangeOf s
  a := (baseChangeFunctor s).map (Under.homMk f h : Under.mk a ⟶ .mk b).op

/-- If Λ-cohomology is continuous over X → h_R (`IsCohomContinuous`), S is an R-algebra and T an
S-algebra, then the cohomology of X_T is the colimit of the cohomologies of X_{S'} over the
subalgebras S' of T generated over S by finite subsets. -/
lemma IsCohomContinuous.isFilteredColimit_adjoin (h : IsCohomContinuous Λ X) T [CommRing T] [Algebra
  S T] a n : IsFilteredColimit (((baseChangeFunctor s ⋙ onTests).rightOp ⋙ cohFunctor (locConstCoeff
  Λ) n ⟨freeAb⟩).mapCocone ((Under.map a).mapCocone (J := Finset T) (F := .mk (S.mkUnder <| adjoin S
  (A := T) ·) (adjoin_mono ·.le |> inclusion |>.toUnder)) ⟨_, .mk fun _ ↦ (val _).toUnder⟩)) :=
  isFilteredColimit_iff_bijective.2 (forall_bijective_iff_bijectiveUpTo.2
  (h (isLimitOfPreserves _ (isLimitOfPreserves (_ ⋙ _ ⋙ pullbackOver s)
  ((reflectsColimit_of_reflectsIsomorphisms _ (Under.forget R ⋙ forget _)).1 (isColimitOf' _ _
  (by exact (⟨{·}, ⟨_, by simp⟩, rfl⟩)) fun _ _ _ ↦ (⟨_, 𝟙 _, SetCoe.ext ·⟩))).some.op)) fun _ ↦
  .baseChange (.map uliftCoyoneda _) isPullback_fibreProd) n)

/-- If q: h_T → Y is relatively representable (affine) with dense image on test rings for
locally constant Λ-valued functions, then Λ-cohomology turns small filtered limits of
functors affine over Y into colimits (`IsCohomContinuous`).

Known result: Descent of torsion étale cohomology along v-covers; excision, transfer, limits. -/
lemma IsCohomContinuous.of_atlas {q} (r : @IsRelAffine (reprBy T) Y q) (hq : HasCohomDenseImage Λ
  q) : IsCohomContinuous Λ Y := fun J _ _ D c hc d n ↦ have := IsFiltered.isConnected J; by
  induction' n with _ ih generalizing D; tauto
  have ⟨B, e⟩ : Σ B, .op B ⋙ uliftCoyoneda ≅ D ⋙ pullbackOver q ⋙ forget _ :=
    ⟨.unop _, liftFunctorCompIso _
    uliftCoyoneda fun _ ↦ ⟨_, ⟨((d _).isPullback _).isoIsPullback _ _ isPullback_fibreProd⟩⟩⟩
  let ⟨E, θ, _, s⟩ := Envelope.exists_functorial_test (Option.rec (colimit B) B)
  let ε : pullbackOver q ⋙ forget _ ⟶ forget Y := .mk (fibreProd.snd _ ·.3)
  let p := whiskerRight (NatTrans.op (B.whiskerLeft θ)) _ ≫ e.1 ≫ D.whiskerLeft ε
  let K {D} o e : HasCohomDenseImage Λ (reprMap _ ≫ Iso.hom e ≫ ε D) :=
    hq.of_preimage_le (mapOnTests _) fun A _ ⟨_, k⟩ ↦ ((e.app _).toEquiv.surjective.comp
    (ULift.map_surjective.2 (s o A)) ⟨(_, _), k⟩).imp fun _ ↦ (congrArg (·.1.2) ·)
  let a := coneOfPreserves (toArrowFunctor (.mk p)) (reprFunctor.mapCone (cocone _).op) hc
  let _ m : (cech Arrow.leftToRight m).IsCorepresentable := ⟨isTerminalPUnit.from
    (ULift _), ⟨.mk (.mk ((cech ..).map · ⟨.up, by tauto⟩) (fun e ↦
    ⟨↾(e.1 ·.1), ↾fun _ ↦ _, by ext; apply e.2 _ 0⟩) (by ext; exacts [rfl, congr($(·.w) _)]))⟩⟩
  refine .of_cech (onTests.mapArrow.mapCone a) (K ·.1 (e.app _) |>.isCohomEquiv)
    ((K none ((isLimitOfPreserves _ (isColimit _).op).conePointsIsoOfNatIso (isLimitOfPreserves _
    (isLimitOfReflects _ hc)) e)).mono ?_).isCohomEquiv (continuousUpTo_locConstCoeff (by tauto) _)
    fun m ↦ ih (Over.lift (toArrowFunctor (.mk p) ⋙ cechFunctor _) (
    .mk (p · |> (cech.proj · _ 0)) ≫ p ≫ .mk fun _ ↦ hom _)) (raiseCone ((cechFunctor _).mapCone a))
    (evaluationJointlyReflectsLimits _ (let v := (evaluation ..) ·; fstSndJointlyReflectLimit
    (c := v.mapArrow.mapCone a) (isLimitOfPreserves (uliftCoyoneda ⋙ v) (isColimit _).op)
    (isLimitOfPreserves v hc) |> isLimitOfPreserves (cech ..))) (.comp ?_ <| .comp ?R <| d ·)
  erw [(hc.hom_ext fun _ ↦ ?_ : _ ≫ _ = reprMap (post ..) ≫ _), mapOnTests, whiskerLeft_comp]
  apply range_comp_le
  simp; erw [← ε.2, map_π_assoc, fac, ← map_comp_assoc, ← op_comp, θ.2, ← ι_post]
  exacts [rfl, m.rec (.of_isIso ..) fun _ h ↦ (h.comp ?R).baseChange (.flip isPullback_cech),
    .comp (.map uliftCoyoneda _) (.comp (.of_isIso ..) (r.baseChange isPullback_fibreProd.flip))]
