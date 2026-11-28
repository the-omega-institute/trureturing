/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/PrimitiveComparison
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/Primitive/PrimitiveComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.Primitive.PrimitiveComparison. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/Primitive/PrimitiveComparison.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.SmoothBaseChange.SmoothBaseChange
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Primitive comparison theorem and period isomorphism (known result; see
Lib.PadicComparison.CrystallineFrobenius.CrystallineCohomology).

This file: Primitive comparison and finiteness of mod p cohomology for smooth proper varieties. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor


open CategoryTheory TensorProduct Functor AlgebraTensorModule AlgebraicGeometry TotalH Function
  PadicTest Abelian.Ext ConcreteCategory Comparison DirectSum ULift CommRingCat Over
variable {p} [ThePrime p] {M} {R : CommRingCat} (Ω) [Field.{0} Ω] [Algebra R Ω] [Algebra Ω ℂ_[p]]

/-- Valuative criterion in a p-adic test: for Y proper over R and a p-adic test with ring S,
given a map Spec S → Spec R, restriction from the points of Y over R in S to those in S[1/p]
is bijective. -/
lemma PadicTest.bijective_generic_points {Y : Over (Spec R)} [IsProper Y.hom] (c :
  PadicTest) {a b r w} : Bijective ((uliftYoneda.{1} Y).map (.op (X := .mk b) (Y := .mk a) ⟨Spec.map
  (ofHom (algebraMap c.ProdRing c.GenericRing)), r,
  w⟩)) := have := QuasiCompact.compactSpace_of_compactSpace Y.hom
  ⟨fun x y h ↦ down_injective
    (OverMorphism.ext (up.inj ((isProperOver_pointsToBase Y.hom).ext_of_jointly_injective
    _ (c.eq_zero_of_algebraMap_genericRing · <| · ()) fun _ ↦ congr(⟨$h.1.1⟩)))), fun z ↦ by
    have H i := (CommSq.mk ((ofHom_comp ..).symm.trans (congr(ofHom $(IsLocalization.Away.lift_comp
      (S := c.GenericRing) (g :=
      (algebraMap _ (FractionRing (c.Cell i))).comp (Pi.evalRingHom _ i)) (p : c.ProdRing)
      (by simp [-map_natCast, IsCell.p_ne_zero]))).symm.trans (ofHom_comp ..)))).op.map Scheme.Spec
    have l i := ((UniversallyClosed.eq_valuativeCriterion.le _ _ _ inferInstance).1 ⟨_, _, _, _,
      (H i).horiz_comp ⟨z.1.w.trans w.symm⟩⟩).1.some
    refine (pointsPi_surjective (of <| c.Cell ·) _ (l · |>.l)).elim fun x e ↦ ⟨⟨homMk x
      (pointsPi_injective _ _ (funext fun i ↦ by simpa [pointsPi, ← congrFun e] using (l i).3))⟩,
      down_injective (OverMorphism.ext
      (up.inj ((isProperOver_pointsToBase Y.hom).ext_of_jointly_injective _ (fun t h ↦
      ?_) fun i ↦ down_injective (((H i).w_assoc x).trans (congrFun e i ▸ (l i).2 :)))))⟩
    obtain ⟨r, u, rfl⟩ := exists_associated_localization t
    simp_all [← funext_iff, ← Pi.zero_def, (u.isUnit.map _).ne_zero]⟩

/-- For a scheme Y over R, the map Y(S) → Y(S[1/p]), natural in the p-adic test S; the hypothesis
`he` says that R → Ω → ℂ_p agrees with R → O_C → ℂ_p. -/
noncomputable def toGenericPoints [Algebra R OC] (he : ∀ r, algebraMap Ω ℂ_[p] (algebraMap R Ω r) =
  algebraMap R OC r) Y : testPoints Y ⟶ genericTestOver Ω ⋙ ObjectProperty.ι _ ⋙ algPointsOf Ω R
  Y := whiskerRight (H := _ ⋙ restrictAlg .. ⋙ restrictAlg R Ω) ⟨fun c ↦
  CommAlg.homOfRingHom _ (he · ▸ c.structMap_coe _ |>.symm), by
  intros; ext; symm; apply mapGeneric_algebraMap⟩ (algPointsOf R R Y)

set_option backward.isDefEq.respectTransparency false

/-- Primitive comparison. Let Ω be algebraically closed, Y proper with `IsCharted` over Ω, and
B ↦ B ⊗ M satisfy `IsAcyclicOnPerfect` (acyclic for tilting at every perfect O^♭-algebra). Then
ℤ[Y_Ω] satisfies `FP`, each Hⁿ(Y_Ω, 𝔽_p) is finite, and `primitiveMap` ⊗ M is bijective on
cohomology along Y(S) → Y_Ω(S[1/p]).

Known result: Primitive comparison theorem and period isomorphism. -/
lemma finite_and_primitive_comparison [IsAlgClosed Ω] (ac : IsAcyclicOnPerfect (moduleCoeff
  (tensorCoeff M))) Y [IsCharted Y Ω] [IsProper Y.hom] : let X := testIncl ⋙ geomPoints R Ω Y; FP
    (freeAb X) ∧ (∀ n, Finite (H (freeAb X) (locConstCoeff ⟨ZMod p⟩) n)) ∧
  ∀ [Algebra R OC] he, CoeffCompBij primitiveMap (freeAbMap (Y :=
    X) (toGenericPoints Ω he Y ≫ whiskerLeft _ (whiskerLeft _ (algToBaseChange Ω Y))))
    (tensorCoeff M) := have := InvertsPrime.mk (NeZero.nat_of_neZero (algebraMap Ω ℂ_[p])).1.isUnit
  let := Module.restrictScalars (ZMod p) OFlat M
  let γ := isoWhiskerRight (NatIso.ofComponents (fun _ ↦ ((cancelBaseChange ..).symm ≪≫ₗ
    TensorProduct.comm ..).toModuleIso) fun _ ↦ ModuleCat.hom_ext tmul_ext :
    asModules (TestOver.toTest Ω ⋙ testIncl ⋙ locConstAlg) ⋙ tensorWith .. ≅ (_ ⋙ oFlatLocConst) ⋙
    tensorCoeff M) (moduleCoeff (𝟭 _))
  let b := Module.Free.chooseBasis (ZMod p) M
  let c : Comparison (TestOver.toTest Ω ⋙ oFlatLocConst ⋙ moduleCoeff (tensorCoeff M)) _ :=
    ⟨genericTestOver .., whiskerRight primitiveMap (moduleCoeff _)⟩
  let θ i := mk₀ (whiskerLeft _ (tensorWith.mk _ (b i) _ ≫ γ.1) ≫ c.2)
  let D :=
    ComparedTheory.mk _ _ θ (hasLineFormula_tiltTheory _ ac) (hasLineFormula_locallyConstant Ω)
           -- M ⊗ L is a sum of copies of L
  have i {Y Y'} (h : FP (freeAb Y)) (u : Y' ≅ _ ⋙ Y) : IsLerayHirschBasis D.b (freeAb Y) ↔
    c.IsBijective (freeAbMap u.1) := by
    let E := ((equivFinsuppOfBasisLeft b).symm ≪≫ₗ directSumRight ..).toAddEquiv.trans
      (congrAddEquiv (.trans (.ofBijective _ (h ..)) <| .ofBijective _ <|
      H.push_bijective_of_isIso γ.isIso_hom ·))
    erw [← bijective_total_iff_isBijective, (IsCohomEquiv.of_isIso _).bijective_totalH.of_comp_iff',
      ← E.bijective.of_comp_iff]
    refine .of_eq congr(Bijective $((?_ : (lerayHirsch ..).toAddMonoidHom =
      (mapThenComp ..).comp E.toAddMonoidHom)))
    ext
    simp [E, ← lof_eq_of (ZMod p)]
    erw [DirectSum.map_of, ← of_comp_homClass, ← of_comp_homClass, lerayHirsch_single,
      TotalH.map_comp_assoc, TotalH.map_comp_assoc]
    simp_rw [map_homClass, ← homClass_comp]; rfl
  have k := D.mem_of_isClosedClass_of_isCharting D.isClosedClass_isGood (@fun Y ↦
    D.isClosedClass_isGood.2 _ (relFreeAb.shortExact _).2 ((D.isGood_iff_of_isCohomEquiv (freeAb.map
    (Subfunctor.ι ⊥)) fun _ z ↦ (z (U := .whisker (Y := (offClosedFibre Y).toFunctor) ⊥ _) fun _ y
    _ ↦ (·.1.1.elim (eq_top_mono (by simp [IdealFamily.ofMaximalIdeal,
    IsLocalRing.maximalIdeal_eq_bot]) y.2))).isCohomEquiv).1 (D.isClosedClass_isGood.1 _
    (freeAb.hom_ext nofun)))) ‹IsCharted ..›.1 ⟨(i (hasFlatBaseChange_reprFunctor _)
    (isoOfAppBijective (toUnit _) (fun _ ↦ by exact ⟨fun _ _ _ ↦ congr(⟨$(CommAlgCat.hom_ext
    (by ext))⟩), (⟨⟨_root_.structureMap⟩, .refl ·⟩)⟩) ≪≫ isoWhiskerLeft _ (isoOfAppBijective _
    pointMap_ofSelf_bijective).symm)).2 (.transfer (ac _) (bijective_of_isIso ((moduleCoeff _).map
    (CommAlgCat.isoMk (.ofBijective _ (Algebra.TensorProduct.includeLeft_bijective
    ((bijective_const_of_isDomain (B := .of Ω)).of_comp_left up_injective)))).1))
    (by intros; erw [← (moduleCoeff
    _).map_comp_apply, ← map_comp_apply, CommAlgCat.isInitialSelf.hom_ext (_ ≫ _)]; rfl)),
    .of_surjective _ ((sectionEquiv ..).surjective.comp
    (bijective_const_of_isDomain (B := .of Ω)).2)⟩
  have h := (isAffinelyCovered_algPoints (·.2.2) Y).hasFlatBaseChange
  ⟨fun _ _ _ ↦ fun Φ n ↦ (bijective_iff_of_comm_sq (baseChangeMap_pull (𝟙 _) _) (map_bijective
    bijective_id (isBijective_algToBaseChange Ω Y (moduleCoeff
    Φ) n)) (by simpa using! isBijective_algToBaseChange ..)).2 (h ..),
    ((isBijective_algToBaseChange ..).finite_iff.2 <| k.2.of_injective _ <|
    of_injective ·), fun e ↦ (isBijective_algToBaseChange Ω Y _).trans ((i h
    (isoOfAppBijective (toGenericPoints Ω e Y) (·.bijective_generic_points))).1 k.1)⟩
