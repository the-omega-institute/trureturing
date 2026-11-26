import OmegaMath.NumberTheory.GRH.Lib.Cohomology.ProjectiveLine.NormalizationPullback
import OmegaMath.NumberTheory.GRH.Lib.PadicComparison.HodgeTate.GaloisTwist
import OmegaMath.NumberTheory.GRH.Lib.Cohomology.Hodge.PointClass
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Hodge–Tate image of dX/X is the units extension class mod (ker θ)². Cup product with
the Hodge–Tate image of a point class on P¹ is injective. -/

open thickeningOver CategoryTheory CommAlgCat MvPolynomial NNRat TotalH PadicTest WittVector freeAb
  CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false

variable {p k} [Field k] [EmbeddedInQpBar p k]

/-- The morphism from ℤ[𝔸¹∖0] to the multiplicative group A ↦ A^× (written additively) on
k-algebras, sending [v] to the coordinate of v, a unit. -/
noncomputable def Gm.ofCoord : freeAb (@unimodular k _ 1).toFunctor ⟶ forget₂ .. ⋙ Gm :=
  desc (fun _ v ↦ ⟨(by
  simpa [unimodular, Set.range_unique] using v.2 : IsUnit (v.1.1 0)).unit⟩) (by simp [ext]; tauto)

/-- The morphism t ↦ 1 − μt from the additive group of T = R[1/p] to the units of B =
W(R^♭)[1/p]/(ker θ)², on p-adic tests with ring R; μ = [ε] − 1. -/
noncomputable def thickeningOver.oneSubMu : genericCoeff ⟶ thickeningOver ⋙ forget₂ .. ⋙ Gm :=
  ⟨fun c ↦ AddCommGrpCat.uliftFunctor.map
  (AddCommGrpCat.ofHom (MonoidHom.toAdditiveRight (.toHomUnits ⟨⟨(1 - mulMu c ·.toAdd), by simp⟩, by
    simp [mul_sub, ← mulMu_proj_mul, proj_mulMu, sub_sub]⟩))), fun _ _ _ ↦ AddCommGrpCat.ext fun _ ↦
  Gm.ext.2 ((_root_.map_sub ..).trans (congrArg₂ _ (map_one _) (map_mulMu ..))).symm⟩

lemma thickeningOver.shortExact_oneSubMu : ∃ w,
  ShortComplex.ShortExact ⟨oneSubMu, whiskerRight proj _, w⟩ := by
  choose s i e using exact_mulMu_proj
  exact shortExact_of_app (fun c _ _ h ↦ congr(⟨$(i c (sub_right_inj.1 (Gm.ext.1 h)))⟩)) (fun c
    ⟨u⟩ ↦ .trans (by simpa [Gm.ext,
    sub_eq_zero.trans eq_comm, eq_comm.trans sub_eq_iff_comm] using! e c (1 - _)) ULift.exists.symm)
    fun c ⟨u⟩ ↦ (s ..).elim fun _ h ↦
    ⟨⟨((IsNilpotent.isUnit_quotient_mk_iff ⟨2, c.ker_thickeningProj_sq⟩).1
    (.of_map (RingHom.quotientKerEquivOfSurjective (s c)) _ ⟨u, h.symm⟩)).unit⟩, Gm.ext.2 h⟩

/-- For d = 1, λ₁[dT/T] is `restrictToPairs` of the boundary, for the pair (𝔸¹, 𝔸¹ ∖ 0), of the
pull-back along T of the extension 0 → R[1/p] → B^× → R[1/p]^× → 0, with B =
`thickeningOver`, first map t ↦ 1 − μt. -/
lemma hodgeTateMap_symbolClass : hodgeTateMap 1 symbolClass =
  restrictToPairs (((relFreeAb.shortExact _).2.map_of_exact (restrictAlong _)).extClass.comp
  (H.map _ (genericOver.whiskerLeft Gm.ofCoord) 1 shortExact_oneSubMu.2.extClass) rfl) := by
  choose ω hω eω using symbolClass_one k
  simpa [eω] using!
    (comp_assoc_of_eq (Comparison.pull_comp_restrictAlong ..) _).symm.trans ((congrArg _ (by
    simp [Comparison.pull, H.map, H.push, Abelian.Ext.toTotalH]
    erw [comp_assoc_of_eq (Cocycle.cohomClass_naturality ⟨_,
      _⟩ _ _ (𝟙 _) (by intros; erw [Category.comp_id])).symm, comp_id, ← homClass_comp_of]
    refine Cocycle.cohomClass_comp_eq_extClass _ (shortExact_oneSubMu.2.map_of_exact (restrictAlong
      _)) _ _ (fun _ ↦ Gm.ofCoord _ ≫ Gm.map (CommRingCat.ofHom (.pullbackFst ..))) (fun _ ↦ ?_)
      fun X _ f ↦ AddCommGrpCat.hom_ext (FreeAbelianGroup.lift_ext _ _ fun ⟨⟨v⟩, u⟩ ↦ (hω _ ⟨_,
      unimodular.map (X.toSqZero) u⟩).elim fun m ⟨h, e⟩ ↦ ?_) <;> simp [← Functor.map_comp]
    congr with ⟨⟩; tauto
    erw [e, ← sub_eq_iff_eq_add', desc_of, Gm.ext]
    show _ * (1 - (thickeningOver.mulMu ..) (-(contraction f.2 (.ι _ m)).algebraMapInv)) = _ + _
    erw [mul_one_sub, ← mulMu_proj_mul, proj.naturality_apply, (v 0).2, ← h, map_smulₛₗ]
    simp [contraction]; rfl
    simp [Cocycle.cocycle_comp, ↓NatTrans.naturality_assoc])).trans
    (Comparison.pull_comp_restrictAlong (relFreeAb.shortExact _).2.extClass ..))

lemma thickeningOver.teichmullerLift_epsTilt c : teichmullerLift c (algebraMap _ _ epsTilt) = 1 +
  mulMu c 1 := by simp [map_one c.thickeningProj ▸ mulMu_thickeningProj c 1, mu]; erw
  [MonoidHom.comp_apply, ← map_teichmuller]; rfl

seal genericAlg thickeningOver

/-- For k embedded in Q̄_p, λ_1 of the class of [1:0] in ℙ¹ comes from a degree-2 class η on
p-adic tests such that x ↦ x × η has zero kernel on Ext^n(N, R[1/p]) for every flat-valued
abelian functor N and every n. -/
lemma projSpace.exists_hodgeTateMap_pointClass_line : ∃ η, hodgeTateMap 1 (pointClass 1
  (@affinePoint k _ 1 _ 0 0)) = restrictToPairs η ∧ ∀ {N n} [HasFlatValues N] (x : H N genericCoeff
  n), _root_.cup (genericAlg ⋙ forget₂ ..).mulPairing x η (add_comm 2 n) = 0 → x = 0 := by
  have D {V U} [s : @IsChartCovered k _ 1 V] o : PairRestrictBijective (relFreeAb U) :=
    (((Comparison.restrict ..).isClosedClass HodgeTatePair.toGeneric).2 _ (relFreeAb.shortExact U).2
    (s.comap U.ι (by simpa)).pairRestrictBijective).1 s.pairRestrictBijective
  obtain ⟨ξ, ⟨hX, h₁, E⟩, G⟩ := (stdChart k 1 0).exists_isLocalSymbol (z := affinePoint 0 0) (g :=
    X) (fun _ _ ↦ by simp [ComesFromPoints]; erw [mk_eq_mk_iff_cross_mul]; simp +contextual
    [Set.range_unique]) ((mk_mem_stdChart_iff _).2 isUnit_one)
  obtain ⟨⟨ξT, hξ⟩, G⟩ :=
    (D isOpenSub_offPoints).exists_hodgeTateMap_eq 1 ξ, G.map_eq_smul_pointClass.symm
  apply_fun hodgeTateMap 1 at E G; simp [hodgeTateMap_map, *, hodgeTateMap_symbolClass,
    ← restrictToPairs_map] at *
  refine ⟨_, G, fun x s ↦
    DirectSum.of_injective _ ((comp_id.trans x.toTotalH.map_id).symm.trans ?_)⟩
  let A : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ _ ⋙ affineSpace k 1 :=
    ⟨(↾fun t ↦ ⟨fun _ ↦ teichmullerLift · (t.1.hom (.single 1 1))⟩),
    by intros; ext; with_unfolding_all exact congr(⟨fun _ ↦ .mk _ $(.symm ((IsLocalization.map_eq
    (powers_le_comap_powers ..) _).trans (congrArg _ (map_teichmuller ..))))⟩)⟩
  let b := A ≫ whiskerRight proj _
  have g c i t : b c ⟨charTwist epsPow (cond i coeHom (-coeHom)) ≫ t.1⟩ = b c t := by
    simp [b, A, affineSpace, charTwist, funext_iff, -AddMonoidAlgebra.coe_algebraMap]
    erw [((proj c).hom.1.1.comp
      ((teichmullerLift ..).comp ((algebraMap ..).1.comp epsPow))).mem_ker.1, one_mul]
    cases i <;> simp [teichmullerLift_epsTilt, proj_mulMu]
  let T : affineSpace k 1 ⟶ reprBy (stdChart k 1 0).R := ⟨fun _ ↦ ↾(⟨ofHom <| aeval ·.1⟩), by
    intros; ext; congrm ⟨ofHom $((comp_aeval ..).symm)⟩⟩
  let φ : twoDiscs ⟶ _ := sigma.desc fun i ↦
    b ≫ whiskerLeft _ (T ≫ pointMap (stdChart k 1 (i.1.rec 1 0)).point)
  have U c t : (A c ⟨discToTorus coeHom ≫ t⟩).1 0 * (A c ⟨discToTorus (-coeHom) ≫ t⟩).1 0 = 1 := by
    simp [A, ← map_mul, ← AddMonoidAlgebra.one_def]
  let W : _ ⟶ _ ⋙ freeAb unimodular.toFunctor := projFirst (B :=
    pointOrTorus) ≫ desc (.of ⟨_, span_eq_top_of_isUnit 0 <| .of_mul_eq_one _
    <| U · ·.1⟩) (by intros; exact .symm congr(.of $(Subtype.ext (A.naturality_apply ..).symm)))
  let ε {X} : freeAb X ⟶ genericCoeff := desc (fun c _ ↦ ⟨(1 : genericAlg c)⟩)
    (by intros; exact congrArg _ (map_one (genericAlg.map _).1).symm)
  obtain ⟨_, _, _, _, _, J, I⟩ := by
    apply toda_squares (oneSub_comp_gluing epsPow) (origin ⟨true⟩) (hom_ext (by simp -dsimp))
      ((relFreeAb.shortExact unimodular).2.map_of_exact (restrictAlong _)) shortExact_oneSubMu.2
      (projFirst ≫ freeAb.map b) (-W ≫ whiskerLeft _ Gm.ofCoord) (projFirst ≫ ε) (whiskerLeft
      _ Gm.ofCoord) (-W ≫ whiskerRight proj _) <;> apply freeAb.hom_ext <;> rintro c
      ⟨⟨⟨⟩⟩⟩ <;> simp [W]
    exacts [rfl, congr(.of $((g _ true _).symm)), sub_eq_of_eq_add (Gm.ext.2 (.symm (show (1 - mulMu
      c _) * _ = _ by
      erw [desc_of, desc_of, desc_of, IsUnit.unit_spec]
      simp [A, charTwist, pointOrTorus, AddEquiv.ulift, -AddMonoidAlgebra.coe_algebraMap,
        -Bool.cond_eq_ite]
      erw [AddMonoidAlgebra.lift_single]
      simp [-AddMonoidAlgebra.coe_algebraMap]
      erw [AlgHom.commutes, teichmullerLift_epsTilt]; rfl)))]
  have m A ψ := @relFreeAb.mk_eq_zero _ _ _ (offPoints {affinePoint 0 0}) A _ ((offPoints _).map ψ
    (a := (stdChart k 1 1).point)
    fun K ψ h ⟨_, rfl, e⟩ ↦ by have := h.nontrivial; simpa using (mk_mem_stdChart_iff ..).1 ⟨_, e⟩)
  obtain ⟨j', hj⟩ := by
    refine J _ _ (freeAb.map φ - origin ⟨false⟩ _ ≫ freeAb.map φ) (whiskerLeft _ (relFreeAb.π _))
      (whiskerLeft _ (relFreeAb.map T (fun _ v l ↦ hX.preimage_fieldLocus_not.ge _
      (.trans (congrArg _ (congrArg _ (funext (aeval_X _)))) l)) ≫ relFreeAb.map _ h₁)) (hom_ext ?_)
      (hom_ext (by simp [-Bool.cond_eq_ite]; simp [freeAb, φ, sigma.desc, g, -Bool.cond_eq_ite]))
        (hom_ext ?_) <;> rintro c ⟨⟨⟨⟩⟩⟩ <;> simp
    exacts [congr(.of $(mk_eq_mk_iff_cross_mul.2 (by
      simp; erw [aeval_X, aeval_X, mul_comm, ← map_mul (proj c).1, U]; simp))),
      (m ..).trans (m ..).symm, sub_eq_self.2 (m ..)]
  have q := congr(pullbackAlong $hj ξT.toTotalH).symm
  erw [← homClass_comp_homClass_comp, homClass_comp_of, whiskerLeft_comp, H.map_comp, (@D _ _
    (.comap _ (EtaleChart.isOpenSub _)) (isOpenSub_offPoints.preimage _)).injective_restrictToPairs
    E, ← H.map_comp, ← whiskerLeft_comp, show _ ≫ _ = 𝟙 _ from relFreeAb.hom_ext fun _ _ ↦
    congrArg (relFreeAb.mk unimodular ⟨·⟩) (funext (aeval_X _)), H.map_id] at q
  erw [map_zero, ← show tensorPoint ε _ ≫ (genericAlg ⋙ forget₂ ..).mulPairing = 𝟙 _ by
    ext _ ⟨⟩; exact congrArg _ ((mul_one_add ..).trans (by simp)), homClass_comp,
    TotalH.comp_assoc_of_sq (naturality ..), (I _ _ _ (subsingleton_coker_gluing
    isCohomEquiv_gluing_generic _)).1 _ (tensorPoint (𝟙 _) _) _ 0, map_zero]
  erw [← map_homClass, ← TotalH.map_comp_assoc, q, ← homClass_comp_homClass_comp, homClass_comp_of,
    TotalH.map_comp_assoc, (comp_assoc_of_eq rfl _).trans (cup_of ..), s] <;> simp +arith
