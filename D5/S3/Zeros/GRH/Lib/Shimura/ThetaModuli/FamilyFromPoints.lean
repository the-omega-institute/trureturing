/- GID: D5/S3/Zeros/GRH/Lib/Shimura/ThetaModuli/FamilyFromPoints
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/ThetaModuli/FamilyFromPoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.ThetaModuli.FamilyFromPoints. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/ThetaModuli/FamilyFromPoints.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.ModelAlongArc
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Moduli of abelian varieties by theta values (theta-null embedding, universal family)
(known result; see Lib.Shimura.ThetaModuli.UniversalFamily).

This file: Closure of theta points is an abelian scheme with action and theta structure. -/


open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory NumberField
  ThetaObject Obj LineBundle PointFn AddObj Scheme ThetaTorus PeriodMap Category Over Spec
  IsLocalRing Fint
attribute [local simp] pullback.lift_fst pullback.lift_snd IsHomogCoords.pull_iff paddingTuple
  doubledCoeffs thetaProduct pull_pi coordSection
  landsIn_iInf AddChar.map_add_eq_mul Finset.prod_ne_zero_iff Int.cast_smul_eq_zsmul funext_iff
attribute [-simp] map_smul
variable {V ι κ : Type} [FinComplexSpace V] {S} [IsReduced S] [IsLocallyNoetherian S] [Finite ι]
  {η : κ → _} (j : ι → κ) (hη : @IsDenseFamily ι S (η <| j ·))

omit [Finite ι] in
lemma LineBundle.IsHomogCoords.pi {K X t V} [Fintype K] {M : K → LineBundle X ι} {θ : ι →
  V → ℂ} {w : K → V} (h : ∀ l, (M l).IsHomogCoords (A := ⟨ℂ⟩) t (θ · (w l))) :
  (LineBundle.pi M).IsHomogCoords t fun μ ↦ ∏ l, θ (μ l) (w l) := by simp_all [IsHomogCoords]

include hη

/-- Let A be flat and proper over S with reduced closed fibres, with maps e_i: V → A(ℂ) dense in
reduced fibres over dense points. If addition, zero and an O-action on V extend to morphisms
of A, then A is an abelian scheme with O-action. -/
lemma exists_isAbelianScheme {O A} [CommRing O] {e : ∀ i, V → (Over.mk (η i) ⟶ A)} (he : ∀ i,
  IsSeparatingFamily fun v ↦
  (lift (e i v) (𝟙 _)).1) (s : IsSeparatingFamily fun s : κ × V ↦ (e s.1 s.2).left) [Flat A.hom]
  [IsProper A.hom] (red : AllSpecializeTo S fun t ↦ IsReduced (pullback A.hom t)) {f : O → _} {F :
  κ → O →+* V →L[ℂ] V} (q : ∀ d i z, e i z ≫ f d = e i (F i d z)) m o (hm : ∀ i y z, e i (y + z) =
  lift (e i y) (e i z) ≫ m) (ho : ∀ i, toUnit _ ≫ o = e i 0) : ∃ (_ : IsAbelianScheme A) (_ :
  ModuleObj O A) (ε : ∀ _, V →+ _), e = (ε · ·) ∧ ∀ c i z, c • e i z = e i (F i c z) := by
  obtain ⟨t, _ : Flat (A ⊗ A).hom⟩ := s.prod hη s.1 (he ·.1), Flat.comp (pullback.fst ..) _
  have := t.prod hη s.1 (he ·.1.1)
  refine let _ : AddObj A := { AddGrpObj.mk (toAddMonObj := ⟨o, m, (λ_ A).inv_comp_eq_id.1 (?_ :
      lift (toUnit A) (𝟙 A) ≫ _ = _), (ρ_ A).inv_comp_eq_id.1 (?_ : lift (𝟙 A) (toUnit A) ≫ _ = _),
      (α_ A A A).inv_comp_eq.1 ?_⟩) (f (-1)) ?_ ?_ with add_comm := ?_ }
    let _ := @ModuleObj.mk _ O _ A _ (fun T ↦ @.ofMinimalAxioms _ _ _ _ ⟨flip (· ≫ f ·)⟩
      (have := isAdditive_of_universal (f := f ·) ?_; (add_comp · · _)) (fun _ _ ↦
      (· ≫= ?_ |>.trans (comp_add ..)))
      (fun _ _ ↦ (· ≫= (?_ : _ = _ ≫ _))) (· ≫= (?_ : _ = 𝟙 A))) fun _ _ _ ↦ (assoc ..).symm
    ⟨.mk (toSmooth := open HasRingHomProperty RingHom MorphismProperty Hom Pullback in
    smoothLocus_eq_top_iff.1 (top_unique fun y _ ↦ have ⟨k, _, _, t, a, H⟩ := red (A.hom y)
      have ⟨⟨x, b, a⟩, U', u, n⟩ :=
        And.intro ((isClosedMap _).specializingMap a) (exists_isAffineOpen_landsIn t)
      let ⟨W, v, m, e⟩ := exists_isAffineOpen_mem_and_subset ((mem_preimage _).2 (a ▸ n ⟨⟩))
      let := (appLE _ U' W e).1.toAlgebra
      b.mem_open (smoothLocus _).2 ((formallySmooth_stalkMap_iff U' u W v e m).2
        (@.of_formallySmooth_fiber _ _ _ _ _ (flat_appLE _ u v _) (finitePresentation_appLE _ u v _)
        _ _ _ _ ⟨rfl⟩ (smooth_algebraMap.1 (Spec_iff.1 (of_isPullback (.paste_horiz (.of_horiz_isIso
        ⟨(fiberToSpecResidueFieldIso ..).2.w⟩) (isPullback_fiberToSpecResidueField_of_isPullback
        (.of_horiz_isIso_mono ⟨id_comp _⟩) (Spec.map _ _))) (by
      erw [← Hom.comp_apply, u.SpecMap_appLE_fromSpec _ v, Hom.comp_apply, v.fromSpec_primeIdealOf,
        a]
      exact instDescendsAlongSchemeSmoothMinMorphismPropertySurjectiveFlatQuasiCompact.1
        (isPullback_fiberToSpecResidueField_of_isPullback (.paste_vert (.of_hasPullback ..)
        (.of_hasPullback _ t)) (id (closedPoint k))).flip (by and_intros <;> infer_instance)
        (of_isPullback (.of_hasPullback ..) (comp_mem _ _ _ inferInstance ((pullbackAddObj
        t).of_chart _ (Opens.ι _) ((pullback.snd _ t).dense_smoothLocus_of_perfectField
        |>.nonempty_iff.2 (exists_preimage_pullback x _ a).nonempty).to_subtype (by
        simp [← smoothLocus_eq_top_iff, ← preimage_smoothLocus_eq])))))))).1))))
    fun m hm ↦ m.cast_smul_eq_nsmul O (𝟙 A) ▸ s.2.surjective _ _ fun z ↦ congr($(q m _ ((m⁻¹
    : ℂ) • z.2)).1).trans (by simp [← smul_assoc, hm]), ‹_›, (.mk' _ <| hm ·), rfl, q⟩ <;> exact
    IsSeparatingFamily.hom_ext ‹_› (by simp +zetaDelta [← hm, q, ← assoc, Hom.add_def,
    AddMonObj.add] <;> grind)

unseal ThetaObject.groupScheme ThetaObject.toFamily in
/-- Let S be reduced, locally Noetherian, embedded over R (Spec R → Spec O_E mono, β̄ − β and
|T| units) by systems c lifting level coordinates of theta tori x_k at points η_k over
Φ_{v₀}, finitely many dense. Under cl (`IsCutOutAt`) and cv, S carries a family
modelled on x_k at η_k.

Known result: Moduli of abelian varieties by theta values (theta-null embedding, universal
family). -/
theorem exists_thetaFamily_of_points {E} [Field E] [CMBase E] {D : PEL E} {R} {π : S ⟶ Spec R}
  {φ : 𝓞 E →+* R} (hd : Mono (specMap φ)) (ho : ∀ i c, (preimage (η i ≫ π ≫ specMap φ)).hom c = Φ v₀
  c.val) {g ℓ : κ → _} {c : D.levelTorsion → LineBundle S D.T} {x : ∀ k, ThetaTorus D (g k) (ℓ k) V}
  (hc : ∀ ω, (c ω).IsLinearSystem) [Fintype D.levelTorsion] (hπ : (pi c).IsProjEmbedding π) (hx :
  ∀ i ω, (c ω).IsHomogCoords (η i) ((x i).thetaCoord · ((x i).torsionLift ω))) (hβ :
  IsUnit (φ (star D.β - D.β))) (hT : IsUnit (Nat.card D.T : R)) (cl : AllSpecializeTo S fun t ↦ ∃ 𝔭,
  IsCutOutAt D.r D.i (thetaRanks D.T D.r) c t 𝔭) (cv : ∀ t s, ∃ o, ∀ (l : D.T) k, l + k ∈ [o, -o,
  s - o] → t ∈ (c ⟨l, D.T_le_levelTorsion l.2⟩).opens k) : ∃ X : ThetaFamily D S (π ≫ specMap φ),
  ∀ i, ∃ m : TorusModel (X := X) (η i) (x i).toPeriodMap, m.θ = fun μ v ↦ (x i).thetaCoord v μ := by
  have u := @Valuation.one_apply_le_one ℂ NNReal
  have ⟨A, N, e, hN@⟨hn, _, _⟩, _, hl, he, red, s₁⟩ := exists_flat_closure j hη hc
    (Nat.le_of_lt D.three_le_r) D.degree_spec.1 (x · |>.thetaCoord_vector_ne_zero)
    (fun i ↦ have k z : IsIntegralCoords _ fun _ ↦ ⟨_, u _⟩ := ⟨1, by
                                simpa using (x i).thetaCoord_vector_ne_zero z⟩
    (x i).isCutOutAt_reduction (φ :=
      algebraMap ..) (by tauto) (x i).hasGoodReduction_trivial k (fun _ ↦ k _) (hx i)) cl
  have s₀ : IsSeparatingFamily fun i ↦ (toUnit (Over.mk (η i))).1 := ⟨‹_›, hη.of_comp⟩
  obtain ⟨s₂, ⟨a, hA, h₁⟩, b, -, h₂⟩ := s₁.prod hη s₁.1 (he ·.1), D.exists_padding
  choose σ hσ hσ' using (s₀.exists_map_of_coords (hW := hc ·) hN (hx · _) (hl · _))
  -- Riemann's relation has regular coefficients where suitable theta constants are units
  have H (a : Fin (D.r - 3) → 𝓞 E) (c : 𝓞 E) (h : star c * c + 3 + ∑ l, star (a l) * a l = D.r)
    (ψ := fun c : _ × _ ↦ ite (c.1 = 1) (fst ..) (ite (c.2 = 1) (snd ..) (toUnit _ ≫ σ 0))) (b := by
    simp +zetaDelta [← comp_left, -lift_left, hσ, hl, hA]) :=
    let P b := paddingTuple (cond b a 1) (cond b c 0)
    have q b :
      IsRiemannTuple (P b) D := by cases b <;> simp [IsRiemannTuple, P, D.three_le_r, ← h] <;> ring
    (exists_isLinearSystem (fun b a ↦
      ((x a.1.1).thetaProduct (doubledCoeffs (P b) (P !b)) · a.1.2 a.2)) s₂ (.pi fun l ↦ hn.pull
    (ψ (doubledCoeffs (P false) (P true) l)).1) (forall_imp (fun _ ↦ .pi) b) fun b μ s ↦
    let y := ∑ l, star (P b l).1 • μ (.inr l) - ∑ l, star (P (!b) (.inr l)).1 • μ (.inl (.inr l))
    (cv _ y).elim fun o a ↦ let ν := Sum.elim (cond · (y - o) o) (μ ∘ .inl ∘ .inr)
      ⟨_, by exact ⟨⟨a 0 _ (by simp), a 0 _ (by simp)⟩, ⟨⟩⟩, fun q ↦ Sum.elim (μ ∘ .inr - (·.1 • q)
        ∘ P b) (ν + (·.1 • q) ∘ P !b), _, ((((hc 0).mul (hc 0)).1 (o, y - o) (μ (.inl (.inl true)),
    μ (.inl (.inl false)))).1.mul (isRegularOn_ofSection ((hT.map (toSpecΓ R ≫
        π.appTop).hom).unit⁻¹.1 * ↑(D.rTorsion.relIndex D.T).sqrt))).pull (A ⊗ A).hom, fun ⟨⟨i, u⟩,
        v⟩ U ↦ by simp [ofSection_eq, hx .., by simpa [hx ..] using U, P, ν, ↓Over.w, mul_assoc,
        ← by simpa [P, ν, mul_assoc] using (x i).riemann_relation (w := u) (q b) rfl (q !b) (μ :=
        μ ∘ .inr) (μ' := ν) (by simp [ν, y, P]) v, mul_left_comm ((x i).thetaCoord o 0)⁻¹]⟩).elim
      fun _ H ↦ (s₂.exists_map_of_coords H.1 (isProjEmbedding_pi _ (fun _ ↦ hN) (Pi.hom_ext _ _))
      H.2.1 fun z ↦ .pi (t := (Pi.lift fun k ↦ e _ _).1) fun k ↦ by
      simpa [← comp_left] using hl _ _).imp fun _ k ↦ And.intro (k.1 ⟨⟨·, ·⟩, ·⟩) (k.2 ▸ H.2.2)
  obtain ⟨g, hg, -⟩ := H a (-1) (by simp [← h₁])
  let μ k := g ≫ Pi.π _ (.inr (.inr k))
  choose f q using (Submodule.mem_span (x := ·) |>.1 (hA.ge ⟨⟩) (AddSubgroup.ofSub {d | ∃ f, ∀ i a,
    e i a ≫ f = e i ((x i).intAction d a)} ⟨1, 𝟙 _, by simp⟩ fun _ ⟨f, h⟩ _ ⟨k, l⟩ ↦ ⟨lift k f ≫ μ
    (.inl true), by simp [*, μ, ← assoc, neg_add_eq_sub, sub_eq_add_neg]⟩).toIntSubmodule
    fun | _, ⟨l, rfl⟩ => ⟨lift (𝟙 A) (𝟙 A) ≫ μ (.inr l), by simp [μ, hg, ← assoc]⟩)
  obtain ⟨_, _, e, rfl, hA⟩ := exists_isAbelianScheme j hη he s₁ red
    q (μ (.inl false)) (σ 0) (by simp [μ, hg, ← assoc]) (by simp [hσ])
  let ψ (c : 𝓞 E × 𝓞 E) := c.1 • fst A A + c.2 • snd A A
  have G i l h := by simpa using (OverMorphism.ext (hN.eq_of_isHomogCoords (by simp)
    (funext ((x i).thetaCoord_mem_thetaSpace · |>.2 l h 0) ▸ hl i _)
    ((hl i 0).smul (by simp [(x i).isAppellHumbert_periodLattice.ne_zero h]))) :)
  have w : D.HasClassLaws N.picClass := by
    simp_rw [PEL.HasClassLaws, Pic.ParallelogramLaw, ← forall_and]
    intro T y z
    have w {c a} h (y z : T ⟶ A) := (H a c h ψ).elim fun g k ↦ by
      simpa -implicitDefEqProofs [ψ, fun l ↦ (s₂.hom_ext (by simp [*, ← assoc]) : g ≫ Pi.π _ l =
        ψ (doubledCoeffs (paddingTuple a c) (paddingTuple 1 0)
        l)), -lift_left, ← pull_comp, ← comp_left] using (congr($(k.2).pull (lift y z).1))
    have := congr(($(w h₁ z 0) - $(@w (-1) a (by simp [← h₁]) z y), $(w h₂ y 0) - $(w h₂ y z),
      $(w h₂ z 0) - $(@w (-star D.β) b (by simp [← h₂, mul_comm]) z z),
      $(w h₁ y 0) - $(w h₁ y (star D.β • z))))
    simp [Pic.pairing, Pic.atPoint, sub_smul,
      D.star_beta] at this ⊢; clear * - this; grind [sub_eq_add_neg]
  have hp i := isGroupBaseChange_counit (A := A) (η i)
  let L i : (.mk (η i) ⟶ A) →ₗ[𝓞 E] _ := ((hp i).pointEquiv (T := 𝟙_ _)).symm.1
  have H i u : (L i u).1 = (lift u (𝟙 _)).1 :=
    pullback.hom_ext (by simpa using! (hp i).1.lift_fst ..) (by simpa using! (L i u).w)
  have U i d h := by refine ((x i).exists_uniformisation_of_dense d h (hN.of_isPullback (hp i).1) ?_
    (.comp (L i) (e i)) ?_ ?_ ?_) <;> simp +contextual [Pic.ParallelogramLaw,
    w.1 _, ↓(hp _).atPoint_picClass_pull, H, hl, G]; apply he
  have dim := smoothOfRelativeDimension_of_fibres s₁.2 (U ·.1 · · |>.choose_spec.2.2.2)
  choose u t using (U · (abelianDim E D.Index) (by simp; infer_instance))
  let ς :
    D.levelTorsion →ₗ[𝓞 E] _ := by use! σ <;> exact fun a b ↦ s₀.hom_ext fun i ↦ sub_eq_zero.1 (by
              simp [hσ, hA, PeriodMap.torsionLift, intAction, ← toRealVectors_smul, ← map_add,
                ← map_sub]; exact G i _ ⟨_, by simp, rfl⟩)
  refine ⟨{
    A := A, N := N, class_laws := w, relative_dim := dim, embeds := hN, η := ς
    theta_law t T _ _ q h := by
      as_aux_lemma =>
        have L i l k := by simpa [thetaShift_apply, ← eq_inv_mul_iff_mul_eq₀,
          ← PeriodMap.torsionLift.eq_1]
          using ((x i).thetaShift_thetaCoord (s := l) (frameTorsionClass_ratLift _) k)
        choose W r hr hW v using fun l m ↦ ((cv _ m).elim fun o H ↦ ⟨_, _, (((hc _).mul (hc 0)).1
          (-o - l, m - o) (m - o - l, -o)).1, landsIn_iff_mem.2 ⟨H l _ (by simp), H 0 _
          (by simp)⟩, by simp +contextual [hx .., sub_eq_add_neg, field, zero_add (_ : V) ▸ L ..]⟩ :
          ∃ W r, IsRegularOn r W ∧ LandsIn t W ∧ ∀ i, LandsIn (η i) W → r _ (η i) =
          (x i).bicharacter (torsionLift_mem ..) m)
        have F f g (h := by simp +contextual [v, bicharacter_neg_eq_swap]) (a : IsRegularOn f _ ∧
          IsRegularOn g (iInf W.uncurry) :=
          by simp +contextual [IsRegularOn, hr _ _ _]) := a.elim s₀.pointFn_ext h _ t (by simp [hW])
        refine ⟨fun s ↦ ⟨(r s · _ t), F _ 1, fun _ _ ↦ F _ (_ * _)⟩, fun s u ↦ F .., fun u s ↦
          exists_isSectionLift_coordSection _ _ fun l m B y a b ↦ ⟨⟨u.1 • l - s, by simp [N.5,
          landsIn_preimage.1 a, ↓H0_smul, smul_smul, AddChar.val_isUnit, IsUnit.map,
          -AddChar.coe_mk]⟩, fun j ↦ ?_⟩, fun s h ↦ H0_ext fun _ _ _ _ a ↦ s₁.pointFn_ext
          (hn.1 ..).1 (hn.1 ..).1 (by simp +contextual [hl .., thetaCoord_eq_of_mem_lagrangian _ s
          h]) _ _ a, by simpa using hT.map (preimage (t ≫ π)).hom,
          fun s h ↦ by simpa using! F (∑ l : D.lagrangian.addSubgroupOf D.T, r s l ^ 2) 0 (by
          simp +contextual [v]; exact fun i _ ↦ (((x i).bicharacter _ ^ 2).compAddMonoidHom
          (AddSubgroup.subtype _)).sum_eq_zero_iff_ne_zero.2
            (h ∘ (x i).mem_lagrangian_of_bicharacter_sq s ∘ DFunLike.congr_fun))⟩
        let f := translation (σ ⟨s, D.T_le_levelTorsion s.2⟩)
        have w := by simpa [f, ← h.translation_comp] using h.smul_id_comp u.1 =≫ f.1
        have R m := ((hr s m).pull A.hom).mul (hn.1 l (u.1 • (s + m))).1
        choose _ H using (x · |>.exists_thetaCoord_sign_smul u)
        simpa [↓H0_smul, ← hr _ _ _, hW, f, ← w, -comp_add] using! s₁.pointFn_ext ((R j).mono
          inf_le_left) (((R m).mul ((hn.1 ..).1.pull ((u.1 • 𝟙 A) ≫ f).1)).mono inf_le_right) (by
          simp +contextual [v, hl .., L, H, ← comp_left, field, f, hσ, ← map_zsmul, ← map_add])
          _ (y ≫ q.1) (by simp [f, ← w, LandsIn.comp, hW, -comp_add]; tauto)
    signature b _ s _ := Spec_stalkClosedPointTo_fromSpecStalk
      s ▸ by as_aux_lemma => simpa using (exists_isLieChart dim _).imp fun V ⟨z, m, J⟩ ↦ ⟨z, _,
      J rfl, .of_points (stalk_eq_zero_of_dense hη) (fun ⟨i, _, E⟩ ↦ (x (j i)).4.elim fun ε he ↦
      ((u _).hasSignature_iff (F := (x (j i)).intAction) (by simp
      [t, ← hA]) (J E) (hp _) (x (j i)).isPeriodMap.finrank_eq_abelianDim).2 (by
      use ε.symm ((1, 0), 0), ?_, ?_, Φ v₀ (star D.β.val - D.β) • .fst .. ∘ₗ .fst .. ∘ₗ ε.1 <;>
        simp +contextual [by simpa [← E] using ho (j i), ← ε.injective.eq_iff, D.emb_beta_eq_of_ne,
        fun a z ↦ by simpa using congr($(he a) (ε z)), Prod.ext_iff, sub_mul, map_smul])) _
      (.map _ (by simpa [← assoc] using hβ.map (preimage
        (S.fromSpecStalk (s (closedPoint _)) ≫ π)).hom))⟩
    eq_of_list_eq _ _ h b := hπ.ext (by simpa [← hσ'] using! congr(pi $(funext b))) (hd.1 _ _ h) },
    fun i ↦ ⟨⟨ho i, _, _, _, (t i).1, fun c w ↦ by simpa [*, intAction] using! ((L i).map_smul
    c (e i ((x i).Q w))), (by simpa [t] using! congr(L i $(hσ · i))), (t i).2.2.1⟩, rfl⟩⟩
