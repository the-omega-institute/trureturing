/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/CrystallineClasses
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/CrystallineClasses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.Crystalline.CrystallineClasses. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/Crystalline/CrystallineClasses.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicComparison.ToricTower.CrystallineLines
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Crystalline comparison, which says that p-adic étale cohomology with good
reduction is crystalline. Only crystallinity is proved here, with no filtration and no
identification with crystalline cohomology. The invariants come from p-complete torsion-free rings
modulo elements with divided powers, and they are compared on toric towers one coordinate at a time.
Source: Bhatt, Morrow, Scholze, Integral p-adic Hodge theory, 2018, Publ. IHÉS 128, Thm 1.1(i)
(first: Faltings, Crystalline cohomology and p-adic Galois representations, 1989); for the site,
Bhatt, Prismatic F-gauges, 2022, Rem. 2.5.12; for the line lemma, Andreatta–Brinon, Acyclicité
géométrique de B_cris relatif, 2013, Comment. Math. Helv. 88.

This file: Crystalline comparison on charts étale over tori, by adjoining roots of coordinates.
Čech–Alexander flat base change; crystalline classes span period-ring cohomology. -/

open Algebra.TensorProduct ULift TimesBNat CategoryTheory Comparison CommRingCat Envelope Fin
  IsDiscreteValuationRing LinearEquiv MvPolynomial RingHom Submodule TensorProduct
  CategoryTheory.Functor ObjectProperty Ideal.Quotient Module.Flat

variable {p : ℕ} [ThePrime p] {C C'} [Category C] [Category C'] {F F'} {c :
  @Comparison C C' _ _ F F'} {ψ : C ⥤ CommAlg OC} {ψ'} {η : ψ' ⟶ c.φ ⋙ ψ} {S : Type}

/-- Let t₁,…,t_n be unit-valued functions on U, and let T represent the points y of U with root
systems of all t_i(y). If root systems of units form lines (`RootSystemsAreLines`) on both
sides, bijectivity of the comparison on h_T implies it on U. -/
lemma Comparison.IsBijective.isBijectiveOn_of_rootSystems {n U T} (l : RootSystemsAreLines F ψ)
  (l' : RootSystemsAreLines F' ψ') (k : c.IsBijectiveOn η (reprBy T)) (t : Fin n → (U ⟶
  underlyingSet)) x (r : _ → _ →* T) (u : ∀ i A y, IsUnit (t i A y).1) (e : ∀ i, ⟨r i (.ofAdd 1)⟩ =
  t i T x) (H : ∀ (A : CommAlg _) y (s : _ → Multiplicative ℚ≥0 →* A), (∀ i, ⟨s i (.ofAdd 1)⟩ =
  t i A y) → ∃! f, pointMap x A f = y ∧ ∀ i, .comp f.1.hom (r i) = s i) : c.IsBijectiveOn η U := by
  induction' n with _ ih generalizing U
  exact (c.isClosedClass η).of_bijective (pointMap x) (by simp_all [AllBijective,
    Function.bijective_iff_existsUnique]) k
  let a := fibreProd.snd rootSystems.atOne (whiskerLeft _ (t 0))
  have L {C} [Category C] {F : AbFunctor C} {ψ} (h : RootSystemsAreLines F ψ) :
    IsLine F ((ψ.prod _).whiskerLeft a) :=
    isBijective_of_fibres (ψ.whiskerLeft _) (isPullback_fibreProd.map (restrictAlong _)) (by tauto)
  refine (L l').trans_iff.1 ((L l).trans ((forall_congr' ((isClosedClass ⟨.prod _ (𝟭 _),
    _⟩ (η.prod (𝟙 _))).2 _ (shortExact_induced (fibreProd ..)).2)).1 (·)
    (((ih ((incl _).whiskerLeft a ≫ t ·.succ) ⟨(_, _), e 0⟩ _ (by bound) (tail e) fun A ⟨(⟨a⟩, y),
    k⟩ s l ↦ ?_).trans isBijective_induced) · |> (funext pull_trans).symm.subst |>
    ((isBijective_induced (X := ψ ⋙ _ ⋙ fibreProd ..) _).of_comp_iff _).1)) rfl)
  convert H A y (cons a s) (cases k l) using 2
  erw [Subtype.ext_iff, Prod.mk_inj, up_inj, forall_fin_succ]; tauto

/-- Crystalline comparison on a chart. Given `CrysPeriodAlgebra`, O_C an R-algebra, and B étale
over R[X_1,…,X_d] by X_i ↦ t_i with all t_i units, the functor D ↦ Hom_R(B, D) on
O_C-algebras satisfies `HasCrysComparison`.

Known result: Crystalline comparison: p-adic étale cohomology with good reduction is crystalline. -/
lemma hasCrysComparison_chart [h : CrysPeriodAlgebra] {R} [CommRing R] [Algebra R OC] {d} {B :
  CommAlg R} (t : Fin d → B) (ht : Etale (polyEval t)) (hu : ∀ i, IsUnit (t i)) :
  HasCrysComparison (restrictAlg R _ ⋙ reprBy B) := by
  let G := Fin d → ℚ≥0
  let g := aeval (R := R) (AddMonoidAlgebra.of OC G <| Pi.single · 1)
  algebraize [g.1, polyEval t]
  have w x : g x ⊗ₜ 1 = 1 ⊗ₜ polyEval t x := tmul_one_eq_one_tmul x
  let e (A : CommAlg OC) := (AddMonoidAlgebra.lift OC A G).symm.trans (Pi.monoidHomMulEquiv (fun _ ↦
    Multiplicative _) _).1
  exact .isBijectiveOn_of_rootSystems rootSystemsAreLines_crysTest
    (·.isLine_rootSystems (isAcyclicAt_almostCoeff h.pFlat_smul_eq_zero) · · |>.rec fun a b ↦
    ((coeffCompBij_id_iff_restrict (.refl _)).1 (.periodAlg_of_almostCoeff
    (hasFlatBaseChange_reprFunctor _) h.2 (fun G ↦ (forall_congr' (Ten.devissage.isClosedClass.2 _
    (shortExact_induced _).2)).1 (·) ((isBijective_induced.baseChangeMap_bijective_iff
    (β := 𝟙 (_ ⋙ _ ⋙ G)) a).2 ((coeffCompBij_id_iff_restrict (.refl _)).2 isBijective_induced)))
    PadicTest.isPerfectTorsionFree_tilt (·.1.isPerfectTorsionFree_tilt)
    ((coeffCompBij_id_iff_restrict (.refl _)).2 b)) :)) (hasCrysComparison_of_etale G
    (.of _ (_ ⊗[MvPolynomial (Fin d) R] B))) (fun i ↦ {app _ := ↾(⟨·.1.1 (t i)⟩)})
    ⟨CommAlg.homOfRingHom includeRight.1 (by simpa using! C · |> w |>.symm)⟩ (e _ includeLeft)
    (fun i _ _ ↦ (hu i).map _) (up_inj.2 <| by simpa [g] using! w <| X ·) fun A ⟨y⟩ ↦ (e
    A).forall_congr_right.1 fun F k ↦ ((isPushout_tensorProduct ..).exists_desc (ofHom F.1) (ofHom
    y.1.1) (by ext <;> simp [g, algebraMap_toAlgebra]; exacts [(F.2 _).trans (y.1.2 _).symm,
                 up_inj.1 (k _)])).rec fun x ⟨a, c⟩ ↦ ⟨⟨CommAlg.homOfRingHom x.1 (F.2 · ▸ congr($a
    _))⟩, ⟨congr(⟨CommAlg.homOfRingHom $c.1 _⟩), fun _ ↦ by ext; exact congr($a _)⟩, by
    rintro ⟨z⟩ ⟨⟨⟩, n⟩
    cases (e A).injective (a₁ := z.1.comp includeLeft) (funext n)
    exact (isPushout_tensorProduct ..).hom_ext a c ▸ rfl⟩

/-- For an algebra G over S/𝔡(S), the functor B ↦ Hom(G, B/𝔡(B)) on p-torsion-free p-complete
S-algebras has flat base change: its cohomology commutes with flat extension of the
coefficients. -/
lemma FP.pdReduction_reprBy [CommRing S] G :
  FP (freeAb.obj (pdReduction (.id (S ⧸ _)) ⋙ reprBy G)) := let L : CrysTest S ⥤ _ :=
    (.mk (fun B ↦ {x : ULift (G ⟶ _) × (G → B) // ∀ g, (x.2 g : _ ⧸ pdIdeal B) = x.1.1 g}) fun f ↦
    ↾fun x ↦ ⟨(⟨_ ≫ (pdReduction (.id _)).2 f⟩, _), (congr((pdReduction _).2 f $(x.2 ·)))⟩)
  isClosedClass.of_bijective (Subfunctor.range (.mk fun _ ↦ ↾(·.1.1) : L ⟶ _)).ι (fun B ↦
    (Equiv.subtypeUnivEquiv
    fun y ↦ ⟨⟨(y, _), (Quot.out_eq <| y.1.1 ·)⟩, rfl⟩).bijective) fun _ _ _ ↦ fun _ ↦ by
    refine Ten.devissage.bijective_range_of_cech _ fun m ↦ have hy :=
        ((eval₂Hom (G.3.2.comp (pdQuotientMk S)) Prod.snd).liftOfSurjective_comp_apply
        (⟨.X ⟨0, ·⟩, by simp⟩) ⟨(pdQuotientMk _).comp _, fun _ ↦
        eq_zero_iff_mem.2 ∘ algebraMap_mem_pdIdeal S _⟩); Ten.devissage.isClosedClass.of_bijective
        (pointMap ⟨fun i ↦ ⟨(⟨CommAlg.homOfRingHom _ (Quot.ind (by simpa using! hy <| C ·))⟩, _),
        (.X ⟨i, ·⟩ |> hy |>.symm.trans (congrArg _ (by simp)))⟩, by tauto⟩) (fun B ↦
        .of_existsUnique _ fun e ↦ (Equiv.ulift.existsUnique_congr fun g ↦ ?_).2 (existsUnique_lift
        _ _ (aeval fun (i, g) ↦ (e.1 i).1.2 g) fun f h ↦ ?_)) (Ten.freeAb_reprBy _)
    have h : Function.Injective (·.1.2 : L B → _) := fun a b h ↦ by ext <;> simp_all [← a.2, b.2]
    erw [Subtype.ext_iff]; simp [← h.eq_iff, funext_iff, MvPolynomial.algHom_ext_iff]; rfl
    erw [← eq_zero_iff_mem, ← map_zero (e.1 0).1.1.1.1, ← h]; apply f.induction_on <;>
      simp_all [(e.1 _).2, show ∀ i, (e.1 i).1.1 = _ from (e.2 · 0)] <;> tauto

variable {R} [CommRing S] [CommRing R] {r : R →+* _ ⧸ pdIdeal S} {X : CommAlg R ⥤ Type 1} (V :
  Subfunctor X) [h : CrysPeriodAlgebra] [Algebra R OC] [Algebra S Amax] (i :
  pdReduction ocToAmaxModPd ⋙ restrictAlg R OC ⟶ CrysTest.restrictScalars S ⋙ pdReduction r)

/-- The comparison along the functor sending a p-adic test c to D = completed A_max ⊗ W(c^♭),
viewed over S, from coefficients D to B_max ⊗ D by x ↦ 1 ⊗ x. -/
noncomputable abbrev crysComparison :=
  Comparison.of (F := moduleCoeff (asModules (ι _))) (crysThickening ⋙ CrysTest.restrictScalars S :)
  (tensorWith.mk Bcris (1 : Bcris) (asModules (crysThickening ⋙ ι _)))

/-- The natural map V(c) → V(D/𝔡(D)) on p-adic tests c induced by `testToThickening`, D the
completion of A_max ⊗ W(c^♭) viewed over S. -/
noncomputable def toCrysPoints : PadicTest.algFunctor ⋙ restrictAlg R _ ⋙ V.toFunctor ⟶
  (crysThickening ⋙ CrysTest.restrictScalars _) ⋙ pdReduction r ⋙ V.toFunctor := whiskerRight
  (whiskerRight testToThickening (restrictAlg ..) ≫ crysThickening.whiskerLeft i) V.toFunctor

attribute [-instance] addCommGroupH

/-- Let S be a p-complete DVR, uniformiser p, r: R → S/𝔡(S) compatible with O_C → A_max/𝔡, V as
in `IsCharting`. If the period cohomology of V on p-adic tests is finite over B_max,
restrictions from H^n(V(D/𝔡), D), D over S, span it.

Known result: Crystalline comparison: p-adic étale cohomology with good reduction is crystalline. -/
lemma span_range_crysComparison_pull_eq_top (_ : IsIso i) [IsDomain S] [IsDiscreteValuationRing S]
  (hS : IsCompleteTorsionFree S) (hV : IsCharting V) (hp : Irreducible (p : S)) (F : ∀ n,
  Module.Finite Bcris (H (freeAb.obj (PadicTest.algFunctor ⋙ restrictAlg R _ ⋙ V.toFunctor))
  (moduleCoeff (asModules (crysThickening ⋙ ι _) ⋙ tensorWith Bcris Bcris)) n)) n :
  span Bcris (.range (crysComparison.pull (freeAbMap (toCrysPoints V i)) n)) = ⊤ := by
  obtain ⟨_, ⟨l⟩⟩ :=
    isTorsionFree_of_dvd_pow h.isSMulRegular_natCast (associated_pow_irreducible · hp |>.imp fun _ ↦
    (·.dvd)), @Amax.nonempty_adicBasis _ _ S _ _ _ rfl hp.prime.isMaximal_span_singleton hS.2
  algebraize [r, (algebraMap _ Bcris).comp (algebraMap S Amax)]
  let N := freeAb (pdReduction r ⋙ V.toFunctor)
  let L : CrysTest S ⥤ _ :=
    ObjectProperty.lift (IsCompleteTorsionFree ·.1) (ι _ ⋙ algBaseChange _ ⋙ algCompletion Amax _)
    (isCompleteTorsionFree_completion fun _ _ e ↦ ·.2.isSMulRegular_natCast.lTensor _ (mod_cast e))
  let o : _ ⟶ L ⋙ ι _ := (ι _ ⋙ algBaseChange _).whiskerLeft (algCompletion.of ..)
  let E A B : (L A ⟶ B) ≃ (A ⟶ CrysTest.restrictScalars _ B) := .trans (.mk _ .mk)
    (.trans (.ofBijective _ (isBijOnCompletion_completion.comp_bijective (o.1 A) B.2.2))
    ((algBaseChangeAdj.homEquiv ..).trans (.mk (⟨·⟩) (·.1))))
  let a : L ⊣ _ := .mkOfHomEquiv ⟨E, fun f ↦ (E ..).surjective.forall.2 fun g ↦ by
    simp [Equiv.symm_apply_eq]; ext; exact congrArg _ (o.naturality_apply f (1 ⊗ₜ _)), by tauto⟩
  have hN : FP N := hV.2 _ (FP.isClosedClass.comap (restrictAlong _)) fun b _ ↦
    ((FP.isClosedClass.comap (restrictAlong (@pdReduction p _ S ..))).of_bijective _
    (pointMap_algBaseChange_unit_bijective b.R) (.pdReduction_reprBy _) :)
  have b : CoeffCompBij (Ψ := (L ⋙ ι _) ⋙ asModules (𝟭 _))
    (by exact crysThickening.whiskerLeft (whiskerRight a.2 (asModules (ι
    _)))) (freeAbMap (toCrysPoints V i)) _ := (isBijective_of_adj (F := crysPeriodCoeff) a).trans
    (((Comparison.restrict ..).isBijective_congr (show 𝟙 _ ≫ toCrysPoints V i = whiskerRight
    testToThickening _ ≫ crysThickening.whiskerLeft (whiskerRight i _) by simp [toCrysPoints]; rfl)
    (.of_isIso _) (.of_isIso _)).2 (by exact hV.2 _ ((isClosedClass (.restrict ..)
    testToThickening).comap (restrictAlong _)) (hasCrysComparison_chart _ ·.etale)))
  let θ n := ofBijective _ (hN ..) ≪≫ₗ ofBijective (pullₗ ..) (b n)
  let t n := ofBijective _ (hN _ Amax Amax (asModules (ι _)) n)
  let u := pullₗ (φ := 𝟭 _) (Φ := asModules (ι _) ⋙ tensorWith ..) (N :=
    N) (whiskerRight o (asModules (𝟭 _))) (𝟙 N)
  refine (orderIsoMapComap ((t n ≪≫ₗ ofBijective (u n)
    (hN.isBijective_of_isReductionMod hS h.isCompleteTorsionFree (·.2) hp _
    (fun n v ↦ (exists_set_linearIndependent ..).elim fun s ⟨e, c⟩ ↦ have := (F n).equiv (θ n).symm
    e.ge.trans_lt (linearIndependent_one_tmul (S := Bcris) (linearIndependent_iff'.2 fun w a e d k ↦
    l.eq_zero_of_coord fun i ↦ linearIndependent_iff'.1 c w _ (((IsDerivedComplete.cohomology
      (·.2.isDerivedComplete) ..).exists_eq_of_approx hS.isDerivedComplete 0 (TensorProduct.lift
    (.lsmul .. ∘ₗ l.coord i) <| (t n).symm <| (u n).ker.subtype ·) (⟨0, v · |>.imp fun y e ↦ by
    simp [← e, Nat.cast_smul_eq_nsmul]⟩) ⟨∑ d ∈ w, a d • t n (1 ⊗ₜ d), by simpa⟩).elim fun _ e ↦ by
    simpa [smul_tmul'] using e.symm) d k)).lt_aleph0_of_finite) (L · |>.2) (fun _ _ _ _ ↦
    .comp_algebraMap)
    n)).baseChange .. ≪≫ₗ θ n)).symm.injective ((ker_mkQ _).symm.trans (LinearMap.ker_eq_top.2 ?_))
  ext z; exact (Quotient.mk_eq_zero _).2 (subset_span ⟨z, .symm (by
    simp [u, t, θ, ← H.push_comp, pullₗ, pull_id_eq_push]; exact (crysComparison.pull_push _ _ _ (by
    ext; exact congr(⟨_ ⊗ₜ $(a.4 _) _⟩)) ..).trans (Abelian.Ext.comp_mk₀_id _))⟩)
