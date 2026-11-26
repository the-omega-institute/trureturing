/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/GaloisRep
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/PointClass/GaloisRep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.PointClass.GaloisRep. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/PointClass/GaloisRep.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Eigenspace.EigenQuotient
import D5.S3.Zeros.GRH.Lib.PadicComparison.HodgeTate.HodgeTateVectors
import D5.S3.Zeros.GRH.Lib.General.Geometry.Lefschetz
import D5.S3.Zeros.GRH.Lib.Cohomology.PointClass.ProjectivePointClass
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles.
Only non-vanishing and linear independence of the distinct point classes are proved, without duality
or a trace map. The proof treats first P¹, then projective space by products, then a smooth
projective variety by transfer along a finite linear projection. Source: Faltings, p-adic Hodge
theory, JAMS 1 (1988) (compatibility with traces and cycle classes); for the transfer,
Suslin–Voevodsky, Singular homology of abstract algebraic varieties, Invent. Math. 123 (1996),
§§4–6.

Known result: Galois representation cut out of cohomology by a Hecke eigensystem; Eichler-Shimura.
Here the representation is a quotient of total cohomology, not an isotypic part. No dimension or
semisimplicity is claimed, only good reduction, annihilation by the Hecke polynomial and occurrence
of given Hodge-Tate weights. Source: Deligne, Formes modulaires et représentations l-adiques, Sém.
Bourbaki 355 (1969), Thm 4.9; Harris and Taylor, The geometry and cohomology of some simple Shimura
varieties (2001), ch. VII; Wedhorn, Congruence relations on some Shimura varieties, J. reine angew.
Math. 524 (2000).

Known result: Half of the holomorphic Lefschetz (Woods Hole) formula for h-forms and
correspondences. No trace is computed here. If a combination of pull-backs kills the Hodge–Tate
images of the Hodge classes of weight h, then the z^h coefficients of the local terms
det(1−zA)/det(1−A) at simple coincidences add up to zero. Source: M. F. Atiyah, R. Bott, A Lefschetz
fixed point formula for elliptic complexes II, Ann. of Math. 88 (1968) 451-491; G. Kondyrev, A.
Prikhodko, Holomorphic Atiyah-Bott formula for correspondences, Arnold Math. J. (2022); SGA5 III
6.12.

This file: Hodge–Tate images of distinct point classes on a projective variety are linearly
independent. Half of holomorphic Lefschetz formula: killed Hodge–Tate classes force vanishing local
term sums. Galois representation from cohomology: good reduction, Eichler–Shimura relation,
Hodge–Tate weights. -/

open CategoryTheory Function CommAlgCat CutsOutLocus IsUnimodCoords projSpace MvPolynomial Finset
  RingHom Fin CommAlg IsLocalization Away Field Submodule Algebra Ideal EtaleChart
  CartesianMonoidalCategory MonoidalCategory

attribute [local instance] FractionRing.liftAlgebra FormallyEtale.of_isSeparable

/-- Let k be an algebraically closed field mapping to Q̄_p, and Y projective over R with Y_k
having an atlas of dimension d. Then the images under λ_d of the distinct classes cl(z), z
in Y(k), form a k-linearly independent family.

Known result: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles. -/
lemma linearIndepOn_hodgeTateMap_pointClass {p k} [Field k] [EmbeddedInQpBar p k] [IsAlgClosed k]
  {R} [Algebra R.1 k] {Y d} [hX : HasAtlas d (algPointsOf k R Y)] (hE : HasProjEmbedding Y.hom) :
  LinearIndepOn k (hodgeTateMap d) (.range (pointClass
  (X := algPointsOf k R Y) d)) := hE.rec @fun _ L _ hL ↦ by
  simp_rw [linearIndepOn_iff_notMem_span, ← Set.image_compl_preimage, Set.image_image,
    mem_span_image_iff_exists_fun]
  rintro _ ⟨z, rfl⟩ ⟨t, ht, n, H⟩
  have := Fact.mk hL
  choose a ζ w₀ ez hw₀ using exists_chart_coords L z (toIsField _)
  obtain ⟨_, _, q, m, hζ⟩ := isReduced_of_etale a.etale, FiniteType.isNoetherianRing k a.R,
    @exists_minimalPrimes_le _ _ (.colon ⊥ {(1 : a.R)}) _ (ker_isPrime ζ.1) (by aesop_cat)
  obtain ⟨_, γ, hψ⟩ := m.1.1, exists_eq_colon_of_mem_minimalPrimes m
  have ⟨ψ, V⟩ : ∃ ψ, ker ψ = q := ⟨algHom k .., q.ker_algebraMap_residueField⟩
  simp [← V, Ideal.ext_iff] at *
  choose n Λ e h using
    exists_isNoetherNormalization (k := k) (ne_iff.2 (hw₀.2.imp fun _ h ↦ (h.map ψ).ne_zero))
  let β := γ * evalForms Λ w₀ 0; let c := a.away β
  obtain ⟨⟨κ, ⟨⟩⟩, w, hw, w₁⟩ := (exists_toAway_comp_iff β (ofHom ψ)).2 (by
    simpa [β, comp_aeval_apply, *, ← sq] using hψ 1), (⟨_, hw₀.map_unit_smul (toAway β)
    (isUnit_of_dvd β (dvd_mul_left ..)).unit⁻¹, by simp [Units.smul_def]; rfl⟩ : ∃ w,
    IsUnimodCoords L _ w ∧ evalForms Λ w 0 = 1)
  obtain ⟨I, hg, u, E⟩ := injective_of_map_algebraMap_zero (M := .powers β) _ κ.1.1 fun r e ↦
    (isUnit_of_dvd β ⟨_, rfl⟩).mul_right_cancel (by simp [← map_mul, (hψ r).1 e]),
    hw.comp κ, (hw.comp κ).exists_unit_smul_eq ((hw₀.comp _).comp κ)
  obtain ⟨_, h, _, m, B⟩ := I.isDomain, eq_inv_smul_iff.2 E ▸ h _,
    hg.exists_mem_open_of_isUnit c.isOpenSub ⟨_, rfl⟩
  let y := aeval (R := k) (evalForms Λ w ∘ succ)
  algebraize [y.1, (κ.hom.comp y).1, κ.1.1, κ.1.1.comp y.1]
  let S := MvPolynomial (Fin n) k
  let M := IntermediateField.mk (.restrictScalars k (.algebraicClosure S q.ResidueField))
    fun _ ↦ .inv
  obtain ⟨⟨_, ⟨⟨φ⟩, ⟨⟩⟩, e⟩, _⟩ := @B (of k M) (⟨_, IsIntegral.isAlgebraic <| h.2 _ (cons 1 X) _
    .refl (funext (by simp [forall_fin_succ, y, *])) ·⟩) (.of_ker M.val 1 (by simp) .refl) (by
    simpa [← M.val.injective.ne_iff]), (faithfulSMul_iff_algebraMap_injective
    ..).2 (.of_ker y fun a _ ↦ by
    choose G c D using exists_homogenization (isHomogeneous_X _ 0) (a.rename succ) .refl
    simpa [D, comp_def, S, bind₁_rename] using h.1.map (aeval (cons (1 : S) X)) c (by
      erw [evalForms_map, ← comp_aeval]; simp [aeval_rename, y, *]))
  have G := IsAlgebraic.mk fun r ↦ (isAlgebraic_algebraMap_iff I).1
    (congr($(c.eq_comp_of_map_point_eq _ ((e.comp (ofHom M.val)).ext hg).symm) r ∈ M).mpr (φ.1 r).2)
  have ⟨δ, hδ, et⟩ := @exists_etale_of_isEtaleAt _ _ _ _ y.1.toAlgebra
    (.of_restrict_scalars_finitePresentation k ..) ⊥ _ (by
    delta IsEtaleAt Localization.AtPrime; rw [primeCompl_bot]; exact .comp _ (FractionRing S) _)
  let U := { c.away δ with coordinate := _, etale := congr($(comp_aeval _ (toAway δ).1).1.Etale).mp
                             (etale_algebraMap.2 et) }
  have e₃ := (c.mem_locus_away δ κ).2 (by simpa using! I.ne hδ)
  have o {A x v} (h : IsUnimodCoords L x v) h' ⦃T⦄ (b : T ⊆ (pointClass d ⁻¹' {pointClass d z})ᶜ) :
    x ∈ offPoints T A := fun K φ I ⟨y, m, e⟩ ↦ let := I.toField
    b m (pointClass_eq_of_functions_eq (hg.exists_function_const · |>.elim fun _ H ↦
      ez ▸ H (hw₀.comp ζ) (.of_ker _ _ hζ (E ▸ .smul
    (.id ..) _ .refl)) ▸ structureMap.1.injective (by simpa [e] using! H (h.comp φ) (.map _ h'))))
  choose b _ _ B T using hg.exists_mem_open_of_isUnit U.isOpenSub e₃
  obtain ⟨_, oU, F, q, r⟩ := e₃.choose.1.1.domain_nontrivial,
    o hw (.of_ker κ.1 1 (by simp [← I.eq_iff]) .refl),
    (G.1 (aeval w b)).exists_nonzero_coeff_and_aeval_eq_zero (by simpa [← I.ne_iff])
  obtain ⟨⟨⟩, ⟨q, m⟩, _, f, D⟩ := equiv_iff_eq.1 ⟨(c.away δ).nonempty_basis_kaehler.some.indexEquiv
    U.nonempty_basis_kaehler.some⟩,
    not_forall.1 (funext.mt q), exists_homogenization (Λ 0).2 (F.eval₂ (bind₁ (Λ ·.succ)).1 b) .refl
  let Q := projSpace.affinePoint (A := of k k) 0 q
  let Γ : Subfunctor (_ ⊗ projSpace k d) := ⟨fun _ x ↦ ∃ v h, IsUnimodCoords L x.1 v ∧ x.2 =
    projSpace.mk (evalForms Λ v) h,
    fun φ _ ⟨v, _, a, e⟩ ↦ ⟨φ ∘ v, evalForms_map Λ φ.1 _ ▸ ⟨_, a.comp φ, congrArg _ e⟩⟩⟩
  let π := Γ.ι ≫ fst ..
  have : Mono π := mono_of_app_injective (by
    rintro _ ⟨⟨⟩, _, _, a, ⟨⟩⟩ ⟨⟨⟩, _, _, a', ⟨⟩⟩ ⟨⟩
    congrm ⟨(_, $(mk_eq_mk_iff_exists_unit.2 ((a.exists_unit_smul_eq a').imp fun _ ↦
      (· ▸ (evalForms_smul _).symm)))), _⟩)
  let O := (offPoints t).preimage π ⊓ fieldLocus fun K x ↦ constMap Q K x = x.1.2 →
    x.1.1 ∈ U.locus K
  let j := O.ι ≫ π
  have hj {A} := injective_of_mono (j A)
  let C := U.comap j ⟨⟨(_, _), _, span_eq_top_of_isUnit 0 (by simp [*]), hw.comp _, rfl⟩,
    (offPoints _).2 _ (oU ht), fun _ _ _ _ ↦ ⟨_, rfl⟩⟩ rfl
  have P {A y} b : y ∈ C.locus A := (U.locus_comap j rfl).ge _
    (U.isOpenSub.fieldLocus_le _ (y.2.2 · · · (map_map_structureMap _ Q ▸ (congrArg _ b).symm)))
  obtain ⟨hV, s, hs⟩ := IsChartCovered.comap _ (h := ⟨fun K hK ↦ let := hK.toField
    by rintro ⟨⟨x⟩, _, H, ⟨a⟩⟩
       obtain ⟨c, κ, w, ⟨⟩, a'⟩ := exists_chart_coords L x hK
       obtain ⟨⟨u, ⟨⟩⟩, j, e⟩ := (a'.comp κ).exists_unit_smul_eq a, exists_isUnit_of_span_eq_top H
       exact ⟨(c.away _).comap π ⟨(_, _), _, span_eq_top_of_isUnit j
         (by simpa using (c.mem_locus_away ..).1 (point_mem_locus _)), a'.comp _, rfl⟩ rfl,
         (locus_comap _ π rfl).ge _ ((c.mem_locus_away ..).2 (by simpa [u.smul_def] using e))⟩⟩)
    (O.range_ι.substr (.inf (isOpenSub_offPoints.preimage _) (isOpenSub_fieldLocus fun _ _ ↦
    (IsSepFunctor.exists_ideal ..).elim fun _ h ↦
    (U.isOpenSub ..).imp' _ fun _ g _ φ f ↦ let := f.toField
    by erw [← map_map_structureMap φ Q, h, g, ← isAtom_top.ne_bot_iff_eq le_top, Ne,
      map_eq_bot_iff_le_ker, sup_le_iff, not_and]))),
    exists_isCoincidenceSet (constMap Q) (O.ι ≫ Γ.ι ≫ snd ..) (fun y b ↦ by
    obtain ⟨⟨ψ : U.R ⟶ _⟩, ⟨⟩⟩ := P b
    erw [← Functor.map_comp_apply, (U.lift_unique (π :=
      SqZeroExt.fst) fst_surjective_and_kerIdeal_sq ?_ fun j ↦ ?_ : _ ≫ _ = ψ)] <;> try rfl
    have := mk_eq_mk_iff_cross_mul (v := ψ ∘ _).1 b j.succ 0
    simp [w₁] at this ⊢; erw [this]; rfl) ![C] fun _ _ _ ↦ (⟨0, P ·⟩)
  have E {X} [HasAtlas d X] x := @(exists_diagonal_pointClass (X := X).choose_spec x).2.2 _
    ⟨fun A a b ↦ (hX.exists_ideal A (j.app A a) (j.app A b)).imp fun _ h B φ ↦
      hj.eq_iff.symm.trans (by erw [j.naturality_apply, j.naturality_apply]; exact h B φ)⟩ hV
  have J x t a := E x j t ⟨fun _ e ↦ hj (by erw [j.naturality_apply, e, map_map_structureMap]; rfl),
    a⟩
  exact (IsChartCovered.pairRestrictBijective.exists_hodgeTateMap_eq ..).elim fun η l ↦
    hodgeTateMap_pointClass_ne_zero Q (l ▸ by simp [(h.pullback_injective
    hg (O := O) (fun V a ↦ ⟨⟨_, _, a, rfl⟩, o a V ht, fun K φ I e ↦ let := I.toField
    (mk_eq_mk_iff_exists_unit.1 e.symm).rec fun u e ↦ ((T ..).ext (a.map_unit_smul φ u) ▸ B (V.smul
      ..) (.mk0 _ fun H ↦ m (by simpa [aeval_bind₁ _, *, congrFun (((evalForms_smul _).trans
      (congrArg _ _)).trans e), ← comp_def, aeval_algebraMap_apply, F.eval₂_eq_sum_range,
      sum_range_succ'] using V.smul φ.hom u f (IsHomogSolution.refl.map _ f
      (by simpa [*, F.aeval_def, F.eval₂_eq_sum_range, aeval_bind₁ w]
      using! r)))) :)⟩) (hV.pairRestrictBijective.injective_restrictToPairs (by
    simp_rw [restrictToPairs_map, ← l, ← hodgeTateMap_map, E _ _ _ hs, map_zero, map_sum]
    exact sum_eq_zero fun y h ↦ (P (hs.2.1 _ h)).elim fun ζ a ↦ by
      rw [← sum_singleton (pointClass d), ← J (j.app _ y) {y} ⟨fun _ h ↦ by
        cases mem_singleton.1 h; simp [constMap]; rfl, fun K _ x e ↦
        ⟨y, mem_singleton_self y, hj (e.trans (j.naturality_apply _ y).symm)⟩⟩,
        not_ne_iff.1
        (oU .rfl _ (_ ≫ ζ.1) (toIsField _) ⟨_, ·, by simp [← a]; rfl⟩)]
      simpa [← hodgeTateMap_map, fun i : t ↦ (J _ ∅ ⟨nofun, fun K hK x e ↦ ((mem_offPoints_iff hK).1
        x.2.1 ⟨_, i.2, e⟩).elim⟩).trans sum_empty] using congr(PairH.map (freeAb.map j) $H).symm)) :
          η = 0)])

open AlgebraicGeometry Polynomial Functor

set_option backward.isDefEq.respectTransparency false

/-- Half of the Atiyah–Bott formula. Let Y/R be proper, W/R projective, k algebraically closed,
Y_E and W_k with atlases of dimension d. If h > d, or ∑ b_i λ_h(u_i^*x) = 0 for all x ∈
Hdg^q(Y_E), q ≤ d, then ∑ b_i[u_i] is h-null (`IsNullFamily`).

Known result: Half of the holomorphic Lefschetz (Woods Hole) formula for h-forms and
correspondences. -/
lemma ellAdicCohom.woods_hole {p A E k d h I} [CommRing A] [Field E] [CharZero E] [Algebra A E]
  [Field k] [IsAlgClosed k] [EmbeddedInQpBar p k] [Algebra E k] {R : Subalgebra A E} {W Y :
  Over (Spec (.of R))} [IsProper Y.hom] {u} {b : I →₀ k} (hX : HasAtlas d (algPointsOf E _ Y)) (hW :
  HasAtlas d (algPointsOf k _ W)) (hE : HasProjEmbedding W.hom) (hF : h ≤ d → ∀ q ≤ d, ∀ x :
  HodgeH _ q, (b.linearCombination k fun i ↦ hodgeTateMap h (x.map
  (freeAb.map ((algPoints E _).map (u i : W ⟶ Y)))).baseChange) = 0) : IsNullFamily u b d h := by
  intro c S P hP
  obtain ⟨⟨φ, _⟩, ⟨δ, hδ⟩, ⟨_, a, _⟩, L, e⟩ := Module.exists_dual_forall_apply_eq_one
    (linearIndepOn_hodgeTateMap_pointClass hE), exists_diagonal_local_terms hX, hW.2,
    (LinearMap.pi (@leval k
    _)).dualMap_surjective_of_injective (fun _ _ ↦ funext ∘ congrFun) (Polynomial.lcoeff k h)
  let D u : algPointsOf k _ W ⟶ restrictAlg E k ⋙ algPointsOf E _ Y := (algPoints ..).map u
  let Φ t (i : b.support) : type_of% δ →+ HodgeH (freeAb (algPointsOf ..)) _ :=
    (H.map _ (freeAb.map (scaledGraph t (D (u i)) (D c))) d).comp HodgeH.baseChange
  have T := (hP · · |>.elim (IsTangentPoly.hasJacobianRatio (c := D c) hW.isChartCovered))
  choose s _ B A using fun i : b.support ↦ exists_isCoincidenceSet (D (u i)) _ (hX :=
    isSepFunctor_algPoints) (fun _ e ↦ (T ⟨i, _⟩ (by congrm _ ≫ $e.1)).2 _ rfl e) a (by tauto)
  have hδ i t : Φ t i δ = _ := (hδ _ _ _ _ _ (by tauto) (T ⟨i, ·⟩ congr($(B _ _ ·).1) |>.1 t)).2
  have e := (congr($e <| · * Polynomial.C ·))
  simp [LinearMap.pi] at e
  refine (Set.ext fun _ ↦ ULift.down_inj.trans ⟨(by simpa using A _ _ (Field.toIsField k) _ ·),
    B _ _ ∘ by simp⟩ : S = univ.sigma s) ▸ ⟨finite_toSet _, .trans (by
    simp [*, ↓finsum_mem_coe_finset, ← sum_fn, mul_sum, sum_sigma, division_def, mul_assoc,
    AddMonoidHom.pi]) ((∑ i, b i.1 • L.toAddMonoidHom.comp
    (.pi ((φ ∘ₗ hodgeTateMap d).toAddMonoidHom.comp <| Φ · i))).ker.1.closure_le.2 ?_ (kunneth δ))⟩
  intro δ ⟨q, _, _, x, _, r⟩
  have F t i : Φ t i δ = .map (freeAb.map (CartesianMonoidalCategory.lift (𝟙 _) (𝟙 _)) ≫
    freeAb.prod ..) _ := (congrArg _ (((congrArg _ r).trans (HodgeH.baseChange_map ..)).trans
    (congrArg _ ((@HodgeTest.baseComparison k _ E _ _).pull_cup abTensor_hom_ext x ..)))).trans
    ((H.map_comp ..).symm.trans (cup_map (Functor.mulPairing _) x.baseChange _ _
    (HodgeTest.scaleModule t _ ≫ Functor.whiskerLeft _ (freeAbMap (D _)))
    (Functor.whiskerLeft _ (freeAbMap (D c))) freeAb.hom_ext))
  simpa [F, e, H.map_comp, hodgeTateMap_map (_ ≫ _), hodgeTateMap_cup, hodgeTateMap_scale, ← sum_fn,
    AddMonoidHom.pi,
    -LinearMap.smul_apply, -LinearMap.coe_smul, ← @eval_X_pow k, -Polynomial.eval_pow] using!
    congrArg (φ ∘ₗ PairH.map _ ∘ₗ _) ∘ (sum_attach ..).trans ∘ (hF · q (by omega) x)

seal ellAdicCohom

open Matrix Module ellAdicCohom LinearMap Flat Filter IsEigenQuotient ModuleCat.Algebra Int

attribute [local simp] Model.cosetSum cosetFn smul_sum baseChange_comp
  ValuationSubring.valuation_eq_one_iff

/-- For a model of neat level over a localisation of O_E where safe primes survive, σ : ℂ ≅
ℚ̄_ℓ, and J supported at σ|E, in weights where θ occurs, some continuous ρ : Gal(Ω/E) →
GL_N(ℚ̄_ℓ) satisfies `SphericalClause` at each safe w, with jumps including J and the
Hecke polynomial of σθ_w.

Known result: Galois representation cut out of cohomology by a Hecke eigensystem;
Eichler-Shimura. -/
lemma Model.exists_galois_rep {E} [Field E] [CMBase E] {a d₀} [HasQuadSubfield _ E] {𝔑 ν R}
    (X : Model (Fin a) d₀ 𝔑 ν R) {ℓ} [NeZero a] (hN : IsNeat (Fin a) 𝔑) [ThePrime ℓ] [Algebra E Ω] M
    (hM : ∀ w, IsSafe 𝔑 w → M ≤ w.1.primeCompl) [_root_.IsLocalization M R] [PadicIso ℓ] (θ :
  SafePlace 𝔑 → _) J (hJ : ∀ u ∈ J, 0 ≤ u ∧ OccursInWeight a ν θ u.toNat) : ∃ ρ : PadicRep _ ℓ,
  Continuous ρ.rep ∧ ∀ w, SphericalClause ρ.rep
  OccursIn (if algebraMap E ℂ = · then J else 0) w.1.1 (heckePoly w.1.1.q a (ιℓ <| θ w ·)) := by
  rcases X.smooth, X.proper, X.projective, X.reduction,
    IsLocalization.isNoetherianRing M R inferInstance
  have := (X.covering · |>.smoothOfRelativeDimension_baseChange X.d)
  have ⟨_, _, _⟩ : IsCharted X.Z R ∧ IsCharted X.Z Ω ∧ ∀ i, IsCharted (X.W i) Ω := by
    and_intros <;> intros <;> exact ⟨(hasAtlas_algPoints X.d).exists_isCharting⟩
  choose hV V using fun n i ↦ transfer (X.covering i) ℓ n
  choose l p _ using fun w : SafePlace 𝔑 ↦
    (Eventually.all (X.eventually_translate ∅ <| heckeIsogeny_mem_GUPlus w.1 ·)).exists
  choose T hT' ht hW using fun n : Set.Iic (X.d + X.d) ↦ exists_commuting_tau_ops (hV n) (V n) p
  have e n w b := congr((baseChangeHom ℤ_[ℓ] Bcris .. ∘ₗ restrictScalarsₗ ..) $(ht n w b))
  simp [LinearMap.ext_iff, -Subtype.forall, heckeSum] at e ht
  have hT i s (g : Gal(Ω/E)) : Commute (T i s) ((galoisAction ..) g) :=
    LinearMap.ext fun x ↦ hV _ (l s.1) (by simp [ht, map_galoisAction])
  obtain ⟨N, r, F, ⟨h₃, H⟩, hr⟩ := exists_isEigenQuotient (ιℓ ∘ ↿θ) hT (continuous_galoisAction · E)
  use ⟨r⟩, hr, fun w A hA ↦ ?_
  have hR r : algebraMap (CommRingCat.of R) Ω r ∈ A :=
    A.mem_of_valuation_le_one _ ((IsLocalization.surj M r).rec
    fun x e ↦ le_of_mul_le_of_one_le_left (by simpa using! A.valuation_le_one ⟨_, congr(algebraMap
    R Ω $e ∈ A).mpr (algebraMap_ringOfIntegers_mem ..)⟩) (not_lt.1 (hM _ w.2 x.2.2 ∘ (hA _).1)))
  have hcr [PadicPlaceEmbedding E A ℓ] i := (isCrystalline_and_linearFrob_rel E hR i
    (X.m ∘ ![]) 0 1 0 (by simp [CongruenceRelation, Cancels]) nofun).1
  obtain ⟨⟨t, f, -, hp, _, hq⟩, C⟩ := w.1.1.1.exists_prime_and_absNorm_eq_pow,
    X.congruence _ w.2 _ (algebraMap _ Ω ⁻¹' A.nonunits) (hA · |>.2) (p w)
  rw [heckePoly, ← hA, ← @fact_iff t.Prime] at *; norm_cast at *
  refine ⟨⟨fun _ _ _ ↦ Units.ext (toLin'.injective (ext_on_range H.1 fun _ ↦ (h₃ ..).trans (by
    simp [*, galoisAction_eq_one_of_inertia hR _ hp]))), isCrystalline ⟨by tauto, H⟩ (hcr ·)⟩,
    fun he γ s hs u hu z ↦ ?_, fun s hs ↦ ⟨fun h ↦ ?_, @fun he _ k o ↦ ?_⟩⟩
  · simp [apply_ite] at hu
    obtain ⟨⟨h, rfl⟩, hO⟩ := (hJ u hu.2).imp_left le.dest
    let ε := ιℓ.trans s.toRingEquiv
    let : EmbeddedInQpBar ℓ ℂ := {ε.toRingHom.toAlgebra with}
    refine (exists_word_kill_of_jump_eq_zero ⟨by tauto, H⟩ (hcr ·) hs (by tauto) hT' z).rec fun c
      ⟨_, n⟩ ↦ hO _ (ε.symm ∘ c) (ε.injective (by simpa [map_list_prod])) fun b ↦
      X.isNullHecke_of_isNullFamily hN ((c.support.eventually_all.2 fun L _ ↦ .all (hW · ℂ L _
      b.2.1)).mono fun l a m ↦ woods_hole (hasAtlas_algPoints _) (hasAtlas_algPoints _)
      (X.projective l) fun hh q hq x ↦ (exists_hasHodgeTateWeight hR (fun r ↦ congr(ε
      ($(hu.1) r)).trans (by simp [ε])) X.d ε.symm ε.right_inv (x.map (freeAb.map
      ((algPoints ..).map (X.m m))))).rec fun v ⟨Θ, hv, K⟩ ↦ .trans ?_ ((sum_congr rfl fun L hL ↦
      congrArg (ε.symm (c L) • ·) (a L hL ⟨_, add_le_add hq hh⟩ (.mk' (Θ <| ·.restrictScalars _
      |>.baseChange _ v) (by simp)))).trans ?_))
    · simp [← K, HodgeH.map_comp]
    simpa [Finsupp.linearCombination, Finsupp.sum, c.support.sum_comm, smul_comm (ε.symm _)]
      using congr(cosetSum (fun g ↦ Θ (baseChange _ _ $(n ⟨_, _⟩ v hv))) b.1)
  · refine toLinAlgEquiv'.injective (ext_on_range H.1 fun ⟨i, x⟩ ↦ ?_)
    simp [↓Polynomial.C_mul', -cast_mul]
    conv_lhs => enter [2, b]; erw [mul_smul, cast_smul_eq_zsmul, ← map_pow (matrixRep r),
      h₃, ← H.2.1 _ (w, b), ← _root_.map_zsmul]
    rw [← _root_.map_sum, congrArg (F i) (hV _ (l w) ?_), map_zero]
    simpa [ht, sum_filter, sum_comm, (finrank_le _).trans_eq]
      using ellAdicCohom.congruence_relation hR (by simpa) hp (hq.rec hs) _ _ _ (C hq) x
  exact IsEigenQuotient.isKilledBy ⟨by tauto, H⟩ (w, ·) (hcr ·) o fun i y ↦
    lTensor_preserves_injective_linearMap (.restrictScalars ℤ_[ℓ] _) (hV i (l w)) (by
    simpa [← baseChange_eq_lTensor, e, sum_filter, sum_comm, (finrank_le _).trans_eq,
      ↓LinearMap.sum_apply] using! congr($((isCrystalline_and_linearFrob_rel E hR _ _ _ _ _ (C
      (o.eq_pow_of_isFrob (_root_.map_inv he.toGp _ ▸ he.isFrob_iff.2 hs))) fun _ ↦ o.pow _).2) y))
