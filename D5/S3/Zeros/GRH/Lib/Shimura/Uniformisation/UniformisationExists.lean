/- GID: D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/UniformisationExists
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/Uniformisation/UniformisationExists
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.Uniformisation.UniformisationExists. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/Uniformisation/UniformisationExists.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.ThetaGroup.ThetaStructure
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

Part of: Abelian schemes: isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified torsion (known
result; see Lib.Shimura.AbelianScheme.ThetaFamily).

This file: Smooth is geometrically reduced; an abelian scheme over an algebraically closed field is
integral. Torsion section of
invertible order vanishing somewhere vanishes (unramified torsion). Rigidified line bundles descend
along fpqc covers; pairing identities descend along isogenies. A complex abelian variety is a
complex torus: charts, compactness, uniformisation. -/

section

open CategoryTheory AlgebraicGeometry Algebra MorphismProperty TensorProduct Set LocallyOfFiniteType

lemma isReduced_of_etale {A B} [CommRing A] [CommRing B] [IsDomain A] {_ : Algebra A B} (_ : Etale A
    B) : IsReduced B := let F := FractionRing A; have := FormallyUnramified.isReduced_of_field F
  isReduced_of_injective _ (includeRight_injective (IsFractionRing.injective A F))

instance {X Y} s [@Smooth.{0} X Y s] : GeometricallyReduced s := ⟨fun _ _ _ _ _ t H ↦
  @isReduced_of_isReduced_stalk _ ((of_isPullback H ‹Smooth s›).exists_isStandardSmooth t
  · |>.elim fun U ⟨_, _, hV, hx, e, h⟩ ↦ have : Nonempty U := ⟨_, e hx⟩
  @isReduced_localizationPreserves _ _ _ _ _ (_) (hV.isLocalization_stalk ⟨_, hx⟩)
    (isReduced_of_etale h.exists_etale_mvPolynomial.choose_spec.choose_spec.2))⟩

/-- An abelian scheme over an algebraically closed field is integral: its points permute its
finitely many irreducible components. -/
instance {k} [Field k] [IsAlgClosed k] (A : Over (Spec ⟨k⟩)) [i : IsAbelianScheme A] : IsIntegral
    A.1 := @isIntegral_of_irreducibleSpace_of_isReduced _
  (GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.hom)
  ((irreducibleSpace_def _).2 ((nonempty_compl.not_left.1 fun h ↦ by
  have := (@finite_irreducibleComponents_of_isNoetherian _
    { isLocallyNoetherian A.hom, compactSpace_of_universallyClosed A.hom with }).to_subtype
  let G := (@AddAction.toPermHom _ (irreducibleComponents A.1) _ (by refine' { vadd g C := ⟨_,
    preimage_mem_irreducibleComponents C.2 (translation g).1.isOpenEmbedding (by simp [C.2.1.1])⟩,
    .. } <;> simp [(· +ᵥ ·), preimage, ← Scheme.Hom.comp_apply, ← Over.comp_left, add_assoc])).ker
  exact (exists_point_mem _ (isClosed_irreducibleComponent.1.isLocallyClosed.preimage
    (by fun_prop)) (h.preimage (i.nsmul_surjective _ G.index_ne_zero_of_finite).1)).elim fun x : _ ⟶
    A ↦ (· (congr($(show 0 ≫ translation _ = x ≫ _ by simp).1 _).subst (congr($(G.nsmul_index_mem x)
    ⟨_, irreducibleComponent_mem_irreducibleComponents _⟩).ge
    mem_irreducibleComponent)))).subst isIrreducible_irreducibleComponent))

open CartesianMonoidalCategory IsLocalRing Ideal Ideal.Quotient Spec AddMonObj

/-- Let B be an abelian scheme over a local ring R and m a natural number invertible in R. A
section x with mx = 0 that vanishes at some field-valued point of Spec R is zero. -/
lemma section_eq_zero_of_torsion {R K g} [CommRing R] [IsLocalRing R] {B : Over (Spec ⟨R⟩)}
    [IsAbelianScheme B] (hd : SmoothOfRelativeDimension g B.hom) {m : ℕ} (u : IsUnit (m : R)) {x}
    (e : m • x = (0 : _ ⟶ B)) [CommRing K] [Nontrivial K] {s : Spec ⟨K⟩ ⟶ _} (h : toUnit (.mk s) ≫ x
    = 0) : x = 0 := have ⟨I, hf, hI⟩ := exists_ideal_le_ker_iff_factors ζ[B].1 x.1
  by simpa [eq_zero_iff_factors_zero_section,
    I.eq_bot_of_le_smul_of_le_jacobson_bot _ (hf (locallyOfFinitePresentation_left (h := by
    simp; infer_instance))) (((hI _).2 (eq_zero_iff_factors_zero_section.1
    (((by simpa [IsInfinitesimal, eq_zero_iff_factors_zero_section,
    ← Spec.map_comp] using! (hI (Ideal.Quotient.mk I)) : IsInfinitesimal (CommRingCat.ofHom
    (factor mul_le_left)) (toUnit (specOver ..) ≫ x)).nsmul_injective_and_eq_zero (h := ⟨by simp_all
    [factor_surjective, eq_zero_iff_mem, ← map_mul, Ideal.Quotient.mk_surjective.forall,
    Ideal.mul_mem_mul]⟩) hd (toUnit _) m).1 (u.map (algebraMap ..)) (by simpa using _ ≫=
    e)))).trans_eq mk_ker) (by simp_all [eq_zero_iff_factors_zero_section, jacobson_eq_maximalIdeal,
    (le_maximalIdeal (RingHom.ker_ne_top (Spec.preimage s).hom)).trans'])] using hI (.id R)

end

attribute [-simp] CategoryTheory.MonoidalPreadditive.whiskerLeft_zero

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Over LineBundle Pic
variable {k} [Field k] {A₀ : Over (Spec ⟨k⟩)} [IsAbelianScheme A₀] [IsIntegral A₀.left] {S}
  {A A₁ A' B B' : Over S} [AddObj A'] [AddObj B] [AddObj B'] {p q}
  (hp : IsPullback p A'.hom A₀.hom q) (f : A ⟶ A₁) [Flat f.1] [Surjective f.1] [QuasiCompact f.1]
include hp

/-- Let A' be a base change to S of an abelian variety, and f : A → A₁ flat, surjective,
quasi-compact over S. A class in Pic(A₁ × A') that is trivial on A × A' equals its pull-back along
(x, a) ↦ (x, 0). -/
lemma eq_pull_zero_section c (h : pull (f ▷ A').1 c = 0) : c = pull (A₁ ◁ 0).1 c := by
  obtain ⟨_, L⟩ := c; have ⟨u, hu⟩ := exists_isFrame_of_picClass_eq_zero h
  have H {T b} (a : T ⟶ _) (e : a ≫ f ▷ A' = b) := congr(L.pull $e.1) ▸ hu.pull a.1
  have hw := hu.mul (H _ (whisker_exchange _ 0)).inv
  refine picClass_eq_iff.2 (@exists_isFrame_of_fpqc _ _ _ _ _ ?_ ?_ ?_ _ hw fun i B t t' E m ↦ ?_)
  iterate 3 apply_rules [MorphismProperty.overPullbackMap]
  have ⟨s, G⟩ : ∃ s, ∃ y x : mk (Y := Spec B) s ⟶ _, x.1 = t ∧ y.1 = t' :=
    ⟨_, homMk _, homMk _ (by simpa using E =≫ hom _), rfl, rfl⟩
  obtain ⟨⟨y, z⟩, ⟨x, _⟩, rfl, rfl⟩ := homEquivToProd.symm.surjective.exists₂.1 G
  obtain ⟨E, _⟩ := congrArg homEquivToProd (OverMorphism.ext E : _ ≫ _ = _ ≫ _), hw.2 i B _ m
  have ⟨r, hr⟩ := (H (y ▷ _) rfl).exists_eq_mul (H (x ▷ _) (by aesop)).1
  have H j a h := (hr j _ (lift (𝟙 (mk s)) a).1 h).trans congr($(hasConstFunctions_of_isPullback
    (.paste_horiz (.flip
    (.of_hasPullback ..)) hp) r _ _ (lift (𝟙 _) z).1 (by simp [Limits.pullback.lift_fst])) * _)
  simp_all [← comp_left, -lift_left]; grind

/-- Let A' be a base change of an abelian variety, f : A → A₁ flat, surjective, quasi-compact,
and b, b' homomorphisms on A'. If ⟨a(x), b(y)⟩_c = ⟨a'(x), b'(y)⟩_c' for all points x of A₁
factoring through f and y of A', it holds for all x. -/
lemma pairing_eq_of_fpqc_cover {c c'} a (b : _ ⟶ B) [IsAdditive b] a' (b' : A' ⟶ B') [IsAdditive b']
  (h : ∀ ⦃T⦄ (x : T ⟶ A) y, pairing c (x ≫ f ≫ a) (y ≫ b) =
  pairing c' (x ≫ f ≫ a') (y ≫ b')) ⦃T⦄ (x : T ⟶ A₁) y : c.pairing (x ≫ a) (y ≫ b) =
  c'.pairing (x ≫ a') (y ≫ b') := by refine (.mp ?_ congr(pull (lift x y).1 $(eq_pull_zero_section
  hp f (c.pairing (fst .. ≫ a) (snd .. ≫ b) - c'.pairing (fst .. ≫ a') (snd .. ≫
  b')) ?_))) <;> simp_all [pairing, Pic.atPoint, ← Pic.pull_comp, ← comp_left, -lift_left]

omit hp

open AnalyticAt ContinuousLinearEquiv Fint PointFn IsLocalRing Matrix MvPolynomial TopologicalSpace
  Topology ContinuousLinearMap.HasRightInverse
variable {A : _} {T ι d t₀} [TopologicalSpace T] {γ : T → ComplexPoint A} [Finite ι] {N :
  LineBundle A.left ι}

/-- The classical topology. -/
instance : TopologicalSpace (ComplexPoint A) := .induced
    (fun x U f O ↦ IsRegularOn f U ∧ IsOpen O ∧ LandsIn x.1 U ∧ f _ x.1 ∈ O) inferInstance

lemma continuousAt_complexPoint_iff : ContinuousAt γ t₀ ↔
  HasGermAt (ContinuousAt · t₀) (γ · |>.1) t₀ := by
  simp [ContinuousAt, tendsto_pi_nhds, nhds_induced, tendsto_nhds_Prop, HasGermAt, @nhds_def ℂ]
  grind [@isOpen_univ ℂ _]

/-- A smooth ℂ-scheme of dimension d has at each complex point x a chart φ to ℂ^d, with
holomorphic local inverse ψ; φ takes holomorphic families through x to analytic maps, with
zero derivative in directions where the family is constant to first order. -/
lemma exists_holomorphic_chart (hd : SmoothOfRelativeDimension d A.hom) x :
    ∃ᵉ (φ) (ψ : (Fin d → ℂ) → ComplexPoint A), φ x = 0 ∧
  (∀ᶠ y in 𝓝 x, ψ (φ y) = y ∧ ContinuousAt φ y) ∧ φ ∘ ψ =ᶠ[𝓝 0] id ∧ HolomorphicAt (ψ · |>.1) 0 ∧
  ∀ {P} [FinComplexSpace P] {γ} {w : P}, γ w = x → HolomorphicAt (γ · |>.1) w →
  AnalyticAt ℂ (φ ∘ γ) w ∧ ∀ v, IsFirstOrderConst (γ · |>.1) w v → fderiv ℂ (φ ∘ γ) w v = 0 := by
  obtain ⟨V, hV, U, hU, hx, e, ι, σ, _, _, P, (_ : _ - _ = d)⟩ := hd.1 (x.1 (closedPoint ℂ))
  obtain ⟨_, hx, h1⟩ := Inhabited.mk x,
    landsIn_iff_mem.2 hx, by simpa using landsIn_iff_mem.2 (e hx)
  algebraize [(A.hom.appLE V U e).hom]
  let E p := (MvPolynomial.eval (σ := ι) p).comp (MvPolynomial.map (evalSection _ h1).hom)
  have hE {p q} : AnalyticAt ℂ (E · q) p := AnalyticOnNhd.eval_mvPolynomial _ _ ⟨⟩
  let a (y : ComplexPoint A) i := PointFn.ofSection (P.val i) _ y.1
  have key y (h : LandsIn y.1 U) q : PointFn.ofSection (aeval P.val q) _ y.1 = E (a y) q
  apply q.induction_on <;> simp_all [E, a, RingHom.algebraMap_toAlgebra, ofSection_appLE,
    ofSection_eq h1]
  let F p j := E p (P.relation j)
  have h3 {y} (h : LandsIn y.1 U) : F (a y) = 0 := by ext; simp [F, ← key, h]
  let G := equivOfRightInverse (fderiv ℂ F (a x)) _ (of_surjective_of_finiteDimensional ((
    vecMul_surjective_iff_isUnit.2 ((LinearMap.isUnit_toMatrix'_iff.2 (.of_mul_eq_one _
    P.aevalDifferentialEquiv.comp_symm)).map (evalSection _ hx).hom.mapMatrix)).forall.2
    (⟨∑ j, · j • Pi.single (P.map j) 1, by rw [(hasFDerivAt_pi.2 fun _ ↦
    hasFDerivAt_mvPolynomial_eval ..).fderiv]; ext; simp
   [*, ← ofSection_eq hx, E, vecMul_eq_sum, pderiv_map]⟩))).choose_spec |> fun G ↦ G.trans
    (.prodCongr (.refl ..) (.ofFinrankEq (F := Fin d → ℂ) (fun _ ↦ by simp_all G.finrank_eq)))
  let c p := (G p - G (a x)).2
  have hc {p} := (by fun_prop : ContDiffAt ℂ ⊤ c p).analyticAt
  have hΦ : HasStrictFDerivAt (fun p ↦ (F p, c p)) (G : _ →L[ℂ] _) _ := .prodMk
    (AnalyticAt.pi fun _ ↦ hE).hasStrictFDerivAt (G.hasStrictFDerivAt.sub_const _).snd
  obtain ⟨H, I, S⟩ := hΦ.eventually_right_inverse.curry_nhds.self_of_nhds, landsIn_fromSpec hU,
    @P.aeval_val_surjective.forall
  choose! ψ hψ using fun p (h : F p = 0) ↦ ((fun h ↦
    ⟨homMk (Spec.map _ ≫ _) (point_eq_of_ofSection_eq hV (landsIn_preimage.1 ((I _).mono e)) h1
    (by simpa [↓← ofSection_appLE _ e, I, ofSection_eq h1, E] using! (h <|
    C ·))), I _, funext (by simpa [a, E] using! (h <| X ·))⟩) (RingHom.liftOfSurjective_comp_apply _
    P.algebraMap_surjective ⟨_, P.span_range_relation_eq_ker ▸ Ideal.span_le.2
    (Set.forall_mem_range.2 (congrFun h))⟩) : ∃ y, LandsIn y.1 U ∧ a y = p)
  have hf y s := continuousAt_complexPoint_iff.1 (continuousAt_id' y) (@isRegularOn_ofSection _ U s)
  have ha {y} h := continuousAt_pi' (f := a) fun i ↦ (hf y _ h).2
  exact sub_self (G _).2 ▸ ⟨c ∘ a, ψ ∘ hΦ.localInverse _ _ _ ∘ (0, ·), rfl, (hf _ 0 hx).1.mp (.mono
    (ha hx hΦ.eventually_left_inverse) fun y _ h ↦ ⟨by ext; apply point_eq_of_ofSection_eq hU <;>
    simp_all [h3 h], by fun_prop⟩), H.mono (by simp_all), .of_affine hU (H.mono (by simp_all)) (S.2
    fun _ ↦ (hE.comp (((AnalyticAt.pi fun _ ↦ hE).prod hc).contDiffAt.to_localInverse hΦ.hasFDerivAt
    (by simp)).analyticAt.curry_right).congr (H.mono (by simp_all [F]; tauto))),
    fun h H ↦ have t i := (H (isRegularOn_ofSection _) (by simp [*])).2
    ⟨hc.comp (AnalyticAt.pi t), fun v k ↦
      fderiv_comp _ hc.differentiableAt (AnalyticAt.pi t).differentiableAt ▸ by simp
      [isFirstOrderConst_iff.1, ← Pi.zero_def, fderiv_pi, differentiableAt, *]⟩⟩

/-- The complex points of a ℂ-scheme with a closed embedding in projective space form a compact
space. -/
lemma LineBundle.IsProjEmbedding.compactSpace_complexPoint (hN : N.IsProjEmbedding A.hom) :
  CompactSpace (ComplexPoint A) := by
  obtain ⟨j, _, hj, rfl⟩ := hN.exists_isClosedImmersion
  choose t o h1 using fun c ↦ ProjSpace.exists_isHomogCoords (𝟙 (Spec ⟨ℂ⟩)) (Function.ne_iff.1
    (@ne_zero_of_mem_unit_sphere (ι → ℂ) _ c)).choose_spec.isUnit
  choose s k using fun c : (Compacts.mk {c | LandsIn (t c) ⟨_, j.isClosedEmbedding.2.1⟩}ᶜ (
    isOpen_iff_mem_nhds.2 fun c k ↦ (HasGermAt.of_isHomogCoords (Q :=
    (ContinuousAt · c)) isProjEmbedding_projSpace (continuousAt_pi.1 (by fun_prop)) (.of_forall h1)
    o (isRegularOn_ofSection 0) k).1).isClosed_compl.isCompact)
    ↦ exists_lift_of_dense_preimage j _ (dense_indiscrete ⟨_, by_contra (landsIn_iff_mem.2.mt c.2)⟩)
  refine Function.Surjective.compactSpace (f := fun c ↦ homMk _ (hj ▸ by simp [reassoc_of% k, o]))
    (.of_at fun c ↦ continuousAt_complexPoint_iff.2 (.of_isHomogCoords hN (continuousAt_pi.1
    (by fun_prop)) (.of_forall (k · ▸ h1 _)))) fun x ↦ ?_
  have p := hN.1.2 (exists_landsIn _ x.1).choose_spec
  have := Function.ne_iff.2 p.ne_zero
  have := isProjEmbedding_projSpace.eq_of_isHomogCoords (by simp [*])
    (.smul (.pull_iff.1 p) (by simpa)) (h1 ⟨_, mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm ‹_›)⟩)
  use ⟨_, (· ⟨⟩ ⟨_, congr($this default)⟩)⟩, by ext; exact (cancel_mono j).1 (k _ ▸ this.symm)

/-- Uniformisation: an abelian variety A over ℂ, smooth of relative dimension d and embedded in
projective space by a linear system N, admits a uniformisation ℂ^d/L ≅ A(ℂ). -/
lemma LineBundle.IsProjEmbedding.nonempty_uniformisation [IsAbelianScheme A] (hN : N.IsProjEmbedding
  A.hom) (hd : SmoothOfRelativeDimension d A.hom) : Nonempty (Uniformisation A (Fin d → ℂ)) := by
  obtain ⟨⟨φ, ψ, h0, hs, H, hol, hc⟩, _, _ : IsTopologicalAddGroup (ComplexPoint A)⟩ :=
    exists_holomorphic_chart hd 0, hN.compactSpace_complexPoint, by
    refine' {..} <;> exact .of_at fun _ ↦ continuousAt_complexPoint_iff.2
      (.comp_hom (by apply_rules [HasGermAt.lift, continuousAt_complexPoint_iff.1] <;> fun_prop) _)
  have ⟨e, _, L, a, D, i, hu⟩ := (Filter.eventually_and.1 hs).elim (exists_lie_exponential h0) H
    (continuousAt_complexPoint_iff.2 (.imp_right (·.continuousAt) ∘ @hol · · ·))
    (hc (by simp [h0 ▸ hs.self_of_nhds]) (by exact .comp_hom (by apply_rules [HasGermAt.lift,
    (Eq.subst _ hol).comp, analyticAt_fst, analyticAt_snd]) _)).1
  have K z := (neg_add_cancel z ▸ (((Eq.subst (by aesop) hol).comp a).exists_isHomogCoords
    hN.1).elim fun _ ⟨a, c⟩ ↦ .of_isHomogCoords hN a (c.mp (L.mono (by lia))) :
    HolomorphicAt (e · |>.1) (-z + z)).comp (by fun_prop)
  use e, e.ker.toIntSubmodule, fun y ↦ (exists_point_over _ ((IsAbelianScheme.nsmul_surjective _
    i.1).1 _)).elim fun x h ↦ (OverMorphism.ext h : homMk x (y.w ▸ h ▸ by simp) ≫ _ = y) ▸ by
    simpa using e.range.nsmul_index_mem _, by tauto, fun z ↦ ⟨by simpa [← comp_left] using ((K
    z).comp_hom (translation (e z)).1), fun v h ↦ (((hasFDerivAt_comp_add_left _).2 (neg_add_cancel
    z ▸ D)).fderiv ▸ (hc (by simp) (K z)).2 v (by simpa [IsFirstOrderConst, ← comp_left, add_comm]
    using (h.comp_hom (translation (-e z)).1)) :)⟩, fun γ h ↦ hu γ (continuousAt_complexPoint_iff.2
    (.imp_right (·.continuousAt) ∘ @h · · ·)) (hc γ.map_zero h).1.differentiableAt
