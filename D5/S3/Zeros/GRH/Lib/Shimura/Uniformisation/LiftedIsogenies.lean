/- GID: D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/LiftedIsogenies
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/Uniformisation/LiftedIsogenies
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.Uniformisation.LiftedIsogenies. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/Uniformisation/LiftedIsogenies.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Deformation.DrinfeldLifting
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.ModelAlongArc
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

Part of: Deformations of the PEL object have at most n-1 parameters (known result; see
Lib.Shimura.Deformation.TangentBound).

This file: Every full complex PEL abelian variety is uniformised by a frame and reflection.
Polarisation kernel has no p-part; maps respecting level and pairing are identity. Lifts of
multiplications are isogenies that keep the pairing; division of lifts. -/
seal Finset.univ Finset.sum Finset.prod

open Algebra ThetaObject AlgebraicGeometry CategoryTheory Complex Finset FourierTransform
  IsArtinianRing LinearMap Matrix NumberField OrzechProperty Category MorphismProperty
  CategoryTheory.Over NumberField.RingOfIntegers

variable {E k B : Type} [Field E] [CMBase E] {D : PEL E} [Field k] {Z σ} {X : ThetaFamily D Z σ}
  {x : ThetaObject X (Spec ⟨k⟩)} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

attribute [-simp] map_smul in
/-- Complex uniformisation: a complex object x with structure map Φ_{v₀} and full structure e is
modelled by a polarised period map to some ℂ^d, on some (g, ℓ) with ℓ a reflection, so that
the full structure of the model has the torsion points of e.

Known result: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class
number. -/
lemma exists_torusModel {τ} {X : ThetaFamily D Z τ} {x : ThetaObject X _} (e : x.FullStructure) (b :
  ∀ c, x.baseHom c = Φ v₀ c.val) : ∃ g ℓ d, ∃ᵉ (Y : PeriodMap D g ℓ (Fin d → ℂ)) (m :
  x.TorusModel Y), m.fullStructure.torsionPoint = e.torsionPoint ∧ IsReflection ℓ := by
  obtain ⟨⟨u⟩, ⟨d, hb⟩, q, _, _, _, J, R⟩ :=
    x.isProjEmbedding.nonempty_uniformisation x.smoothOfRelativeDimension, (exists_mixedEquiv.imp'
    (mixedEmbedding.latticeBasis E).map (by aesop) : ∃ d, ∀ i, d i = cmEmbedding ↑(basis E i)), by
    simpa [conj_eq_iff_im] using D.emb_star_beta_ne, X.signature 0 x
  choose F hF using fun i ↦ u.universal ((IsAddMonHom.addMonoidHom (basis E i • 𝟙 x.groupScheme)
    _).comp u.expMap) (atGeneric_eq _ ▸ (u.immersive 0).1.comp_hom _)
  let G := d.constr ℝ F
  have he (c : 𝓞 E) z : u.expMap (G (cmEmbedding c) z) = c • u.expMap z :=
    (basis E).sum_repr c ▸ by simp [G, ← hb, hF, ↓sum_smul, -zsmul_eq_mul, ↓map_sum]
  choose l hl using (u.surjective <| e.torsionPoint <| frameTorsionClass 1 <| Pi.single · 2⁻¹)
  let P := ∑ j, (ContinuousLinearMap.coeLM ℝ).flip (2 • l j) ∘ₗ G ∘ₗ .proj j
  have h y (h : 2 • y ∈ (frameTorsionClass 1).ker) : u.expMap (P (toRealVectors y)) =
    e.torsionPoint (frameTorsionClass 1 y) := by
    choose c hc using by simpa [ker_frameTorsionClass_one] using h
    simp [P, toRealVectors, hc, ← he, ← hl, two_mul, congrArg (frameTorsionClass 1) (by
      simp [funext_iff, Algebra.smul_def, *, field] : y = ∑ j, c j • Pi.single j 2⁻¹)]
  have T := by simpa [Submodule.eq_bot_iff] using (isIntegral_of_smul_mem_submodule (u.L.map
    ((P.toAddMonoidHom.comp toRealVectors).toRatLinearMap.range.mkQ.restrictScalars ℤ)) · .of_finite
    (2⁻¹ : ℚ) (Set.forall_mem_image.2 ((MulAction.surjective₀ (two_ne_zero' ℚ)).forall.2 fun z _ ↦
    (frameTorsionClass_surjective (g := 1).exists.1
    (x.exists_apply_eq_of_torsion e.injective (u.expMap z) ⟨2, by simp_all [two_smul]⟩)).elim
    fun y a ↦ ⟨z - P (toRealVectors y), by simp_all [h y (e.injective _), two_smul], by simp⟩))
    |> IsIntegrallyClosed.isIntegral_iff.1 |>.imp fun _ ↦ congrArg Rat.den)
  let Q := (LinearEquiv.ofBijective P (bijective_of_surjective_of_finrank_le P (range_eq_top.1
    (eq_top_mono (Submodule.span_le.2 fun _ ↦ by simp; grind -abstractProof) u.3.2.1))
    (by simp [abelianDim.eq_1 E, mul_assoc]))).toContinuousLinearEquiv
  have K c w : Q (c • w) = G c (Q w) := by simp [Q, P, G.map_mul_iff.2 (ext_basis d d fun i j ↦
    u.linear_ext (by simp [← map_mul, mul_smul, *]))]
  obtain ⟨X, o, _, ξ, s⟩ := (reindex_equiv Q).2.1.1
    (u.hasSignature_iff he J x.isGroupBaseChange (by simp) (ρ := x.baseHom).1 R)
  have H c : G c (Q X) = c v₀ • Q X := d.sum_repr c ▸ by simp [sum_smul, mul_smul, *]
  have A (w : RealVectors E D.Index) := by
    simpa [H, ← K, smul_comm (w _), ← map_sum, ← smul_sum, smul_smul (ξ _), ← dotProduct.eq_1,
      ← pi_eq_sum_univ', ← sum_smul] using congr(∑ k, G (w k) $(s (Q (Pi.single k 1))))
  choose f v using fun y ↦ x.exists_apply_eq_of_torsion e.injective (u.expMap (Q (toRealVectors y)))
    ((exists_nsmul_adelicTorsion_eq_zero (frameTorsionClass 1 y)).imp
    fun m k ↦ by simpa [k, -nsmul_eq_mul] using! h (m • y))
  obtain ⟨⟨m, Y⟩, ⟨ε, P⟩, B, χ, θ, h, hp⟩ := exists_matrix_torsionClass_eq (by
    use! f <;> simp [← e.injective.eq_iff, *]), e.weil_pairing 1,
    u.appell_humbert x.isProjEmbedding x.hasClassLaws.1
  simp [← e.injective.eq_iff, v] at Y
  let R := BilinForm.congr Q.1.symm B.riemannForm
  let M := finAdeleIncl ℚ E ε • mᴴ * m
  have W y z : 𝐞 (R (toRealVectors y) (toRealVectors z)) =
    ψf _ (xiForm D.ξ (M *ᵥ frameCoords 1 y) (frameCoords 1 z)) := Circle.ext (by
    have ⟨N, hN, H⟩ := exists_forall_mul_mem_Ô (m *ᵥ frameCoords 1 y ⊕ᵥ m *ᵥ frameCoords 1 z)
    obtain ⟨_, ⟨⟩⟩ := DivisibleBy.surjective_smul _ ℤ (Nat.cast_ne_zero.2 hN) (y, z)
    simp [← nsmul_eq_mul, smul_smul, ← @torsionClass_eq_zero _ D.Index, ← Pi.smul_def] at H
    obtain ⟨⟨⟨_, a⟩, _, b⟩, _, rfl, c⟩ :=
      H.imp e.exists_isTranslationLift e.exists_isTranslationLift, H.elim (P _ _ _)
    simpa [star_trivial, xiForm, M, star_mulVec_dotProduct, R, ← nsmul_eq_mul, mul_smul,
      mul_left_comm]
      using ((lift_commutator_iff_weil_pairing u h (Y _ ▸ a) (Y _ ▸ b)).1 (c _ _ a b)).symm)
  choose r a using fun z y ↦ (⟨_, mod_cast (eq_add_of_sub_eq (fourierChar_eq_one.1 ((𝐞
  ).toAddMonoidHom.sub_mem_ker_iff.2 (W ..))).choose_spec).symm⟩ : ∃ q : ℚ, q =
    R (toRealVectors y) (toRealVectors z))
  choose β k using fun i j ↦ by simpa [DFunLike.ext_iff, BilinForm.toDual] using (BilinForm.toDual _
    (traceForm_nondegenerate ℚ E)).surjective (AddMonoidHom.mk' (r (Pi.single i 1) <| Pi.single j <|
    D.ξ⁻¹ * ·) (by simp [a, mul_add, Pi.single_add, ← @Rat.cast_inj ℝ])).toRatLinearMap
  have hβ : (of β).map (↑) = M := Matrix.ext fun i j ↦
    eq_of_ψf (denseRange_algebraMap_finAdele.eq fun t ↦ by
    simp [ψf_eq, ← map_mul, mul_comm t, xiForm, frameCoords, entrywise, apply_ite, mul_comm (M ..),
      ← mul_assoc, ne_zero_of_map (ne_of_apply_ne im (D.xi_im_pos_and_re_eq_zero v₀).1.ne'), *])
  have rf : R = polarisationForm D (of β) := LinearMap.ext (isClosed_property
    denseRange_toRealVectors (R.eqLocus _).closed_of_finiteDimensional fun y ↦
    sub_eq_zero.1 (eq_zero_of_exp_eq_one _ (denseRange_toRealVectors.eq (by
    simp [W, ← hβ, 𝐞.map_sub_eq_div, ← ψf_eq, xiForm, frameCoords, entrywise]))))
  obtain ⟨m, rfl⟩ : IsUnit m := isUnit_of_mul_isUnit_right (hβ.subst (.map (RingHom.mapMatrix _)
    (mulVec_injective_iff_isUnit.1 fun _ _ _ ↦
    toRealVectors_injective (R.ker_eq_bot.1 (hp.nondegenerate.congr _
    ).ker_eq_bot (LinearMap.ext (denseRange_toRealVectors.eq (by simp [*])))))))
  have v y : e.torsionPoint (frameTorsionClass m⁻¹ y) = _ :=
    .trans (by simp [frameCoords, frameTorsionClass]) (Y y)
  refine ⟨m⁻¹, _, _, ⟨_, Q, B, ⟨ε, gram_inv_of_gram_eq (by simp [*, M])⟩, fun w ↦
    Q.eq_symm_apply.1 (Matrix.ext fun j v ↦ _root_.cast ?_ congr(Q.symm $(A w) j v)), h.2.1,
    congr_fun₂ rf, hp⟩, ⟨b, u, χ, θ, h, by simp [*], by simp [e.3, PeriodMap.torsionLift, ← v],
    Submodule.ext ?_⟩, LinearMap.ext (by simp [TorusModel.fullStructure,
    ← v]), (X · v₀), (I / (Φ v₀ D.β.val).im) • (ξ <| Q <| Pi.single · 1), ?_, rfl⟩
  · by_cases v = v₀ <;> simp [D.emb_beta_eq_of_ne, *, -K, vecMulVec_mulVec, ← by simpa [← K] using
      (H <| Pi.single v₀ ·), Complex.ext_iff, smul_re_im (Φ v₀ _)] <;> clear * - q <;> grind -abstractProof
  · simp [mem_classLattice, ← e.injective.eq_iff, v, Q]; clear * - T; grind -abstractProof
  simp [← by simpa [smul_left_inj, *, ← sub_smul] using A X, Complex.ext_iff, ← two_mul, field]

/-- Rigidity: let x be rigid over a field of characteristic l, w a pull-back of x, y a point of
w over a noetherian local ring. If ⟨y, ·⟩ = 0 over all bases and l^m kills y on some
non-zero ring, then y = 0. -/
lemma ThetaObject.IsRigid.eq_zero_of_pairing_eq_zero (hx : x.IsRigid) {l} [hl : Fact l.Prime] [CharP
  k l] {S b} {w : ThetaObject X S} (hb : w.IsPullbackAlong b x) {t : Spec ⟨B⟩ ⟶ _} (y : .mk t ⟶
  w.groupScheme) m {C} (a : Spec C ⟶ _) [Nontrivial C] (hm : l ^ m • (homMk a : .mk (a ≫ t) ⟶ _) ≫
  y = 0) (h : ∀ ⦃T⦄ a z, w.lineBundle.picClass.pairing (T := T) (a ≫ y) z = 0) : y = 0 := by
  choose u hp using w.exists_isPullbackAlong t
  obtain ⟨z, rfl⟩ := hp.isGroupBaseChange.pointEquiv (T := .mk (𝟙 _)).surjective y
  have := u.obj_isThetaStructure.card_nsmul_eq_zero_of_lift (hx (hp ▸ hb ▸ assoc t b x))
    u.isProjEmbedding (exists_isTranslationLift_iff.2
    (by simpa [hp.lineBundle_eq_pull, Pic.pairing,
    hp.isGroupBaseChange.atPoint_picClass_pull] using! h (homMk _ rfl) hp.schemeMap)).choose_spec
  exact section_eq_zero_of_torsion u.smoothOfRelativeDimension u.obj_isThetaStructure.4 this
    ((nsmul_eq_zero_iff_of_coprime
    (hl.1.coprime_pow_of_not_dvd ((CharP.isUnit_natCast_iff hl.1).1 x.obj_isThetaStructure.4))).1
    ⟨by simp_all [← comp_nsmul], hp.isGroupBaseChange.pointEquiv.injective (by simpa)⟩) ▸ map_zero _

/-- Rigidity: over a local noetherian ring, let x₁ be a pull-back of a rigid object and j: x₁ →
x₂ an O_E-linear homomorphism respecting structure maps from O_E, pairing and level points.
Then x₁ and x₂ have the same point of the base, and j commutes with the projections to the
family. -/
lemma ThetaObject.IsRigid.eq_of_hom (hx : x.IsRigid) {x₁ x₂ : ThetaObject X (Spec ⟨B⟩)} {b} (hb :
  x₁.IsPullbackAlong b x) (hρ : x₁.baseHom = x₂.baseHom) j [hl : IsLinear j] (hN : ∀ ⦃T⦄ y z,
  x₁.lineBundle.picClass.pairing (T := T) y z = x₂.lineBundle.picClass.pairing (y ≫ j)
  (z ≫ j)) (hη : ∀ l, x₁.levelPoints l ≫ j = x₂.levelPoints l) : x₁ = x₂ ∧
  j.left ≫ x₂.toFamily.left = x₁.toFamily.left := by
  have e := x₁.obj_isThetaStructure.pull_eq_of_picClass_eq (hx hb) x₂.obj_isThetaStructure
    D.odd_card j (by tauto) ((x₁.hasClassLaws.2 0
    (𝟙 _)).2.trans (by simpa [*] using! (x₂.hasClassLaws.2 0 j).2.symm))
  have := X.eq_of_list_eq _ _ (by simpa [baseHom, specMap] using congr(specMap $hρ)) (by simp_all
    [← levelPoints_comp_toFamily, ← hη, lineBundle])
  use this, X.embeds.ext e (by aesop)

open DualNumber

variable [IsAlgClosed k] {Z : Scheme} {σ : Z ⟶ Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {Y : ThetaFamily D Z σ} {x₀ : ThetaObject Y _} {x :
  ThetaObject Y (Spec (CommRingCat.of (TrivSqZeroExt k k)))} {x'}
  {hq : IsPullbackAlong (sqZeroReduction k k) x₀ x} {hq' : IsPullbackAlong _ x₀ x'} (f)
  [IsAdditive f] {a : 𝓞 E} (hf : hq.schemeMap ≫ f = a • hq'.schemeMap) [Fact (ringChar k).Prime]

instance : Module.Finite k k[ε] := .prod

include hf

/-- Let x, x' deform x₀ over k[ε], char k prime, and let the homomorphism f: A_x → A_x' reduce
to a ∈ O_E. Then f is O_E-linear; fy = 0 implies ay ≡ 0 mod ε; and ⟨fy, fz⟩' = ⟨ay, az⟩ if
A_x is a base change of A_x₀. -/
lemma isLinear_and_pairing_eq_of_reduction : IsLinear f ∧ (∀ {T} y, y ≫ f = 0 → AgreeModEps hq hq T
  (a • y) 0) ∧ ∀ {s}, x.IsPullbackAlong s x₀ → ∀ ⦃T⦄ (y z : T ⟶ _), x'.lineBundle.picClass.pairing
  (y ≫ f) (z ≫ f) = x.lineBundle.picClass.pairing (y ≫ (a • 𝟙 _)) (z ≫ (a • 𝟙 _)) := by
  have F {T} : ∀ v, v ≫ f = hq'.isGroupBaseChange.pointEquiv (T :=
    T) (hq.isGroupBaseChange.pointEquiv.symm (a • v)) ∧ x'.lineBundle.picClass.atPoint (v ≫ f) =
    x.lineBundle.picClass.atPoint (a • v) := (reindex_equiv hq.isGroupBaseChange.pointEquiv).1.2
    (by simp; simp [IsGroupBaseChange.pointEquiv_apply, ← (IsPullbackAlong.isGroupBaseChange
    _).2.2, Pic.atPoint, ← IsPullbackAlong.lineBundle_eq_pull, *])
  cases by exact_mod_cast x.finite_flat_surjective_smul (a := ringChar k) NeZero.out
  use ⟨fun c ↦ (epi_of_epi_left (ringChar k • 𝟙 _)).1 _ _ (sub_eq_zero.1 (by simpa
    [← smul_sub] using (AgreeModEps.ringChar_smul_and_smul_eq_zero hq' (by simp [AgreeModEps,
    ← assoc, F, smul_comm c])).1))⟩, fun _ h _ _ t ↦ by simpa [← assoc, F, -map_smul] using t ≫= h,
    (pairing_eq_of_fpqc_cover ·.isGroupBaseChange.1 (ringChar k • 𝟙 _) f f _ _ fun T y z ↦ ?_)
  let X := CategoryTheory.Over.mk (T.hom ≫ (specOver k _).hom)
  have U {x : ThetaObject Y _} y : _ • x.lineBundle.picClass.atPoint y =
    x.lineBundle.picClass.atPoint ((homMk _ (by
    rw [absFrobenius_comm 1 X (specOver ..), ← Category.id_comp (absFrobenius ..),
      comp_absFrobenius]
    simpa [X] using _ ≫= Spec.homEquiv.injective (by aesop (add simp CharP.cast_eq_zero))) :
    CategoryTheory.Over.map (sqZeroReduction k k) (CategoryTheory.Over.mk
    (X.hom ≫ specMap (frobPow (natCast_eq_zero_of_over_charP (𝟙 _)) 1))) ⟶ T) ≫ y) :=
    picClass_pull_absFrobenius 1 X (x.isProjEmbedding.1.pull _)
  simp_all [(ThetaObject.hasClassLaws _).1.pairing_nsmul_left]
  simp [Pic.pairing, smul_sub, U, ← AddMonObj.add_comp, ← assoc, (F _).2]

/-- Division of lifts. Let f: A_x → A_x' and F: A_x → A_x₁ be homomorphisms of deformations over
k[ε] reducing to a ≠ 0 and ca. If F kills all points over finite local k[ε]-algebras killed
by f and a², some homomorphism A_x' → A_x₁ reduces to c. -/
lemma exists_lift_of_kills_ker (ha : a ≠ 0) {x₁} (hq₁ : IsPullbackAlong _ x₀ x₁) F [IsAdditive F] c
  (hF : hq.schemeMap ≫ F = (c * a) • hq₁.schemeMap) (h : ∀ S [CommRing S] [IsLocalRing S]
  [Algebra k[ε] S] [Module.Finite k[ε] S] [IsNoetherianRing S] (y : specOver _ S ⟶ _), y ≫ f = 0 →
  a • a • y = 0 → y ≫ F = 0) : ∃ μ, IsAdditive μ ∧ hq'.schemeMap ≫ μ = c • hq₁.schemeMap := by
  obtain ⟨e, ⟨_, L, -⟩⟩ := by simpa [← hf] using congr($(hq'.isGroupBaseChange.2.2 a (𝟙 _)).1),
    isLinear_and_pairing_eq_of_reduction f hf, of_finite k k[ε], x₀.finite_flat_surjective_smul ha,
    of_isPullback hq'.isGroupBaseChange.1.flip isSqZeroExt_fstHom.surjective, of_isPullback
    hq'.isGroupBaseChange.1.flip (IsClosedImmersion.spec_of_surjective _ isSqZeroExt_fstHom.1.1)
  obtain ⟨G⟩ := finite_flat_of_quasiFinite f (.of_finite_preimage_singleton _ fun z ↦
    .of_preimage (e ▸ (_ ≫ hq'.schemeMap.1).finite_preimage_singleton z :)
    (of_isPullback hq.isGroupBaseChange.1.flip isSqZeroExt_fstHom.surjective).1)
    (@.of_comp _ _ _ hq.schemeMap.1 _ (e ▸ inferInstance)), epi_of_epi_left (a • 𝟙 x₀.groupScheme)
  refine (exists_factor_through_isogeny f F fun _ ↦ fun y g ↦ h _ y g ?_).imp fun _ ↦ .imp_right
    (by simp [← hF, ← cancel_epi ((CategoryTheory.Over.map (sqZeroReduction k k)).map (a • 𝟙
    x₀.groupScheme)), ← assoc, (IsPullbackAlong.isGroupBaseChange _).2.2, smul_smul, ← ·, hf])
  choose S ι _ _ _ h₀ H using exists_finite_kernel_ring G.2
  obtain ⟨⟨z, rfl⟩, ⟨⟨γ⟩, ⟨o⟩⟩, _, ψ, b, w, -, ⟨e⟩⟩ :=
    H y g, by simpa [specOver.map_bijective.2.exists, h₀] using
    (⟨H (a • ι), @H (specOver _ k[ε]) 0⟩ : _ ∧ _), exists_isSqZeroExt_mod_eps (specOver k[ε] S).hom
  let u : .mk (b ≫ sqZeroReduction k k) ⟶ specOver _ S := homMk _ w
  choose d e using
    fun s ↦ by simpa [specOver.map, u, ← RingHom.sub_mem_ker_iff, e, dvd_def, -map_sub,
    sub_eq_iff_eq_add] using congr(Spec.preimage ($((mono_of_mono_left ι).1 (u ≫ specOver.map γ)
    (u ≫ specOver.map (ofId ..) ≫ specOver.map o) (by simpa [-map_smul, *] using L _ h₀ ..))).1 s)
  simpa [← specOver.map_comp_assoc, *] using congr(z ≫ specOver.map $(show γ.comp γ =
    ((ofId ..).comp o).comp γ by ext s; simp [e s, e (d _), ← Algebra.smul_def, smul_smul]) ≫ ι)
