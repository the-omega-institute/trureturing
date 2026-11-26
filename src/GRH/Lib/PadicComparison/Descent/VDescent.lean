import GRH.Lib.Cohomology.Etale.RelativeChains
import GRH.Lib.PadicComparison.Descent.TestCover
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Almost acyclicity of the structure sheaf for the v-topology (known result; see
Lib.PadicComparison.Descent.AlmostAcyclic).

This file: v-covers of perfect rings descend: follow a class by Zorn to a valuation ring. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

noncomputable section


open RingHom hiding mk
open LinearMap hiding lTensor rTensor mk ker rTensor_tensor
open TensorProduct Ideal Quotient Function ValuationRing Module NeZero Algebra ULift IsLocalRing
  CategoryTheory Limits Functor AlgebraTensorModule ConcreteCategory ObjectProperty H Comparison Ten
  Filter Localization MonoidalCategory Flat WittVector AlgHom
open ModuleCat hiding ofHom
variable {p} [ThePrime p] {S M M' M'' V A} [CommRing S] [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup M''] [CommRing V] [CommRing A] (N : Type) [AddCommGroup N] [Module OFlat N]
  [Algebra OFlat S] [Module S M] [Module S M'] [Module S M''] {a b d : PerfectAlg S} (φ :
  b ⟶ d) {C} [Category C] {K n} {Φ : C ⥤ ModuleCat S} {z :
  H K (moduleCoeff (Φ ⋙ tensorWith S M)) n} {f : M →ₗ[S] M'} {g : M' →ₗ[S] M''}

/-- 𝔪 ⊗ S is torsion-free, so flat, for reduced S -/
instance MaxIdealTensor.isTorsionFree_of_isReduced [IsReduced S] : IsTorsionFree OFlat (MaxIdealFlat
  ⊗[OFlat] S) := ⟨fun t k ↦ congr(⇑$(lTensor_smul_action ..)).subst ((injective_iff_eq_zero_of_exact
  (lTensor_exact _ (lsmul _ _ t).exact_subtype_ker_map)).2 (ext' fun m ⟨x, h⟩ ↦ by
    obtain ⟨s, k, rfl, n, d, e⟩ := m.exists_smul_eq k.ne_zero
    simp at h
    simp [smul_tmul, IsReduced.eq_zero (s • x) ⟨n + 1, by grind [smul_pow, Algebra.smul_def]⟩]))⟩

/-- Let V be a perfect valuation ring over O^♭ in which π is a non-zero non-unit. There are a
p-adic test c and an O^♭-algebra map φ: V → c^♭ with kernel inside πV such that V/ker φ →
c^♭ is faithfully flat. -/
lemma exists_faithfullyFlat_padicTest (V : CommAlg OFlat) [IsDomain V] [ValuationRing V]
  [PerfectRing V p] (h : IsSMulRegular V pFlat) (u : ¬IsUnit (algebraMap _ V pFlat)) : ∃ (c :
  PadicTest) (φ : V →ₐ[OFlat] c.TiltRing), φ.kerLift.FaithfullyFlat ∧ ∀ y, φ y = 0 → algebraMap _ V
  pFlat ∣ y := (exists_cell_over (ker_isPrime (TensorProduct.productMap (.liftOfSurjective (ofId ..)
  theta_surjective (ofId ..) fun _ a ↦ eq_zero_iff_mem.2 (u <| isUnit_of_dvd_unit (map_dvd _
  (map_dvd _ (theta_eq_zero_iff_xi_dvd.1 a))) ·)) ⟨.comp _ constantCoeff, by tauto⟩ : OC ⊗[Ainf]
  wittFunctor.obj V →ₐ[_] ResidueField V)) (isSMulRegular_tensor_witt (.of_ne_zero out) ⟨‹_›,
  h⟩) (by simp [p_eq_zero_of_algebra_oFlat])).elim fun W ⟨_, _, y, H⟩ ↦ by
  let c := cellPoint ((wittFunctor ⋙ algBaseChange _) V) fun _ : Unit ↦ y
  obtain ⟨⟨φ : _ →+* c.1.TiltRing, r⟩, hφ⟩ := surjective_of_epi (homTiltIso.1 _) c.2
  have e : c.1.ProdRing ≃+* W := .piUnique fun () ↦ W
  have := e.injective.isDomain
  have := e.symm.surjective.valuationRing e.symm.toRingHom
  algebraize [φ.kerLift]
  have := ker_isPrime φ
  obtain ⟨_, _⟩ := isTorsionFree_iff_algebraMap_injective.2 φ.kerLift_injective,
    (mkₐ_surjective V (ker φ)).valuationRing
  have : IsLocalHom φ.kerLift := ⟨Quot.ind fun v k ↦ .map (mkₐ V _) (by_contra fun hv ↦ H _
    (eq_zero_iff_mem.2 (mul_mem_left _ _ hv)) (.apply (congr($hφ.1.1 (_ ⊗ₜ _)).subst
    ((c.1.thetaIso_hom_one_tmul _).substr (.map _ ((map_teichmuller ..).substr (k.map _))))) ()))⟩
  exact ⟨_, ⟨_, r⟩, .of_flat_of_isLocalHom, fun y e ↦ (dvd_total ..).resolve_right
    (IsLeftRegular.ne_zero (R := c.1.TiltRing) c.1.isPerfectTorsionFree_tilt.2 <| zero_dvd_iff.1 <|
    e ▸ r _ ▸ map_dvd _ ·)⟩

local instance : IsScalarTower S S M := inferInstance

/-- For an S-linear map f: M → M' and a functor Φ to S-modules, the induced homomorphism H^n(K,
M ⊗ Φ) → H^n(K, M' ⊗ Φ). -/
def tensorPush := (pushHom K _ _ n).comp (.mk' (fun f ↦ coeffMap (Φ.whiskerLeft
  ((curriedTensor _).map (↟f)) : Φ ⋙ tensorWith S M ⟶ Φ ⋙ tensorWith S M')) (by aesop))

@[simp] lemma tensorPush_comp : tensorPush (g ∘ₗ f) z =
  tensorPush g (tensorPush f z) := by erw [← push_comp]; simp [tensorPush]; rfl

/-- Let M → M' → M'' → 0 be exact via f, g, with f ⊗ Φ(A) injective for all A. If H^m(K, M'' ⊗
Φ) = 0 for all m < n, then a class in H^n(K, M ⊗ Φ) killed by f is zero. -/
lemma eq_of_tensorPush_eq {y} (e : Exact f g) (s : Surjective g) (i : ∀ A, Injective
  (f.rTensor (Φ A))) (h : ∀ m < n, Subsingleton (H K (moduleCoeff (Φ ⋙ tensorWith S M'')) m)) :
  tensorPush f z = tensorPush f y → z = y := ((LongExactSeq.covariant
  ((shortExact_of_app (g := whiskerRight (Φ.whiskerLeft ((curriedTensor _).map (↟g)))
  (forget₂ ..)) i (fun _ ↦ rTensor_exact _ e s) fun _ ↦ rTensor_surjective _ s).2.map_of_exact
  (.obj (whiskeringRight ..) _)) _).f_injective_of_g_surjective (⟨0, h · · |>.1 _ ·⟩) ·)

open WidePushout in
/-- Let S be an O^♭-algebra and φ: b → d a map of perfect S-algebras. On perfect S-algebras, the
(m+1)-fold fibre power of h_d over h_b is representable. -/
lemma exists_repr_cech m : ∃ D z, AllBijective (@pointMap _ _ (cech (reprMap φ) m) D z ·) :=
  have := @PerfectAlg.closed_under_widePushoutShape p S _ _ p_eq_zero_of_algebra_oFlat; ⟨_,
    ⟨(⟨ι (fun _ ↦ φ) ·⟩), by simp [reprMap, reprFunctor, DFunLike.coe,
    arrow_ι fun _ ↦ φ]⟩, fun _ ↦ bijective_iff_has_inverse.2 ⟨fun e ↦ ⟨desc _ _ (congr($(e.2 ·
  0).1))⟩, by constructor <;> intro <;> solve_by_elim [Subtype.ext, funext,
    ULift.ext, ι_desc fun _ ↦ φ, (eq_desc_of_comp_eq ..).symm, (arrow_ι_assoc ..).symm]⟩⟩

/-- For a map φ: b → d of perfect S-algebras, the functor D ↦ ℤ[Hom(b,D)]/ℤ[maps that factor
through φ] from perfect S-algebras to abelian groups. -/
abbrev relFreeAbOfHom := _root_.relFreeAb (.range (reprMap φ))

/-- Flat base change. Let S be an O^♭-algebra, φ: b → d perfect S-algebras, Q = ℤ[h_b]/ℤ[im h_d],
V → A a flat map of S-algebras. If x in H^n(Q, V⊗Φ) dies in H^n(Q, A⊗Φ), then 1⊗x = 0 in A ⊗_V
H^n(Q, V⊗Φ). -/
lemma one_tmul_eq_zero_of_tensorPush {Φ : _ ⥤ ModuleCat S} [Algebra S V] [Algebra V A] [Algebra S A]
  [IsScalarTower S V A] [Flat V A] (x : H (relFreeAbOfHom φ) (moduleCoeff (Φ ⋙ tensorWith V V)) n)
  (e : tensorPush (algHom S V A).toLinearMap x = 0) :
  (1 : A) ⊗ₜ[V] x = 0 := let r D := (cancelBaseChange S V V A (Φ D)).symm.1
  (map_eq_zero_iff _ ((Ten.devissage.isClosedClass.2 _ (relFreeAb.shortExact _).2
    (Ten.devissage.bijective_range_of_cech _ fun _ ↦ Ten.devissage.isClosedClass.of_bijective _
    (exists_repr_cech ..).choose_spec.choose_spec (Ten.freeAb_reprBy _))).1 (Ten.freeAb_reprBy _)
    n).1).1 ((congrArg (x.push _ · n) (by
    ext D; congrm ⟨$(show mk _ _ _ 1 = r D ∘ₗ rTensor _ _ (Algebra.linearMap ..) by aesop)
    _⟩)).trans ((push_comp _ (coeffMap (⟨fun D ↦ ↟(r D), by delta tensorWith; aesop⟩ :
    Φ ⋙ tensorWith V A ⟶ _)) _).trans ((congrArg _ e).trans (map_zero _))))

instance (priority := low) [Algebra V S] : Algebra V a.1 := .compHom _ (algebraMap V S)

instance [Algebra V S] : IsScalarTower V S a.1 := .of_compHom ..

/-- The functor sending a perfect S-algebra D to D ⊗ N ⊗ 𝔪, tensor products over O^♭ with 𝔪 its
maximal ideal, regarded as an S-module. -/
def perfectAlmostCoeff : PerfectAlg S ⥤ ModuleCat S :=
  .mk _ fun f ↦ ↟(rTensor OFlat (N ⊗[OFlat] MaxIdealFlat) f.1.1.toLinearMap)

variable {N} {z : H (relFreeAbOfHom φ) (moduleCoeff (perfectAlmostCoeff N ⋙ tensorWith S a.1)) n}

/-- Let φ: b → d and a be perfect S-algebras, 0 ≠ z ∈ H^n(ℤ[h_b]/ℤ[im h_d], D ↦ a ⊗_S D ⊗ N ⊗
𝔪). Among maps ψ from a to perfect S-algebras keeping z non-zero, one has maximal relation
{(f, g) : ψ(f) ∣ ψ(g)}. -/
lemma exists_maximal_tensorPush_ne_zero (hz : z ≠ 0) : ∃ m, Maximal (fun s ↦
  ∃ (B : PerfectAlg S) (ψ : _ →ₐ[S] B.1), tensorPush ψ.toLinearMap z ≠ 0 ∧ s = (ψ · ∣ ψ ·)) m :=
  .imp (fun _ ↦ And.right) (zorn_le_nonempty₀ _ (fun c hc hc' _ h₀ ↦ by
  choose B ψ h0 e using fun t : c ↦ hc t.2
  let M : Submonoid (∀ t, (B t).1) := ⟨⟨{y | ∀ᶠ t in atTop, y t = 1},
    (·.mp <| ·.mono (by aesop))⟩, by simp⟩
  obtain ⟨P, _⟩ := Bijective.piMap (B · |>.2.1), atTop_neBot_iff.2 ⟨⟨_, h₀⟩,
    hc'.directedOn.isDirectedOrder⟩
  exact ⟨_, ⟨⟨.of _ (Localization M), have := isReduced_of_perfectRing ⟨P⟩;
      perfectRing_of_pow_surjective p_eq_zero_of_algebra_oFlat (·.ind
    (Prod.rec (P.2.forall.2 fun a ↦ Subtype.rec (P.2.forall.2 fun s ↦ (⟨.mk a ⟨s, ·.mono fun _ ↦
    (powMulEquiv ..).map_eq_one_iff.1⟩, mk_pow ..⟩)))))⟩, (algHom ..).comp (.pi ψ), fun q ↦
    ((IsLocalizedModule.eq_zero_iff M (TensorProduct.mk _ _ _ 1)).1 (one_tmul_eq_zero_of_tensorPush
    φ (tensorPush (pi ψ).toLinearMap z :) (tensorPush_comp.symm.trans q))).elim fun s hs ↦
    s.2.exists.elim fun t ht ↦ h0 t (by
    simpa [show (ψ t).toLinearMap = proj t ∘ₗ mulLeft S s.1 ∘ₗ (pi ψ).toLinearMap by ext; simp [ht]]
    using! (congrArg _ hs).trans (map_zero _)), rfl⟩, fun s hs f g a ↦ (monoidOf M).map_dvd_map.2
    ⟨fun t ↦ ite (ψ t f ∣ ψ t g) 1 0, (eventually_ge_atTop ⟨s, hs⟩).mono
      (ite_eq_left <| e · |>.le f g <|
    · f g a), by simp [pi_dvd_iff, apply_ite]⟩⟩) _ ⟨_, .id .., by
    simp [tensorPush]; exact z.comp_mk₀_id.trans_ne hz, rfl⟩)

/-- Let S be an O^♭-algebra, ψ: a → d and k: d → b maps of perfect S-algebras, k ≠ 0, each image
totally preordered by divisibility in the target. Then kψ factors, by S-linear maps, through
a perfect S-algebra that is a valuation domain. -/
lemma exists_perfect_valuationRing_factor {ψ : a.1 →ₐ[S] d.1} {k : _ →ₐ[S] b.1} (q :
  k.toLinearMap ≠ 0) (T : ∀ x y, ψ x ∣ ψ y ∨ ψ y ∣ ψ x) (T' : ∀ x y, k x ∣ k y ∨ k y ∣ k x) : ∃ (V :
  PerfectAlg S) (α : _ →ₗ[S] V.1),
  ∃ β, (k.comp ψ).toLinearMap = β ∘ₗ α ∧ ∃ _ : IsDomain V.1, ValuationRing V.1 := by
  have : IsPrime (ker k) := ⟨(q <| ext fun _ ↦ ·.ge ⟨⟩), @fun x y (_ : _ = 0) ↦ by
    apply (T' y x).imp <;> exact fun ⟨_, _⟩ ↦ (isReduced_of_perfectRing b.2).1 _ ⟨2, by grind⟩⟩
  have R := perfectRing_of_pow_surjective (S :=
    _ ⧸ ker k) p_eq_zero_of_algebra_oFlat (Quot.ind (d.2.1.2.forall.2 (⟨·, rfl⟩)))
  let f := (mkₐ S (ker k)).comp ψ
  let V := f.range.saturation (_ ⊓ nonZeroDivisors _) inf_le_left; exact
  ⟨⟨.of _ V, perfectRing_of_pow_surjective p_eq_zero_of_algebra_oFlat (Subtype.rec
    (R.1.2.forall.2 fun y ⟨v, g, r⟩ ↦ (a.2.1.2.exists.1
    (mul_mem (pow_mem g.1 (p - 1)) r)).elim (⟨⟨y, v, g, ·, R.1.1 <| by simpa [pow_sub_one_mul out,
    ← mul_assoc, mul_pow] using ·⟩, rfl⟩)))⟩, f.codRestrict V (f.range.le_saturation ⟨·, rfl⟩),
    (kerLiftAlg k).comp V.val |>.toLinearMap, rfl, _, (@iff_dvd_total V _ _).2 ⟨fun y z ↦ by
    obtain ⟨⟨_, ⟨⟨v, _⟩, _⟩, u, _⟩, _, ⟨⟨v', _⟩, _⟩, u', _⟩ := y.2, z.2
    apply (T (v' * u) (v * u')).imp <;> exact (map_dvd (mkₐ S _) · |>.elim fun w h ↦ by_contra fun
      n ↦ n ⟨⟨w, _, ⟨⟨_, rfl⟩, by by_contra; aesop⟩, _, h⟩, Subtype.ext (by
      simp; simp_all [f, mul_assoc, mul_left_comm])⟩)⟩⟩

/-- Let π kill N, φ: b → d and a be perfect S-algebras, I an ideal of a, with I ⊂ πa or πa
radical. A non-zero class in H^n(ℤ[h_b]/ℤ[im h_d], D ↦ a ⊗_S D ⊗ N ⊗ 𝔪) stays non-zero over
a/I. -/
lemma tensorPush_quotient_ne_zero (hN : ∀ x : N, pFlat • x = 0) (q : z ≠ 0) (I : Ideal a.1) (hI :
  (∀ y ∈ I, algebraMap _
  _ pFlat ∣ y) ∨ IsRadical (algebraMap _ a.1 pFlat)) : tensorPush (mkₐ S I).toLinearMap z ≠ 0 :=
  (map_ne_zero_iff _ (push_bijective_of_isIso (isoOfAppBijective _ fun D ↦ map_bijective.2
  ⟨ker_eq_bot.1 ((rTensor_mkQ (D.1 ⊗[OFlat] _) (I.restrictScalars S)).trans (range_eq_bot.2 (by
    ext y w n m; obtain ⟨s, c, rfl, k, e⟩ := m.exists_smul_eq pFlat_ne_zero
    obtain ⟨z, hz⟩ := hI.elim (· _ y.2 |>.mul_left _) (· k _ (by grw [e, map_pow]) |>.mul_right _)
    simpa [smul_tmul, ← tmul_smul, ↓smul_tmul', hN, ← Algebra.smul_def] using! congr($hz ⊗ₜ[S]
      (w ⊗ₜ[OFlat] (n ⊗ₜ[OFlat] c)))))), rTensor_surjective _ exists_rep⟩).isIso_hom n).1).2 q

/-- Let S be a perfect O^♭-algebra with p = 0, S → d → a maps of perfect S-algebras, a
faithfully flat over the S-algebra V, N an O^♭-module. Then H^n(ℤ[h_S]/ℤ[im h_d], D ↦ V ⊗_S
D ⊗ N ⊗ 𝔪) = 0. -/
lemma faithfullyFlat_descent [PerfectRing S p] [Algebra S V] (ρ : V →ₐ[S] a.1) (F :
  ρ.FaithfullyFlat) (i : ⟨.of _ S, ‹_›⟩ ⟶ d) (k : d ⟶ a) (x :
  H (relFreeAbOfHom i) (moduleCoeff (perfectAlmostCoeff N ⋙ tensorWith V V)) n) : x = 0 := by
  algebraize [ρ.1]; exact let E : PerfectAlg _ ⥤ PerfectAlg _ := lift _ (ι _ ⋙ tensorLeft a.1)
                            (perfectRing_tensor p_eq_zero_of_algebra_oFlat a)
    let η : 𝟭 _ ⟶ E := .mk fun _ ↦ ⟨ofHom TensorProduct.includeRight⟩
    let r (D : PerfectAlg S) := liftBaseChange V (assoc OFlat S S a.1 D.1 _).1
    have y {K F G x γ} β (z : whiskerRight η K = 0) (e : γ = whiskerRight η F ≫ β) : @push _ _ K F G
      γ n x = 0 := by erw [e, ← pull_id_eq_push, pull_whiskerRight, z]; simp [pull, H.map]
    (F.one_tmul_eq_zero_iff ..).1 (one_tmul_eq_zero_of_tensorPush i x (y (coeffMap (⟨fun D ↦ ↟(r D),
      fun _ _ _ ↦ hom_ext (by ext; rfl : r _ ∘ₗ _ = _ ∘ₗ r _)⟩ : E ⋙ perfectAlmostCoeff N ⋙
      tensorWith V V ⟶ perfectAlmostCoeff N ⋙ tensorWith V a.1)) (relFreeAb.hom_ext fun _ _ ↦
      relFreeAb.mk_eq_zero ⟨⟨k ≫ ⟨ofHom TensorProduct.includeLeft⟩⟩, congr(⟨⟨$(by ext)⟩⟩)⟩)
      (by ext D ⟨x⟩; exact congrArg _ (LinearMap.congr_fun (show rTensor _ _
      (Algebra.linearMap ..) = r D ∘ₗ lTensor _ _ (rTensor _ _ (mk _ _ _ 1)) by ext; simp [r]) x))))

/-- For a map φ: b → d of perfect S-algebras, the ring d regarded as a perfect b-algebra through
φ. -/
def perfectAlgAlong : PerfectAlg b.1 := ⟨@.of _ _ _ _ φ.1.1.toAlgebra, d.2⟩

/-- Almost v-descent: let π kill N. If y: b → b' of perfect O^♭-algebras makes Hom(b', S^♭) →
Hom(b, S^♭) onto for all p-adic tests S, then on perfect D, h_b and the image of h_{b'} have
the same cohomology for D ⊗ N ⊗ 𝔪.

Known result: Almost acyclicity of the structure sheaf for the v-topology. -/
lemma isCover_of_points (hN : ∀ x : N, pFlat • x = 0) {b b' : PerfectAlg _} (y : b ⟶ b')
    (hy : IsPointwiseSurjective (PadicTest.perfectTilt.whiskerLeft (reprMap y))) :
  IsCover (ι _ ⋙ moduleCoeff (almostCoeff N)) (reprMap y) :=
  let R : PerfectAlg b.1 ⥤ PerfectAlg OFlat := lift _ (ι _ ⋙ restrictAlg ..) (·.2)
  let un {d} (φ : b ⟶ d) : d ⟶ R (perfectAlgAlong φ) := ⟨ofHom ⟨.id _, (φ.1.1.2 · |>.symm)⟩⟩
  let i : perfectAlgAlong (𝟙 b) ⟶ perfectAlgAlong y := ⟨structureMap⟩
  suffices ∀ n (E : PerfectAlg b.1), Subsingleton (H (relFreeAbOfHom i) (moduleCoeff
    (perfectAlmostCoeff N ⋙ tensorWith _ E.1)) n) from ((show HasUnivPoints (F := ι _ ⋙ moduleCoeff
    (almostCoeff N)) ⟨R, tensorWith.mk b.1 (1 : b.1) (perfectAlmostCoeff N)⟩ (pointMap (Y
    := _ ⋙ reprBy b) ⟨un (𝟙 b)⟩) from fun A w ↦ ⟨_, ⟨⟨structureMap⟩⟩, un _, rfl, fun B x f k ↦
    ⟨⟨ofHom ⟨_, (congr($k.1.1.1 ·).symm.trans (x.1.1.1.2 _))⟩⟩, ⟨congr(⟨⟨$(by ext)⟩⟩), rfl⟩, fun _ ↦
    (·.2 ▸ rfl)⟩, map_bijective.2 ((TensorProduct.lid _ (perfectAlmostCoeff N
    _)).symm.bijective.comp (map_bijective bijective_id bijective_id))⟩).isCohomEquiv_incl_iff _
    (by ext B g; use (·.elim (⟨⟨un _ ≫ R.map ·.1⟩, · ▸ rfl⟩)), (·.elim fun _ k ↦
    ⟨⟨⟨ofHom ⟨_, (congr($k.1.1.1 ·).trans (g.1.1.1.2 _))⟩⟩⟩, congr(⟨⟨$(by ext)⟩⟩)⟩))).2
    ((relFreeAb.isCohomEquiv_iff_subsingleton _).2 (this · (perfectAlgAlong (𝟙 b))))
  Nat.strongRec fun n IH E ↦ subsingleton_of_forall_eq 0 fun z ↦ by_contra fun hz ↦ by
  have C {E z} hz := (exists_maximal_tensorPush_ne_zero (a := E) i (z := z) hz).imp fun m a ↦
    And.intro a.1 fun f g ↦ show m f g ∨ m g f by
    obtain ⟨⟨B, ψ, w, rfl⟩, a⟩ := a
    obtain ⟨_, _, B₀, i₁, i₂, j, h₁, h₂, sj, ej, ij⟩ :=
      exists_perfect_blowup_charts p_eq_zero_of_algebra_oFlat B (ψ f) (ψ g)
    let k := i₁.toLinearMap.prod i₂.toLinearMap
    have l {B i f g} h := (a ⟨B, .comp i ψ, ·, rfl⟩ (fun _ _ ↦ map_dvd i) f g h)
    exact .imp (l h₂) (l h₁) (not_and_or.1 fun q ↦ w (eq_of_tensorPush_eq ej sj (fun D ↦
      have := isReduced_of_perfectRing (perfectRing_tensor p_eq_zero_of_algebra_oFlat B₀ D)
      congr(⇑$(rTensor_tensor ..)).substr ((assoc ..).injective.comp
      (((lTensor_inj_iff_rTensor_inj _ (.restrictScalars _ (k.rTensor _))).1 (by
      simpa [lTensor_tensor] using (lTensor_injective_of_exact_of_flat _ (lTensor_surjective
        MaxIdealFlat (g := (j.rTensor D.1).restrictScalars OFlat) (rTensor_surjective _ sj)) _
        (lTensor_preserves_injective_linearMap _ (ij D)) (lTensor_exact _ (rTensor_exact (f := k)
        D.1 ej sj :)) N))).comp (assoc ..).symm.injective))) (IH · · _) (q.elim <| by
        simp +contextual [show k = _ from congr($coprod_inl_inr ∘ₗ k) ▸ coprod_comp_prod ..])))
  obtain ⟨_, ⟨B, ψ, q, rfl⟩, a⟩ := C hz
  obtain ⟨_, ⟨_, k, q, rfl⟩, a'⟩ := C q
  obtain ⟨V, α, β, e, _, _⟩ := exists_perfect_valuationRing_factor (q <| by simp [·]) a a'
  have w := tensorPush_quotient_ne_zero i hN (z :=
    tensorPush α z) (q <| by simpa [·] using congr(tensorPush $e z))
  have u G := w ⊤ (.inr G) (by simp [Subsingleton.eq_zero (toLinearMap _)])
  obtain ⟨c, φ, hφ, o⟩ := exists_faithfullyFlat_padicTest (.of _ V.1) ((isSMulRegular_algebraMap_iff
    _).1 (.of_ne_zero (u <| · ▸ zero_isRadical_iff.2 inferInstance))) (u ·.squarefree.isRadical)
  exact (hy c ⟨⟨ofHom (φ.comp (algHom ..))⟩⟩).elim fun ⟨g⟩ e ↦ w _ (.inl o) <|
    faithfullyFlat_descent (a := perfectAlgAlong (y ≫ g)) ⟨φ.kerLift,
    (congr($e.symm.1.1 ·))⟩ hφ i ⟨ofHom ⟨_, by tauto⟩⟩ _
