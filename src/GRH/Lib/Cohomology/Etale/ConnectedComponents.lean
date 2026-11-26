import GRH.Lib.General.Algebra.TensorCohomology
import GRH.Lib.Cohomology.Etale.ContinuityAtlas
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

Part of: Tilting and untilting for products of perfectoid valuation rings over O_C (known result;
see Lib.Cohomology.ProperBaseChange.ValuativeDensity).

This file: Locally constant functions on tests are additive for idempotent partitions. Tilts of
products of valuation rings; kernel of theta is (xi); untilting isomorphism. Cohomological
equivalence can be checked on connected components, by Zorn's lemma. -/

open PrimeSpectrum ULift CommRingCat Ideal Quotient CategoryTheory Functor ConcreteCategory

lemma IsTest.isRadical_span_idempotent {A} [CommRing A] (h : IsTest A) {e : A} (he :
  IsIdempotentElem e) : (span {e}).IsRadical := he.ker_toSpanSingleton_one_sub_eq_span ▸ fun x ⟨n,
  _⟩ ↦ h.3.1 _ ⟨n + 1, by simp_all [mul_pow]; grind⟩

/-- For any abelian group Λ, the coefficient functor on test rings sending A to the locally
constant functions Spec A → Λ is additive for partitions along idempotents, in the sense of
`HasPartitions`. -/
lemma hasPartitions_locConstCoeff {Λ} : HasPartitions testIncl (locConstCoeff Λ) :=
  ⟨fun A e h _ ↦ ⟨⟨_, A.2.quotient (A.2.isRadical_span_idempotent h)⟩,
  ⟨CommRingCat.ofHom _⟩, mk_singleton_self _, fun _ f _ ↦ ⟨⟨CommRingCat.ofHom
  (lift _ f.1.hom (by simp_all [mem_span_singleton']))⟩, by aesop⟩, exists_rep, mk_ker.le⟩, fun _ _
  h ↦ Eq.subst (by ext x <;> use congr(x.1 $(by ext; erw [mem_prod]; simp))) (Equiv.ulift.trans
  ((LocallyConstant.congrLeft ((homeomorphOfRingEquiv (.ofBijective (RingHom.prod ..) h)).trans
  primeSpectrumProdHomeo)).trans (.mk (fun x ↦ (up (x.comap (.mk .inl)), up (x.comap (.mk .inr))))
  (fun (⟨x⟩, ⟨y⟩) ↦ ⟨Sum.elim x y, (⟨x.2 ·, y.2 _⟩)⟩) (by cat_disch)))).bijective⟩

/-- For φ: C' → C, α: N' → N∘φ, Ψ: C → D, G from D to S-modules and G∘Ψ ≅ M: restriction
Ext^n(N, G∘Ψ) → Ext^n(N', G∘Ψ∘φ) is bijective for all n iff Ext^n(N, M) → Ext^n(N', M∘φ) is. -/
lemma Comparison.coeffCompBij_id_iff_restrict {C C' D S} [Category C] [Category C'] [Category D]
  [CommRing S] {φ N} {N' : AbFunctor C'} {α : N' ⟶ φ ⋙ N} {Ψ : C ⥤ D} {G M} (θ : Ψ ⋙ G ≅ M) :
  CoeffCompBij (S := S) (𝟙 (φ ⋙ Ψ)) α G ↔ (restrict φ (moduleCoeff M)).IsBijective α :=
  let γ := whiskerRight θ.1
    (moduleCoeff (𝟭 _)); by apply isBijective_iff_of_coeff_iso γ (φ.whiskerLeft γ); aesop

variable {C k S} [Category C] [CommRing k] [CommRing S] [Algebra k S]

/-- Base change from commutative k-algebras to commutative S-algebras is left adjoint to
restriction of scalars. -/
def algBaseChangeAdj : algBaseChange S ⊣ restrictAlg k S := .mkOfHomEquiv (.mk (homEquiv.trans <|
  .symm <| homEquiv.trans <| @AlgHom.liftEquiv k S · · _ _ _ _ _ _ _ (_) (.of_compHom ..)) fun _ _ ↦
  ConcreteCategory.ext tmul_ext)

/-- For functors F to k-algebras and G to S-algebras, the adjunction bijection from natural
S-algebra maps S ⊗_k F → G to natural k-algebra maps F → G. -/
abbrev baseChangeTranspose := ((@algBaseChangeAdj k S _ _ _).whiskerRight C).homEquiv

lemma pointMap_algBaseChange_unit_bijective B :
  AllBijective (pointMap (Y := restrictAlg k S ⋙ reprBy B) ⟨algBaseChangeAdj.unit B⟩ ·) := fun _ ↦
  ULift.map_bijective.2 (algBaseChangeAdj.homEquiv ..).bijective

open Function Perfection RingHom WittVector Subfunctor Abelian.Ext LongExactSeq
variable {p} [ThePrime p] (c : PadicTest)

/-- For ring maps y_i from an O_C-algebra B to a non-empty family of cells W_i, the p-adic test
∏ W_i, over O_C through B, with the point (y_i): B → ∏ W_i. -/
noncomputable def cellPoint B {I} [n : Nonempty I] {W : I → _} [∀ i, CommRing (W i)]
    [∀ i, IsCell p (W i)] (y : ∀ i, B.1 →+* W i) : Sigma (PadicTest.algFunctor ⋙ reprBy B) :=
  ⟨⟨I, W, .comp (.pi y) _⟩, ⟨ConcreteCategory.ofHom ⟨.pi y, by tauto⟩⟩⟩

/-- The product ring of a p-adic test c is a test ring: reduced, absolutely integrally closed,
and any a, b admit an idempotent e with a ∣ eb and b ∣ (1 − e)a. -/
lemma PadicTest.isTest : IsTest c.ProdRing := .pi

instance PadicTest.instIsAICR : IsAIC c.ProdRing := c.isTest.1

lemma PadicTest.isLeftRegular_p :
  IsLeftRegular (p : c.ProdRing) := by
    refine Pi.isLeftRegular_iff.2 fun i ↦ ?_
    simp [isRegular_iff_ne_zero, IsCell.p_ne_zero]

/-- For a p-adic test with cells W_i, the ring isomorphism from the tilt of ∏ W_i to the product
of the tilts W_i^♭ induced by the projections. -/
noncomputable def PadicTest.tiltPiEquiv := RingEquiv.ofBijective
  (RingHom.pi (tiltMap (p := p) <| Pi.evalRingHom c.Cell ·)) (((quotientMulEquiv ..).bijective_comp
  _).1 ((((Equiv.piComm fun _ ↦ c.Cell).subtypeEquiv (by simp [funext_iff]; tauto)).trans
  .subtypePiEquivPi).trans (.piCongrRight fun _ ↦ (quotientMulEquiv ..).1)).bijective)

lemma PadicTest.dvd_of_untilt_dvd {x y : c.TiltRing} (h : x.untilt ∣ y.untilt) : x ∣ y :=
  (map_dvd_iff c.tiltPiEquiv).1 <|
  pi_dvd_iff.2 (untilt_dvd_iff.1 <| by convert pi_dvd_iff.1 h · <;> apply untilt_tiltMap)

/-- The tilt of a p-adic test c is a perfect O^♭-algebra without π-torsion, in the sense of
`IsPerfectTorsionFree`. -/
lemma PadicTest.isPerfectTorsionFree_tilt : IsPerfectTorsionFree (tilt c) := (⟨inferInstance,
  .of_right_eq_zero_of_smul fun _ _ ↦ zero_dvd_iff.1 (c.dvd_of_untilt_dvd (c.isLeftRegular_p
  (Dvd.elim_left (map_dvd c.structureMap untilt_constantCoeff_xi_dvd_p) (by simp_all [pFlat, ←
  untilt_tiltMap, mul_assoc, ← map_mul, Algebra.smul_def, algebraMap]))).dvd)⟩ :
  IsPerfectTorsionFree (.of _ c.TiltRing))

/-- For a p-adic test with ring S, the kernel of Fontaine's map θ: W(S^♭) → S is the principal
ideal generated by the image of ξ ∈ A_inf. -/
@[simp] lemma PadicTest.ker_theta : ker (fontaineTheta c.ProdRing p) =
  span {xi.map (algebraMap ..)} :=
  have h := mem_ker.2 ((fontaineTheta_map_tiltMap ..).trans (theta_xi ▸ c.structureMap.map_zero))
  le_antisymm (mem_span_singleton.2 <| Witt.dvd_of_mem_of_constantCoeff_dvd h
    (by simp [c.isLeftRegular_p.mul_left_eq_zero_iff]) (fun _ _ ↦
    c.dvd_of_untilt_dvd ((untilt_tiltMap ..).dvd.trans ((map_dvd _ untilt_constantCoeff_xi_dvd_p
    ).trans (by simp_all [← Quotient.eq_zero_iff_dvd, ← mk_fontaineTheta])))) · ·) (by simpa)

/-- For an idempotent e ≠ 1 in the ring of a p-adic test c, there is a map of tests f: c → d,
universal among maps killing e, that is the quotient by the ideal (e). -/
lemma PadicTest.exists_isIdemQuotient (e : c.ProdRing) (he : IsIdempotentElem e) (h : e ≠ 1) :
  ∃ d f, IsIdemQuotient (B := d) ringFunctor e f := let f :=
    (cellPoint (.of ..) (n := nonempty_subtype.2 (ne_iff.1 h)) (Pi.evalRingHom c.Cell ·)).2.1.1
  let s := Subtype.surjective_restrict _
  let k x h := mem_span_singleton'.2 ⟨x, by
    simpa [funext_iff, mul_right_eq_self₀, or_iff_not_imp_left, cellPoint] using! congrFun h⟩
  ⟨_, f, funext (eq_zero_of_mul_eq_self_left ·.2 congr($he _)), fun d g h ↦
    f.liftOfSurjective_comp s g (.trans k (by simpa)) ▸ ⟨_, rfl, (·.cancel_right s |>.1)⟩, s, k⟩

/-- The natural isomorphism O_C ⊗_{A_inf} W(S^♭) ≅ S of O_C-algebras on p-adic tests S, induced
by Fontaine's map θ.

Known result: Tilting and untilting for products of perfectoid valuation rings over O_C. -/
noncomputable def PadicTest.thetaIso : tilt ⋙ wittFunctor ⋙ algBaseChange _ ≅ algFunctor :=
  isoOfAppBijective ((baseChangeTranspose (_ ⋙ wittFunctor) _).2 ⟨(ConcreteCategory.ofHom ⟨_,
  fontaineTheta_map_tiltMap ·.structureMap⟩), fun _ _ f ↦ ext_apply (fontaineTheta_map_tiltMap
  f.1)⟩) fun c ↦ ⟨.of_ker _ ((TensorProduct.mk_surjective _ _ _ theta_surjective).forall.2 fun _ ↦
  (c.ker_theta.trans_le ((ker Algebra.TensorProduct.includeRight).span_singleton_le_iff_mem.2
  ((AlgHom.commutes ..).trans (by simp [algebraMap]))) <| (one_smul OC _).symm.trans ·)), by
    exact fontaineTheta_surjective_of_isAIC (R := c.ProdRing).forall.2 (⟨1 ⊗ₜ ·, one_smul OC _⟩)⟩

lemma PadicTest.thetaIso_hom_one_tmul x : thetaIso.1 c (1 ⊗ₜ x) = x.fontaineTheta _ p :=
  one_smul OC _

variable {Λ R} [CommRing.{0} R] {X Y : PointFunctor} {U V W : Subfunctor Y} (l : U ≤ W) (l' : V ≤ W)

lemma IsRelAffine.preimage (h : IsRelAffine U.ι) (f : X ⟶ Y) : IsRelAffine (U.preimage f).ι :=
  h.baseChange (v :=
  fromPreimage ..) (isPullback_iff.2 (by aesop (add simp [ExistsUnique, toFunctor])))

/-- Mayer–Vietoris for Λ-cohomology, with U, V ⊂ W and U ∪ V dense in W. Restriction Hⁿ(W) →
Hⁿ(U) × Hⁿ(V) is injective if Hᵐ(U) × Hᵐ(V) → Hᵐ(U ∩ V) is onto for all m < n, and bijective
if U ∩ V has points only in zero rings. -/
lemma HV.mayer_vietoris_injective (d : IsCohomDense (locConstCoeff Λ) (((U ⊔ V).preimage
  W.ι).whisker testIncl)) n : ∀ {T} (e : T = U ⊓ V), let P := (map Λ (homOfLe l) n).prod (map Λ
    (homOfLe l') n); ((∀ m < n, ∀ z, ∃ x y, map Λ (homOfLe (e ▸ inf_le_left)) m x - map Λ (homOfLe
    (e ▸ inf_le_right)) m y = z) → Injective P) ∧ ((∀ B, T.toFunctor B → (0 : B) = 1) → Bijective P)
  | _, rfl => have r := (isCohomEquiv_iff_range (g := homOfLe (by simp; tauto : U.whisker testIncl ⊔
      V.whisker _ ≤ W.whisker _)) (by aesop (add simp [homOfLe, toFunctor]))).2 d.isCohomEquiv; by
      constructor <;> intro h <;> [convert! ← (biprodAddEquiv.injective.comp (flip .comp (r n).1
        ((contravariant mayer_vietoris_shortExact.2 _).f_injective_of_g_surjective (h · · ·
        |> Prod.exists'.2 |>.imp' biprodAddEquiv.symm ?_)))) <;> (delta contravariant);
        convert! ← (biprodAddEquiv.bijective.comp
        ((isCohomEquiv_quotient_of_acyclic mayer_vietoris_shortExact.2
        (hasPartitions_locConstCoeff.eq_zero_of_zero_ring (h ·.1))).comp_iff.2 r n))] <;> funext
        <;> simp [biprodAddEquiv, H.map, ← Functor.map_comp, sub_eq_add_neg] <;> tauto

lemma zorn_injective_and_surjective {α} [PartialOrder α] {G K : α ⥤ Ab} {π : ∀ _, _ →+ _} (w :
  ∀ {a b} h x, @K.map a b h (π a x) = π b (G.map h x)) (hc :
  ∀ {c : Set α} [IsDirectedOrder c] [Nonempty c], ∃ m, IsFilteredColimit (G.mapCocone m) ∧
  IsFilteredColimit (K.mapCocone (F := .mk (·.1 : c → α) _root_.id) m)) : ((∀ a x, π a x = 0 →
  (∀ b (h : a < b), G.map h.le.hom x = 0) → x = 0) → ∀ a, Injective (π a)) ∧ ((∀ a y, (∀ b
  (h : a < b), ∃ x, π b x = K.map h.le.hom y) → ∃ x, π a x = y) → ∀ a, Surjective (π a)) := by
  refine ⟨fun hs _ ↦ .of_ker _ (hs _ · · ?_), (· · · ?_)⟩ <;>
    refine by_contra (not_forall₂.1 · |>.imp (zorn_le_nonempty₀ {b | _} fun c h h' z hz ↦ (@hc _
    ⟨h'.directed⟩ ⟨_, hz⟩).imp' _ fun m ⟨k, l, _⟩ ↦ ⟨⟨(h hz).1.trans_le (m.ι ⟨_, hz⟩).le,
    fun e ↦ ?_⟩, (m.ι ⟨·, ·⟩ |>.le)⟩) |>.elim fun _ ⟨m, _, M⟩ ↦ M.1.2 (by apply_assumption <;>
    simp [← Functor.map_comp_apply] <;> grind [M.not_gt, M.1.1]))
  use (k.1 ⟨z, hz⟩ _ (G.map_comp_apply (h hz).1.le.hom .. ▸ e)).elim fun b ⟨_, s⟩ ↦
    (h b.2).2 (G.map_comp_apply .. ▸ s); cases e; obtain ⟨b, x, rfl⟩ := k.2 ‹_›
  refine (l b (π b x - K.map (h b.2).1.le.hom ‹_›) ?_).elim fun d ⟨q, s⟩ ↦ (h d.2).2 ⟨G.map q x, ?_⟩
    <;> erw [_root_.map_sub, w, ← K.map_comp_apply, sub_eq_zero] at * <;> tauto

/-- Let X, Y have continuous Λ-cohomology and U_a ⊂ Y (a ideals of R) be affine, behave like
zero loci, and split densely along idempotents. If u: X → Y is an equivalence over U_a for
each proper a containing e or 1 − e for every idempotent e, u is an equivalence. -/
lemma Components.isCohomEquiv_of_connected (hX : IsCohomContinuous Λ X) (hY : IsCohomContinuous Λ Y)
  (u : X ⟶ Y) {U : Ideal R → Subfunctor Y} (hU : Antitone U) (r : ∀ a, IsRelAffine (U a).ι) (N :
  ∀ {A}, Y A → AddSubmonoid R) (m : ∀ {A x a}, x ∈ U a A ↔ a.toAddSubmonoid ≤ N x) (t : ∀ {A} {x :
  Y A}, 1 ∈ N x → Subsingleton A) (d : ∀ e, IsIdempotentElem e → IsCohomDense (locConstCoeff Λ)
  ((U (span {e}) ⊔ U (span {1 - e})).whisker testIncl)) (h : ∀ a ≠ ⊤, (∀ e, IsIdempotentElem e → e ∈
  a ∨ 1 - e ∈ a) → Components Λ (fromPreimage (U a) u)) : Components Λ u := (IsCohomDense.of_top_le
  (U := (U ⊥).whisker _) fun _ _ _ ↦ m.2 bot_le).isCohomEquiv_of_fromPreimage fun n ↦ by
  have g {X} (p : X ⟶ Y) : Antitone (U · |>.preimage p) := by tauto
  have J {X} p {a e} i := let o e := @g X p _ (a ⊔ span {e}) le_sup_left;
      (HV.mayer_vietoris_injective (o e) (o (1 - e)) ((d e i).of_preimage_le (mapOnTests (_ ≫ p))
      fun _ x ↦ by apply Or.imp <;> erw [m, m, a.sup_toAddSubmonoid] <;> use (sup_le (m.1 x.2))) n
      rfl).2 fun _ ⟨_, x, y⟩ ↦ (t (by
    convert add_mem (m.1 x (?_ : e ∈ _)) (m.1 y (?_ : 1 - e ∈ _)) <;> simp [mem_sup_right])).1 ..
  have S {a} := by simpa using or_not.imp_left fun g ↦ by_cases (· ▸ by
    apply @Unique.bijective .. <;> use ⟨0⟩, hasPartitions_locConstCoeff.eq_zero_of_zero_ring (by
    exact fun _ x ↦ (t (m.1 x.2 ⟨⟩)).1 ..) n) (h a · g n)
  refine (zorn_injective_and_surjective ?w ⟨⟨_, .mk (⟨⟨le_sSup ·.2⟩⟩)⟩,
    hY.isFilteredColimit_antitoneFamily hU r ?_,
    hX.isFilteredColimit_antitoneFamily (g u) (r · |>.preimage
    u) ?_⟩).imp (· (fun a x e G ↦ S.elim (·.1 ?_) fun ⟨_, j, _⟩ ↦ (_root_.map_eq_zero_iff _ (J (𝟙 _)
    j).1).1 (Prod.ext (G _ ?_) (G _ ?_))) _) (· (fun a y G ↦ S.elim (·.2 y) fun ⟨_, j, _⟩ ↦ (G _
    ?_).elim fun x _ ↦ (G _ ?_).elim fun z _ ↦ ((J (𝟙 _) j).2 (x, z)).imp fun _ k ↦ (J u j).1 (by
    cases k; ext <;> use (?w le_sup_left.hom _).trans ‹_›)) _) <;> simp [*, ← HV.map_comp]; tauto
