/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/ProperBaseChange
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/ProperBaseChange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.ProperBaseChange.ProperBaseChange. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/ProperBaseChange/ProperBaseChange.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.ProperBaseChange.SubringSplitting
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.ProperFunctors
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Proper base change and invariance under extension of algebraically closed fields.
Here the coefficients are constant F_ℓ, the base is an absolutely integrally closed valuation ring,
and properness of a functor is expressed by valuative lifting. The proof reduces to spaces of places
of a field, then uses Zorn's lemma on subrings with a Mayer–Vietoris splitting and Kummer theory.
Source: Artin, SGA 4 Exp. XII 5.1, 5.4, 5.5 (1973); Stacks Project Tag 095S; reduction to spaces of
places as in Scholze, Étale cohomology of diamonds (2017), Thm 19.2 and Lemma 19.4, after Huber,
Math. Ann. 295 (1993).

This file: Proper base change: closed fibre over an absolutely integrally closed valuation ring, F_l
coefficients. -/

open CategoryTheory CommRingCat Subfunctor IsLocalRing Ideal Quotient ResiduePlace aicSubrings
  Filter Comparison ULift Functor Subring RingHom

/-- Proper base change: for a functor Y proper over an absolutely integrally closed valuation
ring A and ℓ a prime invertible in A, restriction from Y to its closed fibre is bijective on
all cohomology groups with coefficients ℤ/ℓ.

Known result: Proper base change; invariance under extension of algebraically closed fields. -/
lemma IsProperOver.proper_base_change {ℓ} [ThePrime ℓ] {Y A} [CommRing A] [IsAICLocal A]
  [PreValuationRing A] {s} (h : @IsProperOver Y ⟨A⟩ s) (u : IsUnit (ℓ : A)) :
  Components ⟨ZMod ℓ⟩ (zeroPoints s (maximalIdeal A)).ι :=
  (show IsBijective _ (freeAbMap (Y := _ ⋙ Y) _) from forall_bijective_iff_bijectiveUpTo.2 (by
  induction' · with _ ih generalizing Y; tauto
  refine h.exists_placeSpace_cover.elim fun P ⟨ξ, z, d⟩ ↦ have := z.isAlgClosed_residueField
    bijectiveUpTo_of_cech_pred (p' := mapOnTests (fromPreimage _ (placeSpaceMap z))) (v :=
      mapOnTests (ι _)) rfl d.isCohomEquiv (d.of_preimage_le (mapOnTests (ι _)) (by
               rintro _ ⟨⟩ ⟨_, ⟨⟩⟩; tauto)).isCohomEquiv ?_ fun m ↦ (bijectiveUpTo_congr (p := 𝟙 _)
      ((whisker (zeroPoints ..) testIncl).lift_ι _ fun _ _ ⟨x, e⟩ ↦ e ▸ (x.1 0).2) (.of_isIso _)
      (.of_bijective fun _ ↦ (Equiv.mk _ fun x ↦ ⟨fun i ↦ ⟨_, (x.1.2 0 i ▸ x.2 : _ ∈ zeroPoints s _
      _)⟩, (congr(⟨$(x.1.2 · ·), _⟩))⟩).bijective)).1 (@ih _ (cech.proj (placeSpaceMap z) m 0 ≫ _ ≫
      s) (m.rec (isProperOver_placeSpace.of_isPullback isProperOver_placeSpace (.of_vert_isIso
      (g := 𝟙 _) ⟨rfl⟩) isProperOver_placeSpace (𝟙 _) rfl) fun _ ↦
      (isProperOver_placeSpace.of_isPullback h isPullback_cech · (𝟙 _) rfl)))
  refine (Components.isCohomEquiv_of_connected
    (isProperOver_placeSpace.isCohomContinuous.of_isRelAffine ((isRelAffine_zeroPoints ..).preimage
    _)) isProperOver_placeSpace.isCohomContinuous _ (by tauto) isRelAffine_killingPlaces (placeGraph
    · |>.toAddSubmonoid.comap (.inl .. : _ →+ _)) .rfl (⟨eq_of_zero_eq_one <| placeGraph_unique ·
    (one_mem _)⟩) (fun e i ↦ .of_affine_cover (isRelAffine_killingPlaces <|
    span {cond · e (1 - e)}) fun _ x ↦ (exists_place_of_isLocalRing x).elim
    fun j ⟨_, _, H⟩ ↦ have := H _ _ le_rfl ▸ projRing_mem_killingPlaces j _; by
      cases @j.prime.2.2 e (1 - e) (by simp [i]) <;>
        [use ⊤; use ⊥] <;> rw [← span_singleton_le_iff_mem] at * <;> tauto) fun q T g ↦ ?_).bij
  have M := isMaximal_iff.2 ⟨q.ne_top_iff_one.1 T, fun J t ↦ by grind [z.absolutely_flat t,
    IsIdempotentElem, mul_mem_right, mul_mem_left, J.sub_mem_iff_left, IsConcreteLE.le_iff]⟩
  let γ := (algebraMap P q.ResidueField).comp (baseRingMap s ξ).hom
  let φ {C} (y : killingPlaces z q C) : finiteSubring z y →+* C :=
    .liftOfSurjective _ (rangeRestrict_surjective _) ⟨.domRestrict (snd ..) _, fun v k ↦
    placeGraph_unique v.2 (y.2 _ ((ker_algebraMap_residueField _).le congr($k.1)))⟩
  have hφ {C y} v : @φ C y ⟨_, v, rfl⟩ = v.1.2 := liftOfSurjective_comp_apply ..
  let ς {J} B : (placesFiniteOn z J B.1).toFunctor ⟶ reprBy (quotientFunctor J γ B) :=
    ⟨fun C ↦ ↾fun x ↦ ⟨ofHom (lift _ ((φ _).comp (B.1.inclusion x.2.2)) (map_le_of_le_comap (K :=
    ker _) fun a ↦ (hφ ⟨_, baseRingMap_mem_placeGraph a⟩).trans ∘ x.2.1 a))⟩, by
    intros; ext x; congrm ⟨?_⟩; ext ⟨_, h⟩; obtain ⟨v, rfl⟩ := x.2.2 h
    exact hφ ⟨(_, _), placeGraph_map (hφ v ▸ v.2)⟩⟩
  let σ {J} B : ((placesFiniteOn ..).whisker testIncl).toFunctor ⟶ _ := mapOnTests (@ς J B)
  have G J [p : IsPrime J] B : IsAcyclicOver (@σ J B) _
  have a : Antitone (placesFiniteOn z J ·.1 : aicSubrings γ → _) := antitone_const.inf (by tauto)
  have hκ n {B B'} l x : (HV.antitoneFamily a ..).map l (locConstClass (σ B) n x) =
    locConstClass (σ B') n ((_ ⋙ locConstSpec ⟨ZMod
    ℓ⟩).map l x) := map_locConstClass (by intros; erw [← map_comp_apply]; congr 3 with ⟨⟩; rfl) n
  have V B {Λ} : _ ∨
    IsAcyclicOver (σ B) Λ := let π := ofHom (Ideal.Quotient.mk (extendedIdeal J γ B))
    (em' _).imp (exists_split_mayer_vietoris J γ u B)
      fun n ↦ let j := ResiduePlace.mk ⟨q, _⟩ ⟨_, n⟩ (B.2.1 ⟨·, rfl⟩)
      .of_bijective (.quotient (@isTest_of_preValuationRing j.valSubring _ _ _ _)
        ((Ideal.isRadical_iff_pow_one_lt 2 .refl).2 fun x i ↦
        (exists_map_dvd_of_mem_map i).rec fun i ⟨m, k⟩ ↦ (IsAIC.exists_pow_eq 2 i).rec fun c e ↦
        mem_of_dvd _ (by simpa [← e] using k) (mem_map_of_mem _ (p.isRadical ⟨_, e ▸ m⟩)))) <|
        have c {C x φ} (e : x.1.1 = ⟨⟦j.projRing ≫ φ⟧⟩) : π ≫ @baseRingMap _ _ (ς B) C x = φ := by
          ext ⟨_, h⟩; obtain ⟨v, rfl⟩ :=
            x.2.2 h; exact hφ ⟨_, e.substr (mem_fractionGraph_projRing ..)⟩
        Equiv.bijective ⟨_, ((placesFiniteOn ..).toFunctor.map ·.1 ⟨⟨_,
          projRing_mem_killingPlaces j π⟩, fun a i ↦ (placeGraph_unique
        (baseRingMap_mem_placeGraph a) (by apply mem_fractionGraph_projRing)).trans
          (mk_ker.ge (mem_map_of_mem _ i)), q.algebraMap_residueField_surjective.forall.2
          (⟨⟨_, j.mem_fractionGraph_projRing · ·⟩, rfl⟩)⟩), fun x ↦ SetCoe.ext
        (SetCoe.ext (isProperOver_placeSpace.ext_of_jointly_injective (ofHom <| algebraMap _ <|
          Localization.AtPrime <| MaximalSpectrum.asIdeal ·) (eq_zero_of_localization · fun _
          k ↦ · ⟨_, k⟩) fun _ ↦ let y := (placesFiniteOn ..).toFunctor.map _ x
          (((finiteSubring_total_and_exists_place y.1.2).2 j.valSubring _ y.2.2).elim fun φ e ↦
            .symm (by rwa [← c e, baseRingMap_map] at e)
        : _ = y.1.1))), fun φ ↦ down_injective (hom_ext (ringHom_ext congr($(c rfl).1)))⟩
  have K n := zorn_injective_and_surjective (G :=
    quotientFunctor .. ⋙ locConstSpec _) (hκ n) @fun c hc ⟨o⟩ ↦ let φ (a : c) := a.1.1
    have E (x : ↥(iSup φ)) : ∀ᶠ b in atTop, x.1 ∈ φ b := mem_atTop_sets.2 (.imp (by tauto)
    ((mem_iSup_of_directed hc.1).1 x.2)); ⟨⟨⟨_, le_iSup_of_le o o.1.2.1, ⟨fun P ↦
    (P.coeffs.eventually_all.2 fun y _ ↦ E y).exists.rec fun b k ↦
      b.1.2.2.exists_root_of_coeffs_subset_range (f := inclusion (le_iSup φ b)) (⟨⟨_, k · ·⟩,
      rfl⟩)⟩⟩, .mk (⟨⟨le_iSup φ ·⟩⟩)⟩, isFilteredColimit_locConstSpec (c :=
      (quotientFunctor ..).mapCocone _) (Quot.ind (E · |>.exists.imp fun _ ↦ (⟨⟦⟨_, ·⟩⟧, rfl⟩))) (by
    rintro j ⟨⟩ k
    obtain ⟨o, i, f, e⟩ := exists_map_dvd_of_mem_map (eq_zero_iff_mem.1 k)
    exact ((E f).and (mem_atTop j)).exists.imp fun b witness ↦ by
      obtain ⟨h, l⟩ := witness
      exact ⟨l.hom, eq_zero_iff_mem.2
      (mem_of_dvd _ ⟨⟨_, h⟩, by congrm ⟨$e.1, _⟩⟩ (mem_map_of_mem _ i))⟩),
      (isProperOver_placeSpace.isCohomContinuous.of_isRelAffine
    (isRelAffine_killingPlaces _)).isFilteredColimit_antitoneFamily a (fun _ ↦
      isRelAffine_placesFiniteOn) (by simp [placesFiniteOn, forall_and]; tauto)⟩
  have i := (K 0).1 fun B _ _ _ ↦ (V B).elim (by tauto) (·.1 (by simpa))
  refine ⟨i B, (·.strongRecOn (fun m ih ↦ (K m).2 fun B y g ↦ (V B).rec ?_ (·.2 ..)) B)⟩
  rintro ⟨B₁, B₂, C, l₁, l₂, _, _, u, v, _, k, o⟩; obtain ⟨⟨x₁, e₁⟩, x₂, e₂⟩ := g _ l₁, g _ l₂
  have t := (HV.mayer_vietoris_injective (a l₁.le) (a l₂.le) (.of_affine_cover
    (isRelAffine_placesFiniteOn (B := cond · B₁.1 B₂.1) |>.preimage (placesFiniteOn ..).ι) fun _ ⟨_,
    i, j⟩ ↦ (v ⟨_, (finiteSubring_total_and_exists_place _).1⟩ j).elim (⟨⊤, by tauto, i, ·⟩) (⟨⊥, by
    tauto, i, ·⟩)) m (T := placesFiniteOn z J C) (by ext; simp [placesFiniteOn, u]; tauto)).1
    (ih · · _ |>.forall.2 (o · |>.rec fun _ ⟨_, e⟩ ↦ by erw [e, _root_.map_sub, ← hκ, ← hκ]; tauto))
  cases m <;> [(obtain ⟨x, rfl, rfl⟩ := k x₁ x₂ (i _ (by
    erw [← hκ, ← hκ, e₁, e₂, ← map_comp_apply, ← map_comp_apply]; rfl)); use x);
    use 0] <;> exact t (Prod.ext ((hκ _ l₁.le.hom _).trans e₁) ((hκ _ l₂.le.hom _).trans e₂))
  have S := γ.rangeRestrict_surjective
  let B : aicSubrings γ := ⟨_, le_rfl, .of_surjective S⟩
  have T A x : x ∈ placesFiniteOn z ⊥ B.1 A := ⟨by simp [zeroPoints], fun _ witness ↦ by
    obtain ⟨a, e⟩ := witness
    exact ⟨⟨_, baseRingMap_mem_placeGraph a⟩, e⟩⟩
  exact (isCohomEquiv_iff_range (hg := mono_of_app_injective (by rintro _ ⟨⟨⟩⟩ ⟨⟩ ⟨⟩; rfl)) (U :=
    (placesFiniteOn ..).whisker _) (by ext _ ⟨⟩; exact ⟨fun witness ↦ by
      obtain ⟨y, e⟩ := witness
      exact ⟨e ▸ y.1.2, (T ..).2⟩, (⟨⟨⟨_,
    ·.1⟩, ‹_›⟩, rfl⟩)⟩)).2 (by simpa [← map_comp] using! (((G ⊥ B).isCohomEquiv (isDomain (hI := by
    simp [isPrime_bot])) (isDomain (hI := map_isPrime_of_surjective S (le_maximalIdeal (ker_ne_top
    _)))) (homOfLe (by tauto)) (G _ B)).comp_iff.2 (IsCohomDense.isCohomEquiv .of_top_le))))).eqv
