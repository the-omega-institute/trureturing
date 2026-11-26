import GRH.Lib.Shimura.Uniformisation.UniformisationExists
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Moduli of abelian varieties by theta values (theta-null embedding, universal family) (known
result; see Lib.Shimura.ThetaModuli.UniversalFamily).

This file: Schematic density of points passes to stalks and to fibre products. Coordinates locally
regular combinations of a linear system form a system of same class. Closure of theta points over
the base is flat with reduced fibres. -/

section

open CategoryTheory AlgebraicGeometry Limits pullback Set Scheme Spec Pullback Over PointFn Filter
variable {S} [IsReduced S] {A B : Over S} {V W J} [Finite J] {ξ : J → (_ ⟶ S)}
  {η : W → (Spec ⟨ℂ⟩ ⟶ S)} [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom]

omit [IsReduced S] in
/-- Let A be reduced, z: A → S, s ∈ S, and x_w dense complex points of A with finitely many images
in S. Then A ×_S Spec O_{S,s} is reduced, and the lifts of the x_w to it are dense. -/
lemma isSeparatingFamily_stalk {A z x} [IsReduced A] (d : @IsDenseFamily W A x) (hx : (range (x · ≫
  z)).Finite) s : IsSeparatingFamily fun n : Σ' w ψ, map ψ ≫ S.fromSpecStalk s = x w ≫ z ↦ lift _ _
  n.2.2.symm := ⟨@isReduced_of_isReduced_stalk _ (⟨(fst z _).stalkMap_surjective · |>.forall.2
  (by simp [IsNilpotent.map_iff, stalkMap_injective_of_flat])⟩), (fst z _).isEmbedding.dense_iff.2
  fun y ↦ (((mem_closure_iff_frequently.1 (d _)).and_eventually (z.continuous.tendsto _
  (range_fromSpecStalk.le ((range_fst ..).le ⟨y, rfl⟩) (hx.eventually_all.2 fun p _ ↦
  eventually_imp_distrib_right.2 (specializes_iff_mem_closure (x := p _).2 ·.mem_closure))))).mono
  fun | _, ⟨⟨w, rfl⟩, b⟩ => ⟨_, ⟨⟨w, S.presheaf.stalkSpecializes (b _ ⟨w, rfl⟩ rfl) ≫ _, by
  simpa [-Hom.comp_base] using Spec_stalkClosedPointTo_fromSpecStalk _⟩, rfl⟩, by
  erw [← Hom.comp_apply, lift_fst]⟩).mem_closure⟩

lemma stalk_eq_zero_of_dense (hξ : IsDenseFamily ξ) {x} a (h : ∀ n : Σ' i ψ,
  map ψ ≫ S.fromSpecStalk x = ξ i, n.2.1 a = 0) : a = 0 := by simpa using ((isSeparatingFamily_stalk
  hξ (toFinite _) x).pointFn_ext (f := fun _ y ↦ preimage (y ≫ snd ..) a) (by simp [IsRegularOn])
  (isRegularOn_ofSection 0) (by simpa [lift_snd]) _ (inv (snd (𝟙 _) _)) landsIn_top)

open MonoidalCategory IsSchemeTheoreticallyDominant LocallyOfFiniteType CartesianMonoidalCategory

/-- Let S be reduced, locally noetherian, with a dense finite set of complex points; A, B flat,
locally of finite type, A reduced. If y_w : T_w → B separate B and e_w(v) : T_w → A separate
A ×_S T_w, the (e_w(v), y_w) separate A ×_S B (`IsSeparatingFamily`). -/
lemma IsSeparatingFamily.prod [IsLocallyNoetherian S] [Flat A.hom] [Flat B.hom] {y : ∀ w,
  .mk (η w) ⟶ B} {e : ∀ _, V → (_ ⟶ A)} (k : IsSeparatingFamily (y · |>.1)) (hξ :
  IsDenseFamily ξ) (r : IsReduced A.left) (h : ∀ w, IsSeparatingFamily fun
  v ↦ lift _ (𝟙 _) (e w v).w) : IsSeparatingFamily fun z : W × V ↦ (lift (e _ z.2) (y z.1)).1 := by
  let j := A.hom.smoothLocus.ι
  obtain _ := k.1, isLocallyNoetherian A.hom, isLocallyNoetherian B.hom,
    (j ≫ A.hom).smoothLocus_eq_top_iff.1 (by simp [j, ← j.preimage_smoothLocus_eq]), @of_isDominant
    _ _ j ⟨((dense_iff_closure_eq.2 genericPoints.closure).mono ((fun k ↦ @.of_perfectField _ _
    k.toField (IsLocalHom.isField (stalkMap_injective_of_flat ..) k).toField (_) (@.ofCharZero _ (_)
    (not_forall.1 (one_ne_zero ∘ stalk_eq_zero_of_dense hξ 1)).choose.2.1.1.charZero)
    (stalkMap ..)) ∘ isField_stalk_of_closure_mem_irreducibleComponents _ ·)).denseRange_val⟩ _
  use isReduced ((pullbackRightPullbackFstIso _ _ j).inv ≫ snd ..), (k.2.preimage (Hom.isOpenMap
    _)).induction (fun t ⟨w, a⟩ ↦ (by simpa [range_map, whiskerLeft_left] using ⟨_, a⟩ : t ∈ range
    (A ◁ y w).1).choose_spec ▸ map_mem_closure (by fun_prop) ((h w).2 _) fun _ ⟨q, o⟩ ↦ o ▸
    ⟨⟨w, q⟩, congr($(lift_whiskerLeft (e ..) (𝟙 _) _).1 _).symm⟩) (by simp)

end

open CategoryTheory PointFn LineBundle AlgebraicGeometry Limits MvPolynomial Scheme RingHom Flat
  pullback Over

/-- Let w false, w true be vectors at dense complex points ξ of reduced Z, each entry locally a
regular function times a Q-indexed sum of the other's entries. If w false coordinatises a
linear system M, w true coordinatises one of the same class. -/
lemma exists_isLinearSystem {Z J Q X M} [Fintype J] [Fintype Q] {ξ : X → (_ ⟶ Z)} (w : _ → X →
  J → ℂ) (sep : IsSeparatingFamily ξ) (hM : IsLinearSystem M) (blk : ∀ a,
  M.IsHomogCoords (ξ a) (w false a)) (h : ∀ b j s, ∃ U, s ∈ U ∧ ∃ e : Q → _, ∃ c, IsRegularOn c U ∧
  ∀ a, LandsIn (ξ a) U → c _ (ξ a) * ∑ q, w (!b) a (e q) = w b a j) :
  ∃ N, IsLinearSystem N ∧ (∀ a, N.IsHomogCoords (ξ a) (w true a)) ∧ N.picClass = M.picClass := by
  choose U _ e c _ _ using h true
  let σ j (k : J × (J → Z)) := c j (k.2 j) * ∑ q, M.transition k.1 (e j (k.2 j) q)
  refine ((M.mul (LineBundle.pi (LineBundle.mk (opens := U ·) 1
    (by aesop)) ∅)).exists_picClass_eq_pull_hyperplane (𝟙 _) (s := σ) (fun j ↦ ⟨?_, fun i k _ _ ↦
    (sep.pointFn_ext (g := _ * _) ?_ ?_ ?_ _ _ <| landsIn_inf.2 ⟨·, ·⟩)⟩) fun k _ _ _ n ↦ (h false
    k.1 _).elim fun _ ⟨v, e, c, _⟩ ↦ Function.mtr (by simp_all) (sep.pointFn_ext (g := 1) (f := c *
    ∑ q, σ (e q) k) ?_ ?_ ?_ _ _ (landsIn_inf.2 ⟨n, landsIn_iff_mem.2 v⟩))).elim fun f r ↦ ⟨_,
    ProjSpace.isLinearSystem_hyperplaneBundle.pull f, (ξ · |> exists_landsIn _ |>.elim
    (forall_imp ?_ <| r.2 · _ _)), ?_⟩ <;> simp_all [σ, IsRegularOn, IsLinearSystem, IsHomogCoords,
    ← mul_assoc, ← Finset.sum_mul, landsIn_iInf]; grind

attribute [local simp] lift_fst lift_snd specMap

/-- At the K-point t, in every chart c, the vanishing ideal of the part of Z ⊂ K^J with v_c ≠ 0,
scaled to v_c = 1, satisfies `IsCutOut` for the points P(t). -/
def IsCutOutAt {J I K} [Field K] {S} r i σ (P : I → LineBundle S J) t (Z : Set (J → K)) := ∀ l : I →
  _, (∀ a, LandsIn t ((P a).opens (l a))) → ∀ c, IsCutOut r i σ c (fun a j ↦
  (P a).transition (l a) j ⟨K⟩ t) (⨅ v ∈ {v ∈ Z | v c ≠ 0}, ker (eval (v · / v c)))

/-- Let S be reduced, finitely many of the η n dense, r > 1; assume `IsCutDegree`,
and `IsCutOutAt` at η n for the image of θ n and at a geometric specialisation of
every point. Then some flat closed A ⊂ ℙ^J_S has reduced fibres over η n, in which the θ n z
are dense, and at such specialisations. -/
lemma exists_flat_closure {J W ι I κ S r i σ} [Finite J] [Finite ι] [IsReduced S] (j : ι → κ) {η :
  κ → _} (D : IsDenseFamily fun n ↦ η (j n)) {P : I → _} (B : ∀ a,
  (P a).IsLinearSystem) (H : 1 < r) (Y : IsCutDegree J i r σ) {θ : κ → W → J → ℂ} (hθ : ∀ n z,
  θ n z ≠ 0) (h : ∀ n, IsCutOutAt r i σ P (η n) (.range (θ n))) (cl : AllSpecializeTo S
  fun t ↦ ∃ Z, IsCutOutAt r i σ P t Z) : ∃ A N, ∃ e : ∀ n, W → (mk (η n) ⟶ A),
  IsProjEmbedding N A.hom ∧ Flat A.hom ∧ (∀ n z, IsHomogCoords N (e n z).left (θ n z)) ∧
  (∀ n, IsSeparatingFamily fun v ↦ (lift _ (𝟙 _) (e n v).w :)) ∧ AllSpecializeTo S (fun t ↦
  IsReduced (pullback A.hom t)) ∧ IsSeparatingFamily fun s : κ × W ↦ (e s.1 s.2).left := by
  choose χ ν using (Function.ne_iff.1 <| hθ · ·)
  choose p o g using fun w : ι × W ↦
    ProjSpace.exists_isHomogCoords (η (j w.1)) (ν (j w.1) w.2).isUnit
  choose Z ε x₀ _ E b d using exists_reduced_closure p
  simp [← E, ← IsHomogCoords.pull_iff, -Prod.forall] at o g
  generalize ε ≫ _ = z, pull _ ε = N, (isProjEmbedding_projSpace).comp ε = M at *
  choose T u Q F V using fun {R b c} ↦
    (M.of_isPullback (.of_hasPullback z b)).exists_affine_chart (R := R) c
  let O {R} b := (AffineOpenCover.ofIsOpenCover _ (cover _) (@T R b)).openCover
  have L {R b c A} [CommRing A] {φ : _ →+* A} : ker (@u R b c) ≤ RingHom.ker φ ↔ ∃ y,
    LandsIn y (N.opens c)
    ∧ y ≫ z = specMap (φ.comp C) ≫ b ∧ ∀ j, N.transition c j _ y = φ (X j) := ⟨fun h ↦ by
    obtain ⟨ψ, ⟨⟩⟩ := (u.liftOfSurjective Q).symm.surjective ⟨φ, h⟩
    exact landsIn_fromSpec T (specMap ψ) |> fun i ↦ ⟨_, landsIn_preimage.1 i, by simp [ext (f :=
      ψ.comp _) (ofSection_map_fromSpec .. ▸ V i ·), condition]⟩, fun ⟨y, a, k, h⟩ f _ ↦
    by simpa [*, mem_ker.1, ← hom_eval₂] using (V (lift_fst _ _ k ▸ a :) f).symm⟩
  choose G k R using fun {k} [Field k] {t 𝔭} (h₀ : IsCutOutAt (K := k) r i σ P t 𝔭) ↦ show _ ∧ _ ∧
    _ by
    have a := Spec_stalkClosedPointTo_fromSpecStalk t
    set c := fromSpecStalk ..
    choose _ q using (P · |>.exists_landsIn c)
    have v F ψ := funext₂ fun a j ↦ @((B a).1 _ j).1 _ F ψ _ (q a)
    have K m := map_eq_and_flat_of_isCutOut _ (ker (@u _ c m)) (stalk_eq_zero_of_dense D) H Y
      (v .. ▸ (a ▸ h₀) _ (q · |>.comp _) m) (fun n ↦ v .. ▸ (n.2.2 ▸ h _) _ (q · |>.comp _) m)
      fun f ↦ .trans ⟨by tauto, fun h ↦ (ofSection_map_fromSpec T _ (𝟙 _)).symm.trans
      (((isSeparatingFamily_stalk d ((Set.finite_range (η ∘ j)).subset (by simp_all)) _).pointFn_ext
      (isRegularOn_ofSection _) (isRegularOn_ofSection 0) h _ _ (landsIn_fromSpec T _)).trans
      (by simp))⟩ (by simp +contextual [*, g .., division_def, PSigma.forall, @forall_comm W])
    have e m := (K m).1.trans (eq_of_forall_ge_iff (b := ker (@u _ t m)) (·.mk_ker ▸ by
      simp [↓Ideal.map_le_iff_le_comap, ↓comap_ker, ↓L, comp_assoc, a]))
    use fun y ↦ (comp_iff_of_bijective_left ⟨stalkMap_injective_of_flat .., Hom.stalkMap_surjective
      _ y⟩).1 (Hom.stalkMap_comp .. ▸ @stalkMap _ _ _ (condition.symm.subst (.comp (hf :=
      HasRingHomProperty.instIsZariskiLocalAtSource.of_openCover (O c) fun m ↦ F ▸ SpecMap_iff.2
      (respectsIso.1 _ (quotientKerEquivOfSurjective Q) (flat_algebraMap_iff.2 (K m).2))) ..)) y),
      e, @IsReduced.of_openCover _ (O t) fun c ↦ (affine_isReduced_iff _).2
      ((ker_isRadical_iff_reduced_of_surjective Q).1 (e c ▸ fun _ h ↦ h.elim (by simp_all)))
  choose x q using fun n v ↦ ((L.1 ((k (h n) _).ge.trans (iInf₂_le _ ⟨⟨v, rfl⟩, ν n v⟩))).elim
    fun y ⟨b, e, E⟩ ↦ ⟨homMk y (by simp [e, MvPolynomial.eval]), by grind [M.1.2 b, IsHomogCoords,
    eval_X, homMk_left]⟩ : ∃ x : mk (η n) ⟶ mk z, N.IsHomogCoords x.1 (θ n v))
  exact ⟨_, N, x, M, .of_stalkMap _ fun x ↦ (cl (z x)).elim fun _ ⟨_, _, _, s, _, h⟩ ↦
    ((Pullback.range_fst ..).ge (range_fromSpecStalk.ge s)).choose_spec ▸ G h _, q, fun n ↦ ⟨R (h
    n), fun y ↦ by_contra fun H ↦ have ⟨c, a⟩ := TopologicalSpace.IsOpenCover.exists_mem (cover _) y
    have ⟨f, F, Y⟩ := Q.exists.1 (T.exists_basicOpen_le (V := ⟨_, isClosed_closure.1⟩) ⟨y, H⟩ a)
    by simpa using ((k (h n) c).le (by simpa using fun v _ ↦ by_contra fun _ ↦ F (landsIn_iff_mem.1
      (by rw [landsIn_basicOpen]; simpa [q .., *]; simp [q .., *])) (subset_closure ⟨v, rfl⟩)) ▸
      Y :)⟩, by peel 6 cl; tauto, b,
    d.mono (by simp [fun w ↦ M.eq_of_isHomogCoords ((x ..).w ▸ o w) (g w) (q _ _)])⟩
