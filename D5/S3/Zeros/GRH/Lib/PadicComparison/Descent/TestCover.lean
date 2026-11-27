/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/Descent/TestCover
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/Descent/TestCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.Descent.TestCover. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/Descent/TestCover.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Geometry.OpenSubfunctors
import D5.S3.Zeros.GRH.Lib.Cohomology.ProperBaseChange.ValuativeDensity
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Almost acyclicity of the structure sheaf for the v-topology (known result; see
Lib.PadicComparison.Descent.AlmostAcyclic).

Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: One test covers all points; dévissage from representables to affinely covered
functors. -/

open Function Pi CategoryTheory CommAlgCat Envelope Filter Ideal IsLocalization Quot Ten PadicTest
  ValuationRing Limits ShortComplex Subfunctor Ideal.Quotient

attribute [-simp] Nat.cast_eq_zero isUnit_map_iff

variable {p} [ThePrime p] {C} [Category C] {A} [CommRing A] {ι : C ⥤ CommAlg A} [ι.Full]

omit [ThePrime p] in
/-- If B is p-torsion-free and m is a prime ideal of B containing p, there are a cell W
(`IsCell`) and a ring map B → W sending every element of m to a non-unit. -/
lemma exists_cell_over {B} [CommRing.{0} B] {m} (_ : IsPrime m) (h : IsSMulRegular B p)
    (hp : ↑p ∈ m) : ∃ W, ∃ (_ : CommRing W) (_ : IsCell p W) (y : B →+* W),
  ∀ z ∈ m, ¬IsUnit (y z) := let L := Localization.AtPrime m
  have ⟨U, g, l⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap L (AlgebraicClosure
    (Classical.arbitrary (PrimeSpectrum (FractionRing L))).1.ResidueField))
  let G := (hyperfilter ℕ).Germ U
  let γ : _ →+* G := Germ.coeRingHom _
  have Q : Surjective γ := exists_rep
  have N z hz (u : γ _ ∣ 1) := (AtPrime.isUnit_to_map_iff L m z).1 (l.1 _ (isUnit_of_dvd_one
    ⟨_, (Germ.coe_eq.1 (Q.exists.1 u).choose_spec).exists.choose_spec⟩)) hz
  have : PreValuationRing G := ⟨Q.forall₂.2 fun _ _ ↦ (skolem.1 (.of_forall fun _ ↦
    cond _ _)).imp' γ fun _ ↦ .imp sound sound ∘ Ultrafilter.eventually_or.1⟩
  let π := algebraMap _ (PadicCompletion G p)
  have S : Surjective π := AdicCompletion.of_surjective_iff.2 (Set.pair_eq_singleton _ ▸ by
    apply isPrecomplete_of_shiftDiff_surjective <;> exact Q.comp_left.forall.2 fun c ↦ ⟨(γ fun k ↦
      List.Ico · k |>.foldr (c · k + p * ·) 0), funext fun n ↦ sound (Nat.hyperfilter_le_atTop
      ((eventually_gt_atTop n).mono (by simp_all [List.Ico.eq_cons])))⟩)
  have r := @isSMulRegular_completion G _ G _ _ p (Q.forall₂.2 fun _ _ e ↦
    sound ((Germ.coe_eq.1 e).mono fun _ e ↦ Subtype.ext (((map_units (FractionRing L) ⟨_,
    map_nonZeroDivisors_le m.primeCompl L ⟨_, by simpa [mem_nonZeroDivisors_iff_left] using
    (@h · 0), rfl⟩⟩).map (algebraMap ..)).mul_left_cancel (by simpa using congr($e.1)))))
  have := S.preValuationRing π.toMulHom
  have := (isDomain_iff_noZeroDivisors_and_nontrivial _).2 ⟨⟨or_iff_not_imp_right.2 ∘ fun e h ↦
    eq_zero_of_forall_pow_dvd fun n ↦ (dvd_total ..).resolve_right fun witness ↦ by
      rcases witness with ⟨_, d⟩
      exact h (r.pow n (by simp_all [mul_right_comm]))⟩, _ ^ 1, π 1, (N p hp <| by simpa using pow_dvd_iff.1 ·.dvd)⟩
  ⟨_, _, @.mk _ _ _ _ ⟨⟩ isAdicComplete (((IsTest.pi).of_surjective Q).of_surjective S)
    (r.ne one_ne_zero ∘ by simp), π.comp (γ.comp
    (.pi fun _ ↦ .comp (.codRestrict _ _ g) _)), (N · · <| S.isLocalHom.1 _ · |>.dvd)⟩

attribute [local simp↓] smodEq_span_pow_iff_dvd

/-- an algebra with a point in some test has a point through which every point factors -/
instance exists_padicTest_cover : HasCoveringPoints algFunctor := .mk fun B c z ↦ by
  choose φ hφ k using fun d (z : B →+* ProdRing d) j ↦
    exists_isSolutionClosed ((evalRingHom _ j).comp z)
  let i d z j : {q : Ideal _ // IsCell p (_ ⧸ q)} := ⟨_, have h := k d z j; have hV := d.isCell j
      by refine @.mk _ _ _ h.1.isDomain ((@iff_dvd_total _ _ (_)).2 ⟨?_⟩) {
        haus' := ?_, prec' f e := by simpa [IsSolution, ← h.map_dvd_iff] using h.2 1 (·.casesOn p f)
                                       (by simpa [IsSolution] using hV.prec' _ (by simp_all
          [← h.map_dvd_iff]))} (h.isTest isTest_of_preValuationRing).1 ?_ <;>
        simp_all [← h.1.eq_iff, ← h.map_dvd_iff, dvd_total, hV.haus, hV.5]⟩
  exact ⟨_, (@cellPoint _ _ _ _ ⟨i c z.1.1.1 c.nonempty.some⟩ _ _ (·.2) fun _ ↦ algebraMap ..).2,
    fun d
    ⟨z⟩ ↦ have e x := funext (congr($(hφ d z.1.1 ·) x)); ⟨⟨.pi fun j ↦ (φ d z.1.1 j).kerLift.comp
    (evalRingHom (_ ⧸ ·.1) (i ..)), (z.1.2 · ▸ e _)⟩, congr(⟨$(ConcreteCategory.ext_apply e)⟩)⟩⟩

instance : algFunctor.Full := ⟨by tauto⟩

/-- Flat base change (`FP`) defines a closed class of functors from C to abelian
groups: it holds 0 and, for M' ⊂ M with M' in it, holds M exactly if it holds M/M'. -/
lemma FP.isClosedClass : @IsClosedClass C _ FP := by simp_all [IsClosedClass, FP, AllBijective,
  devissage.isClosedClass.1, devissage.isClosedClass.2]

omit [ι.Full] in
/-- For a functor ι from C to commutative A-algebras and any A-algebra B, the functor
Hom(B, −) is affinely covered along ι (`IsAffinelyCovered`). -/
lemma isAffinelyCovered_reprBy B : IsAffinelyCovered ι (reprBy B) :=
  ⟨⟨fun _ x y ↦ ⟨⨆ a, Ideal.span {x.1.hom a - y.1.hom a}, fun _ _ ↦
  ULift.up_inj.trans (by simp [ConcreteCategory.hom_ext_iff])⟩⟩, B, ⟨𝟙 _⟩, by tauto⟩

variable [ι.Faithful] [HasCoveringPoints ι] {Y}

/-- Let ι be full and faithful with `HasCoveringPoints`, let f satisfy `Devissage`. If f is
bijective in all degrees on Z[h_c] for every object c, it is so on Z[Y] for every Y satisfying
`IsAffinelyCovered`. -/
lemma IsAffinelyCovered.devissage_bijective {M N f} (h : @Devissage C _ M N f) (rp : ∀ c,
  AllBijective (f (freeAb.obj (reprBy c)))) (k : IsAffinelyCovered ι Y) :
  AllBijective (f (freeAb.obj (ι ⋙ Y))) :=
  forall_bijective_iff_bijectiveUpTo.2 (·.rec (by tauto) (fun _ i X ⟨⟨s⟩, B, y, hp⟩ ↦ by_contra
  fun n ↦ n (forall_bijective_iff_bijectiveUpTo.1 (h.isClosedClass.1 _ (freeAb.hom_ext fun d
  w ↦ have ⟨c, ⟨η⟩, u⟩ := HasCoveringPoints.exists_surjective_point B (hp d w).choose
  let q := reprMap η ≫ pointMap y
  have := (range (ι.whiskerLeft q)).eq_top_iff_isIso.1
    (top_unique fun d x _ ↦ ((hp d).comp (u d) x).imp' _ (by tauto))
  by apply n.elim ∘ h.step ⟨exact_kernel
    (freeAb.map (range (ι.whiskerLeft q)).ι)⟩ (cech_descent_step _ h.1 _ fun m ↦ i (cech q m)
    ⟨⟨fun _ x y ↦ ⟨⨆ (i) (a), span {(x.1 i).1.hom a - (y.1 i).1.hom a}, by simp +instances [cech,
    funext_iff, reprFunctor, ConcreteCategory.hom_ext_iff]⟩⟩, let e := Sigma.ι fun _ ↦ ι c; by
  choose J h using fun i j ↦ s _ (X.map (η ≫ e i) y) (X.map (η ≫ e j) y)
  simp [e, ← X.map_comp_apply, -Functor.map_comp] at h
  exact ⟨_, ⟨(⟨e · ≫ ofHom (mkₐ ..)⟩), fun _ _ ↦ (h ..).2 ((le_iSup J.uncurry
    (_, _)).trans mk_ker.ge)⟩, fun d x ↦ ⟨⟨ofHom (liftₐ _ _ (iSup_le fun _ ↦ (h ..).1 (by
    simpa [-Functor.map_comp] using! x.2 ..)))⟩, congr(⟨(⟨$(Sigma.ι_desc (x.1 · |>.1) ·)⟩), _⟩)⟩⟩⟩)
    <;> solve_by_elim [forall_bijective_iff_bijectiveUpTo.1, h.isClosedClass.1,
    (isZero_kernel_of_mono _).eq_of_src, h.isClosedClass.of_bijective,
    pointMap_id_bijective_of_fullyFaithful])) _)) Y k)

/-- Let ι from C to A-algebras be fully faithful, and suppose each A-algebra B with a point in
some ι(c) has one point through which all its points factor. If Y is affinely covered
(`IsAffinelyCovered`), then ℤ[Y] has flat base change. -/
lemma IsAffinelyCovered.hasFlatBaseChange (k : IsAffinelyCovered ι Y) :
  FP (freeAb (ι ⋙ Y)) := by simp_all [FP, devissage_bijective devissage freeAb_reprBy]

lemma hasFlatBaseChange_of_iso_reprBy {B Y} (e : algFunctor ⋙ reprBy B ≅ Y) : FP (freeAb Y) :=
  (FP.isClosedClass.iff_of_isIso (freeAb.map e.1)).1 (isAffinelyCovered_reprBy B).hasFlatBaseChange
