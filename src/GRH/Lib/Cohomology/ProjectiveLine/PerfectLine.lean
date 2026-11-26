import GRH.Lib.PadicComparison.Descent.AlmostAcyclic
import GRH.Lib.PadicComparison.HodgeTate.HodgeTatePairs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Kummer sequence, Chern class of O(1), projective line formula (tilted O/p coefficients)
(known result; see Lib.Cohomology.ProjectiveLine.NormalizationPullback).

This file: Perfected projective line from two perfect discs: tilted cohomology relative to infinity
vanishes. -/

noncomputable section

open AddMonoidAlgebra CategoryTheory Comparison CommAlgCat Function H LinearEquiv NNRat
  TensorProduct PadicTest CategoryTheory.Functor MonoidalCategory

set_option backward.isDefEq.respectTransparency false

instance {C} [Category C] {F A : AbFunctor C} [HasFlatValues F] [HasFlatValues A] :
  HasFlatValues (abTensor F A) := have := @HasFlatValues.flat; ⟨fun _ ↦ .instTensorProduct⟩

variable {p} [ThePrime p] (S : Type) [AddCommMonoid S] (χ : Multiplicative ℚ →* OFlat) (g : ℚ≥0 →+
  ℚ) (a : ULift.{1} Bool) (B : ULift.{1} Bool → CommAlg OFlat) (ψ :
  _ ⥤ CommAlg OFlat := 𝟭 _) {b b' : CommAlg OFlat}

/-- For an additive commutative monoid S, the monoid algebra O^♭[S], as a commutative
O^♭-algebra. -/
abbrev monoidAlg := CommAlgCat.of OFlat OFlat[S]

/-- For a character χ of ℚ with values in O^♭ and an additive map f: S → ℚ, the O^♭-algebra
endomorphism T^s ↦ χ(f(s)) T^s of O^♭[S]. -/
def charTwist {S} [AddCommMonoid S] (f : S →+ ℚ) : monoidAlg S ⟶ monoidAlg S :=
  ofHom ((AddMonoidAlgebra.lift ..)
  ((algebraMap ..).1.comp (χ.comp f.toMultiplicative) * AddMonoidAlgebra.of ..))

/-- For an additive map g: ℚ≥0 → ℚ, the map of monoid algebras O^♭[ℚ≥0] → O^♭[ℚ] over O^♭
sending T^a to T^{g(a)}. -/
abbrev discToTorus : monoidAlg ℚ≥0 ⟶ monoidAlg ℚ := ofHom (mapDomainAlgHom _ _ g)

/-- Evaluation at T = 0: the O^♭-algebra map from O^♭[ℚ_{≥0}] to b sending T^0 to 1 and T^a to 0
for a > 0. -/
abbrev evalZero b : monoidAlg ℚ≥0 ⟶ b := ofHom
    ((AddMonoidAlgebra.lift ..) ⟨⟨(if · = 1 then 1 else 0), ite_eq_left rfl⟩, by aesop⟩)

/-- The O^♭-algebra O^♭[ℚ] (the torus with all roots of its coordinate) if the lifted Boolean a
is true, and O^♭ itself (a point) if it is false. -/
def pointOrTorus := cond a.1 (monoidAlg ℚ) (.of _ OFlat)

/-- For O^♭-algebras B_i indexed by Bool and an endofunctor ψ of O^♭-algebras (default the
identity), the functor S ↦ ⊔_i Hom(ψ(B_i), S^♭) on p-adic tests. -/
abbrev tiltPointsSum := sigma fun a ↦ tilt ⋙ reprBy (ψ (B a))

/-- The functor S ↦ Hom(ψ(O^♭[ℚ≥0]), S^♭) ⊔ Hom(ψ(O^♭[ℚ≥0]), S^♭) on p-adic tests, ψ an
endofunctor of O^♭-algebras; for ψ the identity (default), two perfect discs. -/
abbrev twoDiscs := tiltPointsSum (fun _ ↦ monoidAlg ℚ≥0) ψ

/-- The map ℤ[torus ⊔ pt] → ℤ[`twoDiscs`] sending t to its inverse on line false minus t on line
true, and pt to the origin of the line false. -/
abbrev gluing : freeAb (tiltPointsSum pointOrTorus ψ) ⟶ freeAb (twoDiscs ψ) :=
  freeAb.desc (fun | _, ⟨⟨true⟩, t⟩ => .of ⟨⟨false⟩, ⟨ψ.map (discToTorus (-coeHom)) ≫ t.1⟩⟩ - .of ⟨⟨true⟩,
       ⟨ψ.map (discToTorus coeHom) ≫ t.1⟩⟩ | _, ⟨⟨false⟩, t⟩ => .of ⟨⟨false⟩, ⟨ψ.map (evalZero _) ≫ t.1⟩⟩) (by bound)

@[simp] lemma evalZero_comp g : evalZero b ≫ g = evalZero b' := by aesop

variable (X : PadicTest ⥤ _ := pointFunctor _) {B : ULift.{1} Bool → CommAlg OFlat} (Δ : ∀ b,
  B b ⟶ B b)

/-- For a set-valued functor X on p-adic tests, the morphism ℤ[X] → ℤ[V], V =
`twoDiscs`, sending every point to the origin T = 0 of the disc with index a. -/
abbrev origin : freeAb X ⟶ freeAb twoDiscs :=
  freeAb.desc (fun _ _ ↦ .of ⟨a, ⟨evalZero _⟩⟩) (by intros; congr; simp)

/-- The map ℤ[Hom(B_true, S^♭) ⊔ Hom(B_false, S^♭)] → ℤ[Hom(B_true, S^♭)] that keeps the points
of the first part and sends those of the second to 0. -/
abbrev projFirst : freeAb (tiltPointsSum B) ⟶ freeAb (tilt ⋙ reprBy (B ⟨true⟩)) := freeAb.desc
    (fun | _, ⟨⟨true⟩, t⟩ => .of t | _, ⟨⟨false⟩, _⟩ => 0) (by bound)

/-- For endomorphisms Δ_b of the O^♭-algebras B_b, the endomorphism 1 − Δ of the functor S ↦
ℤ[⊔_b Hom(B_b, S^♭)], sending [x] to [x] − [x∘Δ_b]. -/
abbrev oneSub : freeAb (tiltPointsSum B) ⟶ freeAb (tiltPointsSum B) :=
  freeAb.desc (fun _ x ↦ .of x - .of ⟨_, ⟨Δ _ ≫ x.2.1⟩⟩) (by bound)

@[simp] lemma charTwist_comp_evalZero : charTwist χ g ≫ evalZero b =
  evalZero b := by ext; simp_all [charTwist]

@[reassoc] lemma charTwist_comp_discToTorus : charTwist χ g ≫ discToTorus g =
  discToTorus g ≫ charTwist χ (.id _) := by ext; simp [charTwist]

lemma oneSub_comp_gluing : oneSub (fun ⟨b⟩ ↦ b.rec (𝟙 _) (charTwist χ (.id _))) ≫ gluing =
  gluing ≫ oneSub (charTwist χ <| cond ·.1 coeHom (-coeHom)) :=
  freeAb.hom_ext (by rintro _ ⟨⟨⟨⟩⟩⟩ <;> simp [charTwist_comp_discToTorus_assoc]; abel)

instance : Mono gluing := have I : Epi (discToTorus coeHom) := ⟨fun x y h ↦ hom_ext (algHom_ext'
         (MonoidHom.ext fun s ↦ mabs_mem_iff (H := MonoidHom.eqLocus ..).1
         (by simpa [mabs] using! congr($h (single s.nnabs 1)))) (by ext))⟩
  (NatTrans.mono_iff_mono_app _).2 fun c ↦ SplitMono.mono ⟨AddCommGrpCat.ofHom
         (FreeAbelianGroup.lift fun ⟨⟨b⟩, ⟨t⟩⟩ ↦
    .of ⟨⟨false⟩, ⟨_root_.structureMap⟩⟩ - cond b (Function.extend (discToTorus coeHom ≫ ·)
    (.of ⟨⟨true⟩, ⟨·⟩⟩) 0 t) 0), by dsimp [freeAb, AddCommGrpCat.free]; ext ⟨⟨⟨⟩⟩⟩ <;>
    simp [freeAb.desc, freeAb, Injective.extend_apply I.1] <;> rcongr⟩

/-- Let N be an O^♭-module with B ↦ B ⊗ N satisfying `IsAcyclicOnPerfect`, and c a p-adic test. Then
source and target of `gluing`, base-changed to c^♭, satisfy `FP`, and
the map is bijective on all Ext^n(−, S ↦ S^♭ ⊗ N). -/
lemma isCohomEquiv_gluing_tilt {N} c : let G := moduleCoeff (tensorCoeff
    N); let ψ := tensorLeft (tilt c); IsAcyclicOnPerfect G → FP (freeAb (twoDiscs ψ)) ∧
      FP (freeAb (tiltPointsSum pointOrTorus ψ)) ∧ IsCohomEquiv (tilt ⋙ G) (gluing ψ) := by
  intro G ψ ac
  let L := asModules (𝟭 (CommAlg OFlat))
  let U := tensorWith (S := OFlat) _ (tilt c) ⋙ moduleCoeff (tensorRight N)
  let D {X} B (f : ∀ b, X ⟶ L (B b)) x : freeAb (tiltPointsSum B ψ) ⟶ _ ⋙ G :=
    freeAb.desc (fun _ t ↦ G.map t.2.1 (U.map (f _) x)) (by solve_by_elim [G.map_comp_apply])
  have κ {X} B (h : ∀ b, _) f (e : Bijective fun x ↦ (f ⟨false⟩ x, f ⟨true⟩ x)) :
      Bijective (Abelian.Ext.mk₀ ∘ @D X B f) ∧ _ ∧ FP (freeAb (tiltPointsSum B ψ)) :=
    have u b : PerfectRing (ψ (B b)) p :=
      perfectRing_tensor p_eq_zero_of_algebra_oFlat ⟨_, c.isPerfectTorsionFree_tilt.1⟩ ⟨_, h b⟩
    have ⟨a, _⟩ := forall_and.1 (isBijective_reprBy_iff.1 <| @ac _ <| u ·)
    have := e.map_prod (U ⋙ forget _)
    ⟨(bijective_iff_of_comm_sq (fun _ ↦ by ext; simpa [H.map] using congrArg _ freeAb.hom_ext)
      (.comp (f := fun x b ↦ U.map (f b) x) (.piMap a) (by simp_all [bijective_iff_existsUnique,
      funext_iff])) (sigma_bijective ..)).2 (.piMap fun _ ↦ Abelian.Ext.mk₀_bijective ..), (· + 1 |>
      sigma_bijective (fun a ↦ tilt ⋙ reprBy (ψ (B a))) (tilt ⋙ G) |>.1.subsingleton), by
    (repeat intro); exact (bijective_iff_of_comm_sq (by induction · <;> simp_all [mapₗ, map_push,
      funext_iff]) ((ofBijective (.pi fun _ ↦ mapₗ ..) (sigma_bijective ..)).lTensor _ ≪≫ₗ piRight
      ..).bijective (sigma_bijective ..)).2 (.piMap fun x ↦
      hasFlatBaseChange_of_iso_reprBy homTiltIso.symm ..)⟩
  let π b := ModuleCat.ofHom (cond b (.snd ..) (.fst ..) : _ →ₗ[OFlat] monoidAlg ℚ≥0)
  obtain ⟨⟨k, _, f⟩, l, _, f'⟩ := κ (fun _ ↦ monoidAlg ℚ≥0) (by simp [perfectRing_monoidAlgebra])
    (π ·.1) bijective_id, κ pointOrTorus (by simp [pointOrTorus, Bool.cond_true, Bool.cond_false,
    perfectRing_monoidAlgebra, instPerfectRingOFlat])
      (fun ⟨b⟩ ↦ b.rec (π false ≫ L.map (evalZero _))
    (π false ≫ L.map (discToTorus (-coeHom)) - π true ≫ L.map (discToTorus coeHom))) (by
    refine (ofLinearMap (.prod _ _) (.coprod (Algebra.linearMap ..) (Finsupp.linearCombination _
    (fun t ↦ if 0 ≤ t then (0, -single t.toNNRat 1) else (single (-t).toNNRat 1, 0)) ∘ₗ
    (coeffLinearEquiv _).1)) ?_ ?_ :
      _ ≃ₗ[_] _).bijective <;> dsimp +zetaDelta [pointOrTorus, Bool.cond_true, Bool.cond_false] <;>
          ext : 3 <;>
    simp <;> split <;> simp_all [le_of_lt, Rat.coe_toNNRat, ← one_def, ← single_neg, Prod.ext_iff])
  use f, f', Nat.rec ((k.of_comp_iff _).1 ?_) (by simp [bijective_iff_existsUnique, nontriviality])
  convert l; ext; simp [H.map]; congr; exact freeAb.hom_ext
    (by rintro _ ⟨⟨⟨⟩⟩⟩ <;> simp [D, -comp_obj] <;> rfl)

/-- For every p-adic test c, the map ℤ[h_c]⊗ℤ[V'] → ℤ[h_c]⊗ℤ[V] induced by `gluing`
induces bijections on all Ext^n with coefficients `genericCoeff`, the functor R ↦ ℂ_p
⊗_{O_C} R^. -/
lemma isCohomEquiv_gluing_generic c : IsCohomEquiv genericCoeff (gluing (tensorLeft (tilt c))) :=
  have := IsLocalization.flat ℂ_[p] (.powers (p : OC))
  (isCohomEquiv_gluing_tilt c (isAcyclicAt_almostCoeff isPeriodRingPair_OC.pFlat_smul_eq_zero)).elim
    fun f ⟨g, e⟩ ↦
    ((coeffCompBij_id_iff_restrict (by exact exists_periodAlg_iso_genericAlg.choose)).1
    (.periodAlg_of_almostCoeff f isPeriodRingPair_OC (by clear f; tauto) isPerfectTorsionFree_tilt
    isPerfectTorsionFree_tilt ((coeffCompBij_id_iff_restrict (.refl _)).2 e.bij))).eqv

/-- If ℤ[h_c]⊗i induces bijections on all Ext^n(−, F) for every p-adic test c (i =
`gluing`), then Ext^n(S⊗coker i, F) = 0 for every flat S and every n. -/
lemma subsingleton_coker_gluing {F} (h : ∀ c, IsCohomEquiv F (gluing (tensorLeft (tilt c)))) S
  [HasFlatValues S] : ∀ n, Subsingleton (H (abTensor S (Limits.cokernel gluing)) F n) :=
  (isCohomEquiv_iff_subsingleton (.map ⟨ShortComplex.exact_cokernel _⟩ _)).1 (IsBijective.eqv
  (((Comparison.id F).devissage (abTensor.flip _) (abTensor.flip.map _)).bijective_of_sigma_repr
  (fun ι c n ↦ let u B : sigma (tiltPointsSum B <| tensorLeft <| tilt <| c ·) ⟶ sigma (reprBy <|
    c ·) ⊗ tiltPointsSum B := ⟨fun _ ↦ ↾fun
  x ↦ (⟨_, ⟨preimage _ (tensorInl ≫ x.2.2.1)⟩⟩, ⟨_, ⟨tensorInr ≫ x.2.2.1⟩⟩),
    by intros; ext; simp; erw [← Category.assoc, preimage_comp, preimage_map]; rfl⟩
  have b B := (sigma_bijective ..).comp (((IsCohomEquiv.of_bijective (p := u B) fun _ ↦
    Equiv.bijective ⟨_, fun (⟨_, ⟨f⟩⟩, ⟨_, ⟨t⟩⟩) ↦ ⟨_, _, ⟨ofHom (Algebra.TensorProduct.productMap
      (tilt.map f).hom t.hom)⟩⟩, fun _ ↦ by simp; congr; aesop,
      fun ⟨⟨_, ⟨_⟩⟩, _, ⟨_⟩⟩ ↦ by simp [← ofHom_comp]⟩).comp_iff.2 (.of_isIso (freeAb.prod ..))) n)
  (bijective_iff_of_comm_sq (fun _ ↦ by ext; simp [← H.map_comp]; congr 2; exact freeAb.hom_ext (by
    rintro _ ⟨⟨⟨⟩⟩⟩ <;> show _ = _ ⊗ₜ _ <;> simp [u, sigma.ι, tmul_sub,
    ← Category.assoc, ← ofHom_comp, (· ◁ ·)] <;> rfl)) (b _) (b _)).2 (.piMap fun _ ↦ h ..)) S))
