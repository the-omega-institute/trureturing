import GRH.Lib.PadicComparison.Primitive.TiltedTheory
import GRH.Lib.Cohomology.ProjectiveLine.PerfectLine
import GRH.Lib.PadicComparison.Duality.IntegrationOverLine
import GRH.Lib.Cohomology.Kunneth.LerayHirschBasis
import GRH.Lib.Cohomology.PointClass.LocusEquations
import GRH.Lib.Cohomology.PointClass.HomogeneousCoords
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: The Kummer sequence, the Chern class of O(1) and the projective line formula
(tilted O/p coefficients). Here the formula H(P¹×S) = H(S) ⊕ H(S)·η is given in Leray–Hirsch form
for a coefficient theory on test rings. For tilted O/p coefficients it comes from the perfected
projective line, glued from two perfect discs. Source: SGA 4½; SGA 5 VII (Jouanolou); Milne, Étale
Cohomology VI.10; Scholze, p-adic Hodge theory for rigid-analytic varieties.

Comparison of cohomology theories by duality, using a diagonal kernel on products of P¹. For torsion
coefficient theories in which the projective line is computed, a class supported on the diagonal of
(P¹)^d carries finiteness and comparison from the point to standard étale charts over affine space.
Source: for the known theorems, SGA 4, SGA 4½ Finitude/Dualité; Faltings, Scholze primitive
comparison; the route is in the spirit of Dold–Puppe dualisability.

Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles (known
result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Projective line formula for tilted O/p coefficients via a left inverse of cup with η.
Projective line formula for mod-l cohomology over bases mapping to fields or C_p. Loci keeping
coincidences among finitely many maps to a proper functor form a cover. Comparison property for
opens of affine space in (P¹)^d and standard étale charts. Pull-back along a finite linear
projection to projective space is injective (transfer). -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

noncomputable section

section

open AddMonoidAlgebra CategoryTheory projLine TotalH TensorProduct Limits ShortComplex

set_option backward.isDefEq.respectTransparency false

attribute [-simp] Bool.cond_eq_ite

attribute [local simp] Bool.cond_true Bool.cond_false

/-- Take two exact triangles of additive groups through I: W → I → B → W (maps b, c, a) and K →
I → P → K (maps f, d, e). If d∘b is bijective, so is c∘f. -/
lemma TotalH.bijective_of_two_triangles {K P I W B a e} [AddGroup K] [AddGroup P] [AddGroup I]
  [AddGroup W] [AddGroup B] {b : W →+ I} {c : I →+ B} {d : I →+ P} {f : K →+ I} (h : Function.Exact
  a b ∧ Function.Exact b c ∧ Function.Exact c a) (k : Function.Exact d e ∧ Function.Exact e f ∧
  Function.Exact f d) (t : Function.Bijective (d.comp b)) : Function.Bijective (c.comp f) := by
  simp [Function.Exact, ↓injective_iff_map_eq_zero, Function.Bijective, t.2.of_comp (f := d) _] at *
  use by grind, (h.2.2 · |>.1 (t.1 _ (by grind)) |>.rec
    fun r ↦ (t.2 (d r)).rec fun w ↦ by grind [k.2.2 (r - b w), sub_self, sub_zero])

variable {C} [Category C] {W' W Z₀ : AbFunctor C} {S T : ShortComplex (AbFunctor C)}

/-- Let i be injective, iδ' = δi, δz = 0, with f, α, α₁, κ compatible with S, T, and η ∈
Ext²(S₃, T₁) the product of their classes along n. There are j: B → S₃, y: Z₀ → K, ω ∈
Ext(B, K) such that sj lifts along r whenever gi = gδ = 0 and rg is f followed by S₂ → S₃
and s; and, after any exact Φ with Φ(coker i) acyclic for F, s ↦ ωs is onto and j^*(ηm) = ωs
implies (κz)^*m = y^*s. -/
lemma toda_squares {i : W' ⟶ W} [Mono i] {δ' δ} (w : δ' ≫ i = i ≫ δ) (z : _ ⟶ W) (o : z ≫ δ = 0)
  (k₁ : S.ShortExact) (k₂ : T.ShortExact) f α κ n α₁ (e₁ : α₁ ≫ S.f = i ≫ f) (e₂ : δ ≫ f = 0) (e₃ :
  δ' ≫ α = i ≫ κ ≫ T.f) (n₁ : α₁ ≫ n = α ≫ T.g) : ∃ B K, ∃ (j : B ⟶ S.X₃) (y : Z₀ ⟶ K), ∃ ω,
  (∀ Q R g (r : Q ⟶ R) s, i ≫ g = 0 → δ ≫ g = 0 → g ≫ r = f ≫ S.g ≫ s → ∃ t, t ≫ r = j ≫ s) ∧ ∀ E
  [Category E] (Φ : _ ⥤ AbFunctor E) [IsExactFunctor Φ] F, (∀ n, Subsingleton (H (Φ (cokernel i)) F
  n)) → (∀ N (τ : N ⟶ _) m s, comp (F := F) (.homClass (Φ.map j)) (comp (.map Φ (k₁.extClass.comp
  (H.map _ n 1 k₂.extClass) rfl).toTotalH) m) = comp (.map Φ ω) s → comp (.homClass (τ ≫ Φ.map (z ≫
  κ))) m = comp (.homClass (τ ≫ Φ.map y)) s) ∧ Function.Surjective (comp (F := F) (.map Φ ω)) := by
  let D := pushout.desc i δ w
  obtain ⟨c₁, c₂, _⟩ := ShortExact.mk (exact_cokernel (Abelian.factorThruCoimage D)),
    ShortExact.mk (exact_cokernel (kernel.ι D)), k₁.2, k₂.2
  have s : CommSq (pushout.desc α₁ 0 (by simp [← cancel_mono S.f, reassoc_of% w, *]))
    (cokernel.π _) S.f (Abelian.factorThruCoimage D ≫ f) := ⟨by ext1 <;> simp [D, *]⟩
  have q : pushout.desc α _ e₃ ≫ T.g = cokernel.π _ ≫ s.lift ≫ n := by ext1 <;> simp [*]
  have ⟨u, h⟩ := k₂.1.lift' (kernel.ι D ≫ pushout.desc α _ e₃) (by simp [*, -CommSq.fac_left_assoc])
  refine ⟨_, _, cokernel.desc _ (f ≫ S.g) (by simp [← reassoc_of% s.fac_right]), kernel.lift D
    (z ≫ pushout.inr ..) (by simpa [D]), comp c₁.extClass.toTotalH c₂.extClass.toTotalH, by
      intros; use cokernel.desc _ ‹_› ?_ <;> simp [coequalizer.hom_ext_iff, pushout.hom_ext_iff, D,
      *], fun _ _ Φ _ F e ↦ (?_ : Function.Bijective _).imp_left fun b _ τ m _ a ↦ by
    simp [← b ((comp_assoc_of_sq (y := TotalH.homClass (Φ.map u))
      (by simp [← map_homClass, H.map, c₂.extClass_naturality k₂ ⟨_, _, _, h, q⟩, ← TotalH.map_comp,
      ← Abelian.Ext.comp_assoc (h₁₂ := zero_add 1), ← c₁.extClass_naturality k₁ ⟨_, f, _,
      s.fac_right, (cokernel.π_desc ..).symm⟩, -map_of, comp_of]) m).trans a),
      homClass_comp_homClass_comp, ← Functor.map_comp]; congr 5; simp [← cancel_mono T.f, *]⟩
  simpa [funext (map_comp_assoc _)] using! bijective_of_two_triangles (exact_triangle (c₁.map Φ) F)
    (exact_triangle (c₂.map Φ) _) ((funext (homClass_comp_homClass_comp
    _)).symm.subst (((isCohomEquiv_iff_subsingleton (.map ⟨exact_cokernel _⟩ Φ)).2
    (IsCohomEquiv.of_isIso (Φ.map (inv _ (I := isIso_cokernel_map_of_isPushout (.flip
    (.of_hasPushout ..))))) · |>.2.subsingleton)).comp_iff.1 (by simpa [← Φ.map_comp, D] using
    (isCohomEquiv_iff_subsingleton (.map ⟨exact_cokernel i⟩ Φ)).2 e)).bijective_totalH)

variable {ℓ A} [CommRing A] [InvertsPrime A ℓ] {g : C ⥤ TestOver A} (M : TorsionCoeff g) (Θ :
  Theory g) {S : AbFunctor C} [HasFlatValues S]

lemma TorsionCoeff.sliceEquiv_mulClass (v : TotalH S _) : sliceEquiv
  (M.mulClass (etaClass g).toTotalH v) = comp (.map (restrictAlong _) v) M.cupClass.toTotalH := by
  erw [← M.onElements.mulClass_eq_comp_etaAt (S := _ ⋙ S) _ _ rfl, ← comp_id (x := TotalH.map _ v),
    ← map_restrictAlong_etaClass (elementsProj _), ← M.mulClass_naturality, comp_id]; rfl

/-- Let S be flat and x a class on S ⊗ ℤ[P¹] with coefficients in the theory Θ whose pull-back
along the base point (1:1) vanishes. Then (q^*x)·η_r = (r^*x)·η_q for all sections q, r of
P¹, η_r the pull-back of `etaClass` along r. -/
lemma etaAt_swap x : let t q : S ⟶ abTensor S _ := tensorPoint (freeAbSectionMap q) S
  let o q r := comp (pullbackAlong (t q) x) (Θ.etaAt (freeAbSectionMap r)).toTotalH
  pullbackAlong (t (basePt g)) x = 0 → ∀ q r, o q r = o r q := by
  intro t o k
  have D q r := (exists_etaClass_supported_diagonal ..).elim fun J ⟨z, ξ, e⟩ ↦ have c a :=
      (Θ.mulClass_congr_of_eq_on_zeros J ξ (a := t a) (a' := t r) · x ▸ Θ.mulClass_eq_comp_etaAt _ _
      e _); c q (by ext; exact congr(_ ⊗ₜ .of $(z · ·))) ▸ c r (by simp)
  simpa [by simpa [k, Θ.comp_etaAt_basePt] using (D · (basePt _))] using D

/-- Let S be flat. Suppose v ↦ v·η (`TorsionCoeff.mulClass`) is injective on total Ext(S, Θ), and
its image contains every x for which, over the points of P¹, (`sliceEquiv` x)·η is x
followed by `TorsionCoeff.cupClass`. Then the projective line formula holds at S. -/
lemma line_formula_of_mulClass_injective (i : Function.Injective (Θ.mulClass (S :=
  S) (etaClass g).toTotalH)) (s : ∀ x, Θ.onElements.mulClass (S := _ ⋙
  S) (etaClass _).toTotalH (sliceEquiv x) = comp (.map (restrictAlong _) x) Θ.cupClass.toTotalH →
  x ∈ (Θ.mulClass (etaClass g).toTotalH).range) : IsLerayHirschBasis Θ.lineBasis
  S := have a S (x : TotalH S Θ.F) := (x.map_map (restrictAlong (elementsProj (projLineAlong g)))
    (restrictAlong (sectionLift (𝟭 C) (basePt g)))).trans x.map_id
  (Comparison.bijective_iff_of_comm_sq
    (fun _ ↦ by simp [lerayHirsch, Finsupp.sum_fintype, mapThenComp, TorsionCoeff.lineBasis,
    Θ.sliceEquiv_mulClass, Function.Exact.splitSurjectiveEquiv]; abel!)
    (Finsupp.equivFunOnFinite.trans (.boolArrowEquivProd _)).symm.bijective sliceEquiv.bijective).1
    (Function.Exact.splitSurjectiveEquiv (f := (Θ.mulClass _).toIntLinearMap) (g :=
    (comp _).toIntLinearMap) (.of_comp_of_mem_range (funext (Θ.comp_etaAt_basePt · ▸
    Θ.mulClass_eq_comp_etaAt _ _ rfl _)) fun x e ↦ s x (sliceEquiv.injective (by
    erw [TorsionCoeff.sliceEquiv_mulClass, map_homClass_comp]
    exact .trans (etaAt_swap Θ.onElements.onElements (S := _ ⋙ _) _ (by
      simpa -dsimp [map_homClass_comp] using! congr(TotalH.map (restrictAlong _)
        (.map (restrictAlong _) $e))) ⟨_, (·.1.2)⟩ _) ((comp_assoc ..).trans
      (congrArg _ (by erw [TotalH.map_comp, Θ.onElements.map_etaAt_onElements]; rfl)))))) i
    ⟨(sliceEquiv.symm.toAddMonoidHom.comp (TotalH.map (restrictAlong _))).toIntLinearMap,
    LinearMap.ext fun x ↦ ((map_homClass_comp.trans (a .. ▸ rfl)).congr (a _ x)).1
    (congrArg _ (sliceEquiv.right_inv _))⟩).1.symm.bijective

/-- Projective line formula H(P¹ × N) = H(N) ⊕ ηH(N), for all N, in the theory `tiltTheory`
of ℓ-adic tests S with coefficients S^♭ ⊗ M; here A maps to ℂ_ℓ, and M is an O^♭-module
satisfying the acyclicity hypothesis of that theory.

Known result: Kummer sequence, Chern class of O(1), projective line formula (tilted O/p
coefficients). -/
lemma hasLineFormula_tiltTheory M [Algebra A ℂ_[ℓ]] ac : (tiltTheory A M ac).HasLineFormula := by
  have := (@cyclotomicRootSystem _ A).2
  have ⟨χ, hχ⟩ := exists_tilt_lift_of_character ((algebraMap A _).1.comp
    ((Units.coeHom _).comp cyclotomicRootSystem.1)) (by aesop)
  choose ε h using @exists_unit_smul_unimodularRow
  let F c x : (cocycle (genericTestOver A)).extension.X₂ c := (⟨ε x⟩, .of ⟨⟦x⟧⟩)
  have hF c d f x : (cocycle _).extension.X₂.map f (F c x) = F d _ :=
    Prod.ext (add_rowUnit_eq _ _ (.trans (by simp -dsimp [← h]) (h _))) rfl
  let ρ c : PadicTest.tilt c →*₀ c.GenericRing :=
    .comp (.ofClass (algebraMap ..)) (Perfection.teichmuller₀ ..)
  have n c d f x : (ringOf (genericTestOver A)).map f (ρ c x) = ρ d _ :=
    untilt_tiltMap f.1 x ▸ c.mapGeneric_algebraMap ..
  have G c (s : OFlat) : ρ c (algebraMap _ _ s) = _ :=
    (untilt_tiltMap c.structureMap s ▸ c.structMap_coe _).symm
  let Θ := tiltTheory A M ac
  have l := @subsingleton_coker_gluing _ _ Θ.F (isCohomEquiv_gluing_tilt · ac |>.2.2)
  obtain ⟨_, _, j, y, _, -, t⟩ := by
    refine toda_squares (oneSub_comp_gluing χ) (origin ⟨true⟩) (freeAb.hom_ext (by simp -dsimp))
      (cocycle _).shortExact_extension (shortExact_kummerSeq (genericTestOver A)) (freeAb.desc
      (fun c y ↦ F c (0, 0) - F _ (cond y.1.1 (· - 1, 1) (0, ·) (ρ c (y.2.1.hom (single 1 1)))))
      fun _ _ ↦ ?_) (projFirst ≫ freeAb.desc (fun _ t ↦ .comp (.mk' .up (by tauto))
      ((ρ _).toMonoidHom.comp (t.1.hom.1.1.comp (of ..))).toHomUnits.toAdditiveRight) fun _ _ _ _ ↦
      AddMonoidHom.ext fun _ ↦ Gm.ext.2 (n ..).symm) (projFirst ≫ freeAb.map (toUnit _) ≫ tateGen _)
      _ _ ?_ ?_ ?_ (Category.comp_id _) <;>
      (try apply freeAb.hom_ext) <;> rintro c ⟨⟨⟨⟩⟩, y⟩ <;> simp [*, charTwist, ← neg_eq_iff_eq_neg,
      -coe_algebraMap, -Functor.comp_map, -Functor.comp_obj] <;> try rfl
    exacts [eq_sub_of_add_eq (Prod.ext_iff.2 (.imp ULift.ext_iff.2 ((zero_add _).trans ∘ congrArg
      FreeAbelianGroup.of) (smul_unimodularRow_inj (by erw [mul_smul, ← h, ← h]; simpa using ⟨rfl,
      Units.mul_inv _⟩)))), sub_eq_of_eq_add (AddMonoidHom.ext fun _ ↦ Gm.ext.2 (congr(ρ c (y.1.hom
      $(lift_of ..))).trans
      (by erw [map_mul, map_mul, AlgHom.commutes, G, hχ, freeAb.desc_of]; rfl)))]
  erw [H.map_id, ← etaClass] at t
  refine lerayHirsch_bijective_of_repr fun c ↦ line_formula_of_mulClass_injective Θ (.of_ker _ fun v
    a ↦ ((Θ.tateGen_comp_tateAction v).congr (map_zero _)).1 ((t _ _ _ (l _)).1 _ (tensorPoint (𝟙 _)
    _) _ 0 (a ▸ by simp))) fun x a ↦ ((t _ _ _ (l _)).2 (pullbackAlong ((abTensor _).map j) x)).imp'
    (pullbackAlong (tensorPoint y _)) fun w b ↦ sliceEquiv.injective ?_
  erw [Θ.sliceEquiv_mulClass, map_homClass_comp, comp_assoc, ← (t _ (restrictAlong _ ⋙ _) ..).1 _
    (tensorPoint (𝟙 _) _), Θ.onElements.tateGen_comp_tateAction]
  erw [← TotalH.map_map, map_restrictAlong_etaClass, a]
  simpa -dsimp [map_comp_assoc,
    TotalH.map_map] using! congr(comp (.map (restrictAlong _) $b) _).symm
  exact fun _ ↦ ((IsCohomEquiv.of_isIso (NatIso.ofComponents (F := abTensor (abTensor _ (freeAb _))
    _) (fun _ ↦ (rightComm ℤ ..).toAddCommGrpIso) fun _ ↦ addCommGrp_tensor_hom_ext (·.inductionOn
    (by tauto) (by simp_all [add_tmul]))).1).bijective_totalH.1.comp (sliceEquiv (N :=
    abTensor (freeAb _) _).symm.injective.comp (DirectSum.of_injective _))).subsingleton

end

section

open CategoryTheory CommAlgCat Finsupp Ideal TotalH MonoidalCategory

section

seal locConstCoeff projLine

set_option backward.isDefEq.respectTransparency false

variable {C} [Category C] {ℓ A} [CommRing A] [InvertsPrime A ℓ] {g : C ⥤ TestOver A}
  {M : TorsionCoeff g}

/-- Let θ be a family of self-extension classes of the coefficient of Θ over the points of P¹,
one of them `TorsionCoeff.cupClass`. If `lerayHirsch` for θ is bijective at ℤ[pt] and at
ℤ[P¹], the projective line formula holds at ℤ[pt]. -/
lemma line_formula_of_basis (Θ : Theory g) {I} {d : I → ℕ} (θ : ∀ i, H (restrictAlong _ Θ.F) _ (d
  i)) i (hi : (θ i).toTotalH = Θ.cupClass.toTotalH) (h : IsLerayHirschBasis θ (freeAb (pointFunctor
  _))) (h' : IsLerayHirschBasis θ (freeAb (projLineAlong g))) : IsLerayHirschBasis Θ.lineBasis
  (freeAb (pointFunctor _)) := line_formula_of_mulClass_injective Θ (fun v w k ↦ single_injective i
  (h.1 (by simp_all only [lerayHirsch_single, ← Θ.sliceEquiv_mulClass]))) fun x k ↦
  (h.2 _).imp' (· i) fun w e ↦ (Finsupp.ext_iff.1 (((isClosedClass_lerayHirsch.iff_of_isIso
  (freeAb.map (λ_ _).inv ≫ freeAb.prod (pointFunctor _) _)).1 h').1 ((lerayHirsch_naturality θ _
  (fun _ _ ↦ Θ.mulClass_naturality ..) w).trans (by rwa [lerayHirsch_single,
  map_restrictAlong_etaClass, e, hi]))) i).trans (by simp)

/-- For a test c over A, the class η·1 in H² with locally constant ℤ/ℓ coefficients, pulled back
to the functor (B, x ∈ P¹(B)) ↦ Hom(c, B). -/
def etaOneClass c := H.map _ (freeAb.map (toUnit (testOfPoint A _ ⋙ reprBy c))) 2
  (.map _ oneLocConst 2 Theory.locallyConstant.cupClass)

lemma pull_etaOneClass {T c} (u : pointFunctor C ⟶ g ⋙ reprBy c) :
  comp ((Comparison.restrict (Functor.Elements.precomp g _) _).pull
  (freeAbMap ((elementsProj _).whiskerLeft u)) 2 (etaOneClass c)).toTotalH T =
  pullbackAlong (oneLocConst (g := elementsProj _ ⋙ g)) (comp T M.cupClass.toTotalH) := by
  simp [etaOneClass, Comparison.pull, H.map, H.push]
  erw [Abelian.Ext.toTotalH, ← homClass_comp_of, ← map_of, comp_assoc,
    Theory.locallyConstant.onElements.etaAt_naturality]
  exact congr(pullbackAlong $freeAb.hom_ext _)

variable (A) (k : Type) [Field k] [Algebra A k]

/-- For an A-algebra k that is a field, the restriction of scalars functor from test k-algebras to
test A-algebras. -/
def TestOver.resScalars : TestOver k ⥤ TestOver A :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ restrictAlg ..) (·.2)

/-- On test k-algebras B, the map from the point to the functor B ↦ Hom_A(k, B) that picks the
structure map k → B. -/
def TestOver.structurePt [IsAlgClosed k] :
  pointFunctor _ ⟶ resScalars A k ⋙ reprBy ⟨of A k, isTest_of_preValuationRing⟩ := sectionMap
  ⟨fun B ↦ ⟨⟨CommAlg.homOfRingHom _ (by tauto)⟩⟩, (congr(⟨⟨$(by ext; apply ·.1.1.2)⟩⟩))⟩

lemma hasUnivPoints_structurePt [IsAlgClosed k] : (Comparison.restrict (TestOver.resScalars A k)
  Theory.locallyConstant.F).HasUnivPoints (TestOver.structurePt A k) := fun B y ↦ ⟨⟨@of k _ _ _
  y.1.1.1.1.toAlgebra, B.2⟩, ⟨⟩, ⟨CommAlg.homOfRingHom _ (y.1.1.1.2 · |>.symm)⟩, rfl, fun _ _ f e ↦
  ⟨⟨CommAlg.homOfRingHom _ (congr($e.1.1.1 ·).symm)⟩, by bound⟩,
  ConcreteCategory.bijective_of_isIso ((locConstCoeff _).map (𝟙 _))⟩

/-- The absolutely integrally closed valuation ring A, viewed as a test over itself. -/
abbrev TestOver.ofSelf (A) [CommRing A] [IsAICLocal A] [PreValuationRing A] : TestOver A :=
  ⟨of A A, isTest_of_preValuationRing⟩

lemma pointMap_ofSelf_bijective {A} [CommRing A] [IsAICLocal A] [PreValuationRing A] :
  AllBijective (@pointMap _ _ (pointFunctor _) (TestOver.ofSelf A) ⟨⟩
  ·) := fun _ ↦ ⟨fun _ _ _ ↦ congr(⟨⟨$(by ext)⟩⟩), (⟨⟨⟨structureMap⟩⟩, .refl ·⟩)⟩

variable [PreValuationRing A]

/-- Let A be a valuation ring whose non-zero elements are units in all g(d), and M a coefficient
along g with multiplication by η non-zero on the cohomology of the point. Then the
projective line formula holds for locally constant ℤ/ℓ-valued functions on tests over A. -/
lemma hasLineFormula_of_cupClass_ne_zero (hg : ∀ d, ∀ a ≠ 0, IsUnit (algebraMap A (g d).1 a)) (M :
  TorsionCoeff g) (ne : ¬∀ y, lerayHirsch M.lineBasis (freeAb (pointFunctor C)) (.single false
  y) = 0) : Theory.locallyConstant (A := A).HasLineFormula := lerayHirsch_bijective_of_repr fun _ ↦
  lerayHirsch_bijective_of_fields isDetectedAtPoints_projLine fun ⟨k, o⟩ _ hc ↦ let := hc.toField
  have := o.isAlgClosed
  have := InvertsPrime.mk (map_natCast (algebraMap A k) ℓ ▸ InvertsPrime.isUnit_prime.map _)
  have z c : (@IdealFamily.ofMaximalIdeal k _ _).I c = ⊥ := by simp [IdealFamily.ofMaximalIdeal,
    IsLocalRing.maximalIdeal_eq_bot]
  let Θ : Theory (TestOver.resScalars A k ⋙ 𝟭 _) := {Theory.locallyConstant with}
  (exists_lerayHirsch_basis Theory.locallyConstant.1.onElements isDetectedAtPoints_projLine
    .of_top_le ⟨2, Θ.cupClass⟩).elim fun b t ↦
    (TorsionCoeff.HasLineFormula.bijective_iff_of_hasUnivPoints _ (hasUnivPoints_structurePt A k)).2
    (line_formula_of_basis Θ _ ⟨_, t.1 fun e ↦ ne (M.comp_oneLocConst_surjective.forall.2 fun T ↦ by
  let l Q {T} h h' : (residueTest (.ofSelf A) Q).right ⟶ T :=
    ⟨ofHom (ResidueField.liftₐ _ structureMap.1 h h')⟩
  have z : etaOneClass _ = 0 := (H.map_map ..).symm.trans (((PrimeSpectrum.le_iff_specializes
    ..).1 bot_le).mem_open (isDetectedAtPoints_projLine.1 _ 2 (etaOneClass _)).1 ((H.map_map
    ..).trans ((isDetectedAtPoints_projLine.2 _ ⟨k, o⟩ (l (.comap _ ⊥) le_rfl fun _ ↦ .mk0 _)
    (Field.toIsField (ResidueField _)) hc 2).1 ((H.map_map ..).trans (((hasUnivPoints_structurePt A
    k).on_elements.isBijective 2).1 (DirectSum.of_injective _ (((comp_id.congr
    (congrArg _ id_comp)).1 (pull_etaOneClass (M := Θ.1) _)).trans (by simpa))))))))
  erw [lerayHirsch_single, map_comp_assoc, map_homClass, ← pull_etaOneClass (sectionMap
    ⟨(⟨l ⊥ bot_le <| hg ·⟩), fun _ ↦ congr(⟨⟨ofHom $(ResidueField.algHom_ext (by ext))⟩⟩)⟩), z]
  simp)⟩ rfl (isClosedClass_lerayHirsch.of_bijective _ pointMap_ofSelf_bijective (t.2 _ (z _)))
    (isClosedClass_lerayHirsch.of_bijective (E := _ ⋙ projLinePow Unit) {app _ := ↾_} (fun _ ↦
    (Equiv.funUnique ..).bijective)
    (bijective_lerayHirsch_iff.2 (isAffinelyCovered_projLinePow.devissage_bijective
    lerayHirsch.devissage (bijective_lerayHirsch_iff.1 <| t.2 · (z _))) :)))

/-- Known result: projective line formula, here for locally constant coefficients. -/
lemma hasLineFormula_locallyConstant [Algebra A ℂ_[ℓ]] [FaithfulSMul A ℂ_[ℓ]] :
  Theory.locallyConstant (A := A).HasLineFormula :=
  have m := isAcyclicAt_almostCoeff (N := _ ⧸ span {pFlat}) (by simp [Algebra.smul_def])
  hasLineFormula_of_cupClass_ne_zero A (fun d _ k ↦ .map d.structMap (by simpa)) (tiltTheory A _
    m).1 fun z ↦ by simpa [Submodule.mem_smul_top_iff, mem_span_singleton_mul, pFlat_ne_zero] using
    (LinearMap.ker_tensorProductMk _).le ((TensorProduct.lid OFlat _).symm.injective
    (ULift.up_injective ((sectionEquiv ..).injective
    ((m _).bijective_totalH.1 ((IsCohomEquiv.of_bijective (p := toUnit (_ ⋙ reprBy _)) fun _ ↦
    ⟨fun _ _ _ ↦ congr(⟨$(isInitialSelf.hom_ext ..)⟩), (⟨⟨structureMap⟩,
    .refl ·⟩)⟩).bijective_totalH.2.forall₂.2 (fun v w ↦ congrArg _ (single_injective _
    ((hasLineFormula_tiltTheory ..).1 (by erw [z, z])))) ..)))) : _ ⊗ₜ ⟨_, not_isUnit_pFlat⟩ = 0)

/-- Let P_i: Y → Z be finitely many maps, Z proper. U ⊂ Y is dense for Λ if it contains each
point x in a test ring for which some geometric point z has P_i(z) = P_j(z) ⇒ P_i(x) =
P_j(x) for all i, j. -/
lemma IsProperOver.isCohomDense_of_coincidences {Λ Y Z D s} (h : @IsProperOver Z D s) {U J}
  [Finite.{1} J] (P : J → (Y ⟶ Z)) (H : ∀ {k} [Field k] [IsAlgClosed k] z B x,
  (P · B.1 x).FactorsThrough (P · ⟨k⟩ z) → x ∈ U B) : IsCohomDense (Y := testIncl.comp Y)
  (locConstCoeff Λ) U := .of_affine_cover (V := fun ε : J → Set J ↦ ⟨({y | ∀ᵉ (i) (j ∈ ε i),
  P i · y = P j _ y}), by simp; grind⟩) (fun ε ↦ isRelAffine_of_zero_unit_locus fun y ↦ by
  choose I h using h.1; use ⋃ (i) (j ∈ ε i), I _ (P i _ y) (P j _ y), ∅
  simp_all; tauto) fun O y ↦ ⟨_, H (Y.map (CommRingCat.ofHom
  O.subtype) y), fun _ _ _ ↦ h.injective_map_valuationSubring O (by aesop)⟩

end

open CartesianMonoidalCategory Finset IsLocalRing projLine Subfunctor relFreeAb

open Polynomial hiding comp

set_option backward.isDefEq.respectTransparency false

variable {Γ} [Category Γ] {ℓ d} {A B R T : Type} [CommRing A] {g : Γ ⥤ TestOver A} [CommRing B]
  [CommRing R] {E Y : TestOver A ⥤ Type 1} {U V : Subfunctor Y} [CommRing T] [Algebra A T]
  (e : MvPolynomial (Fin d) A ≃ₐ[A] T)

/-- For rows r_i = (a_i, b_i), the ideal of B generated by φ(J) and (∏ b_i)·Σ_m φ(Φ_m) ∏
a_i^{m_i} b_i^{deg_i Φ − m_i}, the multihomogenised Φ times all b_i. -/
def multihomIdeal (Φ : MvPolynomial _ A) J (φ : A →+* B) (r : Fin d → B × B) :=
  span {(∑ m ∈ Φ.support, φ
  (Φ.coeff m) * ∏ i, (r i).1 ^ m i * (r i).2 ^ (Φ.degreeOf i - m i)) * ∏ i, (r i).2} ⊔ .map φ J

lemma map_multihomIdeal Φ {J} {φ : A →+* _} (f : B →+* R) {r r'} {l : Fin d → Rˣ} (h : ∀ i, .map f f
  (r i) = (l i).1 • r' i) : (multihomIdeal Φ J φ r).map f = multihomIdeal Φ J (f.comp φ) r' := by
  erw [Ideal.map_sup, multihomIdeal,
    ← span_singleton_mul_right_unit (∏ i, l i * l i ^ Φ.degreeOf i).isUnit]
  simp_all [J.map_map, Finset.sum_mul, Prod.ext_iff, mul_assoc, ← prod_mul_distrib]
  congr! 6; rw [← pow_mul_pow_sub _ (Φ.monomial_le_degreeOf _ ‹_›)]; ring

variable (A T) in
/-- For an A-algebra T, its functor of points c ↦ Hom_A(T, c) on tests over A. -/
abbrev testSpec := (ObjectProperty.ι _ : TestOver A ⥤ _) ⋙ reprBy (of A T)

/-- A point ψ of Spec T with values in a test A-algebra c, viewed as an A-algebra homomorphism T
→ c. -/
abbrev testSpec.asAlgHom {c} (ψ : testSpec A T c) : T →ₐ[A] c.1 := ψ.1.hom

/-- For a in T, the subfunctor of Spec T (on tests over A) of the points ψ at which ψ(a) is a
unit. -/
def testUnitLocus (a : T) : Subfunctor (testSpec A T) :=
  ⟨fun _ ↦ {ψ | IsUnit (testSpec.asAlgHom ψ a)}, fun f _ ↦ .map f.1.1⟩

open IsLocalization Away Algebra in
lemma testUnitLocus.nonempty_iso_away (a : T) (L :=
  Localization.Away a) [CommRing L] [Algebra A L] [Algebra T L] [IsScalarTower A T L] [Away a L] :
  Nonempty (testSpec A L ≅ (testUnitLocus a).toFunctor) := by refine' ⟨
  NatIso.ofComponents fun _ ↦ Equiv.toIso ⟨(⟨⟨ofHom (algHom ..) ≫ _⟩, (algebraMap_isUnit a).map
  ·.1.1⟩), (⟨ofHom <| liftAlgHom a ·.2⟩), fun _ ↦ congr(⟨ofHom $(algHom_ext (.powers a) _)⟩), fun _
  ↦ congr(⟨⟨ofHom $_⟩, _⟩)⟩⟩ <;> ext <;> apply IsLocalization.lift_eq

/-- For e: A[X_1,…,X_d] ≅ T, the map from Spec T to (P¹)^d on tests over A sending ψ to the
points (ψ(e X_i) : 1). -/
def affineToLines : testSpec A T ⟶ ringOf (𝟭 _) ⋙ projLinePow (Fin d) :=
  ⟨fun _ ↦ ↾fun ψ i ↦ affinePt (testSpec.asAlgHom ψ (e (.X i))), fun _ _ _ ↦
  congr(↾fun _ _ ↦ $(.symm (map_affinePt ..)))⟩

seal Finset.sum in
instance : Mono (affineToLines e) := mono_of_app_injective fun c ψ χ
  h ↦ congr(⟨$((cancel_epi (isoMk e).1).1 (by ext; exact affinePt_injective congr($h _)))⟩)

lemma multihomIdeal_eq_top_iff {a c q} : multihomIdeal (e.symm a) ⊥ (algebraMap A c.1)
  (unimodularRow <| q ·) = ⊤ ↔ q ∈ range ((testUnitLocus a).ι ≫ affineToLines e) c := by
  obtain ⟨ψ, rfl⟩ | h := em (q ∈ range (affineToLines e) c)
  erw [← (ψ.1.hom.comp e.toAlgHom).comp_algebraMap, ← map_multihomIdeal _ _ (r := (.X ·, 1)) fun _ ↦
    .trans ?_ (@exists_unit_smul_unimodularRow (.of _) _).choose_spec, range_comp,
    (injective_of_mono _).mem_set_image] <;>
    simp [multihomIdeal, ← MvPolynomial.eval₂_eq', testUnitLocus]
  exact ψ.1.hom.map_one
  use fun k ↦ h.elim ?_, by aesop
  choose x r using ((IsUnit.dvd (by simp_all [multihomIdeal])).imp <| affinePt_eq_map (𝟙 _) <| q ·)
  use ⟨ofHom (.comp (MvPolynomial.aeval x) e.symm)⟩, by simp [affineToLines, testSpec.asAlgHom, *]

variable [InvertsPrime A ℓ] (D : ComparedTheory g)

/-- For a local ring A, the subfunctor of Y of all points over those tests c in which the
maximal ideal of A generates the unit ideal. -/
abbrev offClosedFibre Y := (@IdealFamily.ofMaximalIdeal A _ _).topLocus.preimage (toUnit Y)

namespace ComparedTheory

/-- Excision: suppose that, Zariski locally, every point of Y lies in U or the image of u: E →
Y, and points with equal image agree or lie in u⁻¹U. Then `ComparedTheory.IsGood` holds for
ℤ[E]/ℤ[u⁻¹U] exactly when it holds for ℤ[Y]/ℤ[U]. -/
lemma isGood_iff_of_locally_bijective (u : E ⟶ Y) (s : IsLocallyEverything (ringOf (𝟭 _)) (.range
  u ⊔ U)) (i : IsLocallyEverything (ringOf (𝟭 _)) (Y := fibreProd u u) ⟨fun _ x ↦ relFreeAb.mk _
  x.1.1 = relFreeAb.mk _ x.1.2, fun f _ ↦ congrArg ((relFreeAb (U.preimage u)).map f)⟩ := by
  exact fun _ ⟨(a, b), e⟩ m _ ↦ ⟨1, m.one_notMem, by cases (by apply_rules [Subtype.ext] : a = b)
    <;> tauto⟩) : D.IsGood (relFreeAb (U.preimage u)) ↔ D.IsGood (relFreeAb U) :=
  D.isGood_iff_of_isCohomEquiv (map u le_rfl) fun g z ↦
  LocalIso.isCohomEquiv ⟨fun c ↦ Quot.ind (mem_of_map_eq_zero u (π _) _ (fun x y e ↦ (z (i.whisker
  g)).of_preimage_le (pointMap ⟨(_, _), e⟩) fun _ _ ↦ sub_eq_zero.2) (by simp_all [mk_eq_zero])),
  fun c ↦ mem_of_mk_mem (U := .whisker ..) (.comap _ (locallyZero ..)) fun y ↦ (z
  (s.whisker g)).of_preimage_le (pointMap y) fun _ _ ↦ (QuotientAddGroup.eq_zero_iff _).2 ∘ Or.rec
  (.imp' (relFreeAb.mk _) fun _ ↦ congrArg (relFreeAb.mk U)) (⟨0, mk_eq_zero · |>.symm⟩)⟩

/-- For N flat and ξ in total Ext(P, T), T the Tate module, the operation y ↦ p^*((π^*y)·ξ) from
Ext(K∘g, Θ) to Ext(N'∘g, Θ), natural in the theory Θ. -/
def mulClassOp {N N' K P : AbFunctor (TestOver A)} [HasFlatValues N] (ξ :
  TotalH P (tateModule (𝟭 _))) (p : N' ⟶ abTensor N P) (π : N ⟶ K) : NaturalOp 0 K N' :=
  ⟨fun t ↦ (pullbackAlong (t.g.whiskerLeft p)).comp ((t.Θ.mulClass (.map (restrictAlong _) ξ)).comp
  (pullbackAlong (t.g.whiskerLeft π))), by
  intros; erw [mapThenComp_comp map_homClass, TorsionCoeff.mulClass_naturality (S := _ ⋙ N) (P :=
    _ ⋙ P), map_restrictAlong_restrictAlong _ _ ξ, map_comp_assoc, map_homClass]; rfl⟩

/-- Let V ⊂ Y and S ⊂ P¹ the complement of (0 : 1). If `ComparedTheory.IsGood` holds for the pair (Y
× P¹, V × P¹ ∪ Y × S), it holds for the pair (Y, V). -/
lemma isGood_of_prod_projLine : D.IsGood (relFreeAb (V.preimage (fst ..) ⊔ (affineChart.whisker
  (ringOf (𝟭 _))).preimage (snd ..))) → D.IsGood (relFreeAb V) := (((TotalH.exact_triangle
  (shortExact _).2 _).1 _).1 (comp_etaClass_eq_zero_of_isUnit (affineChart.whisker _).ι fun _ ↦
  (·.2))).elim fun ξ e ↦ D.isGood_of_retract ![mulClassOp ξ (relFreeAb.prod ..) _] ![.integrate
  ⟨fun t ↦ pullbackAlong (map (U := .whisker (_ ⊔ _) _) (U' := .whisker ..)
  (CartesianMonoidalCategory.lift (𝟙 _) (toUnit _ ≫ sectionMap (projLinePow.component t.points 0)))
  (by tauto)), by intros; apply mapThenComp_comp map_homClass⟩] fun t x ↦ (Fin.sum_univ_one _).trans
  (.trans (congrArg t.line_formula.integrate ((congrArg _ map_homClass_comp).trans (by
  conv_rhs => erw [map_zero, add_zero, ← TorsionCoeff.sliceEquiv_mulClass,
    ← map_restrictAlong_etaClass (g := 𝟭 _), ← e, map_homClass_comp, map_comp_assoc, map_homClass]
  exact (comp_assoc_of_sq (by simpa [← homClass_comp] using congrArg _ (hom_ext (U := .whisker ..)))
    _).trans (congrArg _ map_homClass_comp).symm))) (t.line_formula.integrate_mul_cupClass _ 0))

variable (L : D.IsGood (relFreeAb IdealFamily.ofMaximalIdeal.topLocus)) [Algebra A R] (P :
  StandardEtalePair R)

open AdjoinRoot Ideal.Quotient testSpec Finsupp

/-- For a standard étale pair (f, g) over R: the pairs (y, x) over one point of R with f(y) = 0,
g(y) and g(x) units, and f(x) an associate of x − y. -/
def rootPairs : Subfunctor ((testUnitLocus (A := A) (AdjoinRoot.mk P.f P.g)).toFunctor ⊗
  (testUnitLocus P.g).toFunctor) := ⟨fun _ (w, ψ) ↦ Associated (asAlgHom ψ P.f)
  (asAlgHom ψ.1 X - asAlgHom w.1 (root _)) ∧ ∀ r, asAlgHom w.1 (.of _ r) = asAlgHom ψ
  (C r), fun f _ ↦ .imp (by simpa using! ·.map f.1.1) (congr(f.1 $(· ·)))⟩

lemma exists_notMem_of_rootPairs {P} {c : TestOver A} {t m ε} (w : _ →ₐ[A] _) (ψ :
  _ →ₐ[A] c.1) [IsPrime m] (n : IsUnit (w (.mk _ P.g)) ∨ IsUnit (ψ P.g)) {S : ∀ d, (c ⟶ d) → _} (o :
  ε ∉ m) (k : t ∈ m) (s : ∀ d f h i, IsUnit (f.1.hom ε) → (⟨⟨ofHom w ≫ f.1⟩, h⟩,
  ⟨⟨ofHom ψ ≫ f.1⟩, i⟩) ∈ rootPairs P d → S d f) (j : ψ X = w (root
  _) + t ∧ ∀ r : R, w r = ψ (C r) := by simp_all) : ∃ a ∉ m, ∀ d f, IsUnit (f.1.hom a) → S d f := by
  have T p : ∃ r, ψ p = w (.mk _ p) + r * t ∧ r - ψ p.derivative ∈ m := p.recOnHorner ⟨0, by simp⟩
    (by simp; grind) fun p _ ↦ .imp' (· * w (root _) + ψ p) (by simp_all [← eq_zero_iff_mem]; grind)
  obtain ⟨⟨r⟩, ⟨⟩, ⟨_, _, _, e⟩⟩ := T P.f, T P.g, P.4, n.imp m.notMem_of_isUnit m.notMem_of_isUnit
  replace e := congr(Ideal.Quotient.mk m (ψ $e.symm))
  use w (.mk _ P.g) * ψ P.g * ε * r, fun _ ↦ by simp_all [← eq_zero_iff_mem]
  simpa using! (s · · · · · ∘ fun _ ↦ by
    constructor <;> simp [asAlgHom, *, associated_unit_mul_left])

include L

/-- Let O be the locus where 𝔪_A generates the unit ideal, and a ∈ T ≅ A[X_1,…,X_d]. If
`ComparedTheory.IsGood` holds for ℤ[pt]/ℤ[O], it holds for ℤ[(P¹)^d]/ℤ[U], U the union of (P¹)^d × O
and the locus in Spec T ⊂ (P¹)^d where a is a unit. -/
lemma isGood_principal_open a :
  D.IsGood (relFreeAb (.range ((testUnitLocus a).ι ≫ affineToLines e) ⊔ offClosedFibre _)) := by
  let I J : IdealFamily (elementsProj (projLinePow _ ⊗ reprBy (.of A))) :=
    ⟨fun x ↦ multihomIdeal (e.symm a) J x.2.2.1.1 (unimodularRow ∘ x.2.1),
    (·.2 ▸ map_multihomIdeal _ _ fun _ ↦ unimodularRow_map ..)⟩
  let Q := @IdealFamily.ofMaximalIdeal A _ _
  have γ := Theory.locallyConstant.onElements.isCohomDense_botLocus (I (maximalIdeal A)).pullToTests
  have δ := γ.mono (V := Q.botLocus.whisker (testOfPoint ..)) fun _ _ ↦ eq_bot_mono le_sup_right
  obtain ⟨ι, -, h⟩ :=
    exists_lerayHirsch_basis (Theory.onZeros ..) ((I _).isDetectedAtPoints_of_proper
    (isProperOver_projLinePow _) _ (IdealFamily.bijective_toZerosCoeff _ _) γ) δ ⟨0, 0⟩
  choose θ l using fun i : ι ↦ (δ.isCohomEquiv_of_bijective_on (α :=
    (restrictAlong _).map (Q.toZerosCoeff _)) (fun _ ↦ Q.bijective_toZerosCoeff _ _) _).2 i.1.2
  have t {E Y} (u : NatTrans E Y) (h : ∀ c k, _) := have b c k := (FreeAbelianGroup.equivOfEquiv
    (.ofBijective (u.1 c) (h c k))).bijective; (Comparison.bijective_iff_of_comm_sq
      (lerayHirsch_mapRange_comp θ (map_homClass (f := freeAb.map u))) (mapRange_bijective _ _
      ((Theory.locallyConstant.isCohomDense_botLocus Q).isCohomEquiv_of_bijective_on
      b).bijective_totalH) (δ.isCohomEquiv_of_bijective_on (b ·.1)).bijective_totalH).2
  choose _ q _ _ u k using (TestOver.exists_quotient · (Q.I _))
  have R {Y} := bijective_lerayHirsch_iff.2 ∘ @IsAffinelyCovered.devissage_bijective _ _ _ _ _ _ _
    TestOver.hasCoveringPoints Y _ _ _ lerayHirsch.devissage fun c ↦ bijective_lerayHirsch_iff.1 (t
    (reprMap _) (fun _ h ↦ ULift.map_bijective.2 (.of_existsUnique _ (u c _ · ((Q.2 _).trans h))))
    (.imp (·.of_comp_right (mapRange_surjective _ _ ((sectionEquiv ..).surjective.forall.2
    (Quot.ind (⟨sectionEquiv _ _ ·, by erw [of_comp_homClass, push_homReprEquiv_symm]; rfl⟩)))))
    .of_comp ((funext (lerayHirsch_naturality _ (comp.flip (.homClass _)) (r' := .id _)
    fun _ _ ↦ by erw [map_comp_assoc, map_homClass, homClass_comp_of, l]; rfl)).symm.subst
    (h _ ((Q.2 _).symm.trans (k c))))))
  have h : _ ⊔ offClosedFibre _ ≤ (I _).pullToTests.topPoints := fun c q ↦ Or.rec (eq_top_mono
    (sup_le_sup_left (by simp) _) ∘ (multihomIdeal_eq_top_iff e).2) (eq_top_mono le_sup_right)
  refine (D.isGood_iff_of_isCohomEquiv (relFreeAb.map (𝟙 _) h) fun g z ↦
    isCohomEquiv_of_le (U := .whisker ..) (U' := .whisker ..) (by tauto) (z fun c q m M ↦ ?_)).2
    (D.isGood_topPoints_of_surjective _ ((isClosedClass_lerayHirsch.2 _ (shortExact _).2 (t (homOfLe
    (le_sup_left.trans h)) (fun c k ↦ ⟨injective_of_mono _, (⟨⟨_, (multihomIdeal_eq_top_iff e).1 <|
    eq_top_mono (sup_le_sup_left (k.le.trans bot_le) _) ·.2⟩, rfl⟩)⟩)
    ((isClosedClass_lerayHirsch.iff_of_isIso (freeAb.map ((testUnitLocus.nonempty_iso_away a).some.1
    ≫ toRange _))).1 (R (isAffinelyCovered_reprBy _))))).1 (R isAffinelyCovered_projLinePow :)).2
    ((D.isGood_iff_of_isCohomEquiv _ (Q.isCohomEquiv_constToZeros · .locallyConstant rfl)).1
    ((D.isClosedClass_isGood.2 _ (shortExact_nsmul_abCoker (N := relFreeAb _)).2 L).1 L)))
  exact by_cases (fun k ↦ ((I ⊥).pullToTests.exists_notMem_eq_top (c := ⟨q.1⟩) fun h ↦
    M.ne_top (eq_top_mono (sup_le (le_sup_left.trans h) k) q.2)).imp fun _ ↦
    .imp_right fun H c f u ↦ .inl <| (multihomIdeal_eq_top_iff e).1 <| H (.mk (obj := g c) _)
    ⟨g.map f, rfl⟩ u) (by peel (Q.whisker g).exists_notMem_eq_top ·; tauto)

/-- Let O be the locus where 𝔪_A generates the unit ideal, R[X] ≅ A[X_1,…,X_d], and (f, g) a
standard étale pair over R. If `ComparedTheory.IsGood` holds for ℤ[pt]/ℤ[O], it holds for
ℤ[Y]/ℤ[Y × O], Y = Spec (R[X]/f)[1/g].

Step in comparing cohomology theories by duality, using a diagonal kernel on products of P¹. -/
lemma isGood_standard_etale (e : MvPolynomial (Fin d) A ≃ₐ[A] R[X]) :
  D.IsGood (relFreeAb (offClosedFibre (testUnitLocus (AdjoinRoot.mk P.f P.g)).toFunctor)) := by
  let v : (rootPairs P).toFunctor ⟶ _ ⊗ projLineAlong (𝟭 (TestOver A)) :=
    ⟨fun c ↦ ↾fun ⟨(w, ψ), _⟩ ↦ (w, affinePt (asAlgHom ψ.1 X - asAlgHom w.1 (root _))),
    fun _ _ f ↦ congr(↾fun _ ↦ (_, $(by erw [map_affinePt, map_sub]; rfl)))⟩
  have n c : (⇑(v c)).Injective := fun ⟨⟨_, ⟨_⟩, _⟩, _, j⟩ ⟨_, _, i⟩ e ↦ by
    cases congr($e.1); congr; simp; ext; simp [j, ← i]
    simpa [j, ← i] using affinePt_injective congr($e.2)
  refine D.isGood_of_prod_projLine (Iff.mp (D.isGood_iff_of_locally_bijective v fun c ⟨w, (q :
    projLine (.of c.1))⟩ m M ↦ by_cases (fun h : (unimodularRow
    q).1 ∈ m ↦ (exists_idempotent_dvd_of_notMem c.2.2 M (g := (unimodularRow q).2) (fun _ ↦ by
    simp_all [unimodularRow, ← eq_zero_iff_mem])).elim fun ε ⟨n, i, z, l⟩ ↦
    exists_notMem_of_rootPairs _ (aevalTower ((asAlgHom w.1).comp (ofAlgHom ..)) (asAlgHom w.1
    (root _) + z * (unimodularRow q).1)) (.inl w.2) n (m.mul_mem_left z h) fun _ f _ _ u k ↦ .inl
    ⟨⟨_, k⟩, congrArg _ (affinePt_eq_map _ _ _ (by
    simpa [mul_assoc, asAlgHom, l] using! congr($(u.mul_eq_left.1 (i.map
    _)) * _).symm))⟩) (⟨_, ·, fun _ _ ↦ .inr ∘ .inr ∘ isUnit_unimodularRow_map _ _⟩)) (cast
    (by congr 2 with c ψ; exact .or .rfl (ψ.2.1.isUnit_iff.trans (.symm
    isUnit_unimodularRow_affinePt_iff))) ((D.isGood_iff_of_locally_bijective (U :=
    (offClosedFibre _ ⊔ testUnitLocus P.f).preimage (ι _)) ((rootPairs P).ι ≫ snd ..) (fun c ψ m M ↦
    by_cases (fun k ↦ (c.2.exists_root_map_eq (P.monic_f.map _) (by erw [eval₂_map, ← hom_eval₂,
    ← hom_eval₂, eval₂_C_X, eq_zero_iff_mem.2 k])).elim fun y e ↦ exists_notMem_of_rootPairs
    (liftAlgHom _ ((asAlgHom ψ.1).comp CAlgHom) y ((eval₂_eq_eval_map _).trans e.1)) _ (.inr ψ.2)
    m.one_notMem (Ideal.Quotient.eq.1 e.2.symm) fun _ _ _ _ _ k ↦ .inl ⟨⟨_, k⟩, rfl⟩)
    (⟨_, ·, by tauto⟩)) fun c ⟨⟨⟨(w, ψ), a, j⟩, (χ, _), b, i⟩, rfl⟩ m M ↦ by_cases (fun n ↦
    exists_notMem_of_rootPairs _ ((asAlgHom w.1).comp (.restrictScalars A (mkₐ _))) (.inl χ.2)
    m.one_notMem (m.mem_of_dvd (b.dvd.sub a.dvd) n) fun _ _ _ _ _ k ↦ congr(relFreeAb.mk _ ⟨(⟨⟨ofHom
    $(by ext; exacts [(k.2 _).symm, by simpa [asAlgHom] using! k.1.dvd])⟩, _⟩, _), _⟩)) (⟨_, ·,
    fun _ _ h ↦ .trans (relFreeAb.mk_eq_zero (.inr h)) (.symm (relFreeAb.mk_eq_zero (.inr h)))⟩)).2
    (Eq.mpr ?_ (D.isGood_of_shortExact (shortExact_triple ((testUnitLocus P.g).ι ≫ affineToLines e)
    _).2 (D.isGood_principal_open e L (P.g * P.f)) (cast ?_ (D.isGood_principal_open e L P.g)))))))
    <;> congr 2 with _ <;> simp [range_comp, (injective_of_mono _).eq_iff, testUnitLocus] <;> grind

end ComparedTheory

end

open MvPolynomial CategoryTheory Ideal Function MonoidalCategory CartesianMonoidalCategory

/-- Let L embed Y, g be coordinates of a field point, Λ a Noether normalisation of g. If O ⊂ Γ ⊂
Y × P^d contains (x,[Λ(v)]) whenever coordinates v of x satisfy the homogeneous equations of
g, pull-back along O → P^d is injective on H^n on p-adic tests with coefficient
`genericCoeff`. -/
lemma CutsOutLocus.IsNoetherNormalization.pullback_injective {p k ι F} [Field k] [EmbeddedInQpBar p
  k] [Field F] {R} [Algebra R.1 k] [Finite ι] [Algebra k F] {g d n Y Λ} {L : LineBundle _ ι}
  [Fact (L.IsProjEmbedding Y.hom)] {ξ : PointsIn Y (.of k F)} (hξ : IsUnimodCoords L ξ g) (h :
  IsNoetherNormalization (k := k) Λ g) {Γ : Subfunctor (algPointsOf k R Y ⊗ projSpace k d)} {O :
  Subfunctor _} (E : ∀ {A x v h}, IsHomogSolution k g v → IsUnimodCoords L x v → ∃ a,
  ⟨(x, projSpace.mk (evalForms Λ v) h), a⟩ ∈ O A) :
  Injective (H.map genericCoeff (genericOver.whiskerLeft (freeAb.map (O.ι ≫ Γ.ι ≫ snd ..))) n) := by
  choose G B _ f b N i₁ i₂ M using h.exists_galois_closure
  let W := genericOver ⋙ .mk (fun A ↦ {x : (G → _) × (B ⟶ A) // (∀ σ,
    IsUnimodCoords L (x.1 σ) (x.2 ∘ b σ)) ∧ span (.range (x.2 ∘ f ∘ X)) = ⊤}) fun φ ↦ ↾fun x ↦
    ⟨(_, _ ≫ φ), (x.2.1 · |>.comp φ), unimodular.2 φ (a := ⟨_⟩) x.2.2⟩
  let t σ : W ⟶ genericOver ⋙ O.toFunctor := .mk fun _ ↦ ↾fun x ↦ ⟨_, show ∃ a, ⟨(x.1.1 σ,
    projSpace.mk _ x.2.2), a⟩ ∈ _ by convert E ((N _).1.map _) (x.2.1 σ) <;> simp [*, x.2].2⟩
  let π := genericOver.whiskerLeft (O.ι ≫ Γ.ι ≫ snd ..)
  choose _ _ _ _ _ _ e D using exists_transfer_map (by tauto : ∀ i, t i ≫ π = t 1 ≫ π)
  refine .of_comp ((funext (congr($(e ▸ map_nsmul (H.mapHom ..) ..) ·).symm.trans (H.map_comp
    ..))).subst (((HasUniqueDiv.of_isTorsionFree k _).1 (by simp)).comp (D _ ?_ ?_ n).1))
  all_goals
    refine hasZariskiDescent_genericOver (𝟭 _) (hasPartitions_periodAlg _
      exists_periodAlg_iso_genericAlg.choose) fun c x (m : Ideal (genericOver c)) hm ↦ ?_
    have I : IsTest (genericOver c) := c.isTest.localization
    choose _ _ _ _ _ O i _ using I.exists_valuationSubring_atPrime m
    algebraize [(O.subtype.comp i.2).comp (algebraMap k _)]
    let κ : _ →ₐ[k] _ := ⟨O.subtype.comp i.2, fun _ ↦ rfl⟩
    have P {σ} [Finite σ] {r s : σ → _} (h : ∀ i, κ (r i) = κ (s i)) := (IsLocalizedModule.pi
      m.primeCompl fun _ ↦ Algebra.linearMap ..).3 (funext (Subtype.ext <| h ·))
  · obtain ⟨⟨w⟩, hw⟩ := x
    obtain ⟨⟨_, π, S, s, hs⟩, φ, E⟩ := RingHom.FinitePresentation.of_finiteType.1 i₁.finiteType,
      exists_algHom_comp_eq_of_integral f (κ.comp (aeval w)) i₁.to_isIntegral
      (comap_bot_le_of_injective _ i₂)
    algebraize [f.1]
    rw [aeval_unique π] at *
    choose r H using fun i ↦ I.mem_range_of_isIntegralElem (.of_comp
      (congr(($E).IsIntegralElem _).mp ((i₁.to_isIntegral _).map _)))
    obtain ⟨⟨g, n⟩, e⟩ := @P s _ _ 0 fun x ↦ ((hom_eval₂ ..).trans (eval₂Hom_congr congr($E.symm.1)
      (funext H) rfl)).trans ((hom_eval₂ ..).symm.trans (congr(φ $(hs.le (subset_span x.2))).trans
      (by simp)))
    let H {A : CommAlg k} (ψ : _ →ₐ[k] A) (h : IsUnit (ψ g)) : {v : B ⟶ A // v ∘ f ∘ X = ψ ∘ w} :=
      ⟨_, by
      ext; simpa using! (aevalTower f _).liftOfSurjective_apply S (ψ.comp (aevalTower (aeval w) r))
       (hs ▸ span_le.2 (by simpa [h.mul_right_eq_zero, funext_iff] using! congr(ψ ∘ $e))) (C (X _))⟩
    let v := @H (.of k m.ResidueField) (IsScalarTower.toAlgHom ..) (by simpa)
    choose i hi using fun σ ↦ ne_iff.1 fun H : v.1 ∘ b σ = 0 ↦ hm.ne_top (eq_top_mono (span_le.2 (by
      simpa [funext_iff, ← H, N, v.2] using evalForms_smul Λ (u := v.1 0) (v := 0))) hw)
    choose _ _ _ _ _ _ _ S using (hξ.exists_universal_chart ((N _).1.map _) <| hi ·)
    refine ⟨_, mul_mem n (prod_mem (t := ⊤) fun σ _ ↦
      hi σ ∘ algebraMap_residueField_eq_zero.2), fun _ φ h ↦ ?_⟩
    simp at h; let v := H _ h.1
    use ⟨(_, v), (S · ((N _).1.map v.1.1) (h.2 _)),
      v.2.substr (unimodular.2 _ hw)⟩, congr(projSpace.mk $(v.2) _)
  choose u e using projSpace.mk_eq_mk_iff_exists_unit.1 (x.2 0 1)
  choose τ q using M (κ.comp _) (κ.comp _) _ (by simpa [funext_iff, u.smul_def] using congr(κ ∘ $e))
  obtain ⟨⟨g, n⟩, e⟩ := P fun l : G × ι ↦ congr($(q l.1) l.2).trans (map_mul ..).symm
  use g, n, fun _ f h ↦ ⟨.mulLeft τ, fun ρ ↦ congr(⟨⟨($(IsUnimodCoords.ext ((funext fun l ↦
    h.mul_left_cancel (by simpa using! congr(genericOver.map f ($e (ρ, l))))).subst (((x.1 1).2.1
    ρ).comp _)) (((x.1 0).2.1 _).map_unit_smul _ (u.map _))), $(((cech ..).map f x).2 ..)), _⟩, _⟩)⟩
