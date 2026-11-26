import OmegaMath.NumberTheory.GRH.Lib.General.Geometry.EtaleCharts
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck symbols)
(known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Ext classes of cocycles of functors; connecting classes commute up to sign. Hodge
cohomology as Ext on pairs (algebra, free module); scaling, base change, charts. -/

open Function Pi AddCommGrpCat CategoryTheory ExteriorAlgebra IsLocalization LinearMap TotalH Limits
  ShortComplex

set_option backward.isDefEq.respectTransparency false

variable {C} [Category C] {F G : AbFunctor C} {T T' M M' : Type} [CommRing T] [CommRing T']
  [AddCommGroup M] [AddCommGroup M'] [Module T M] [Module T' M'] {a : T →+* T'} (m : M →ₛₗ[a] M')

/-- Let 0 → ΨK → ΞK → ΦK → 0 be short exact, naturally in K, with Φ, Ψ exact. For x in
Ext^a(F,G), Φ(x) followed by the extension class at G equals (−1)^a times the extension
class at F followed by Ψ(x). -/
lemma TotalH.extClass_sign_comm {Ψ Ξ Φ : _ ⥤ AbFunctor C} [IsExactFunctor Φ] [IsExactFunctor Ψ]
  [Ξ.Additive] {i : Ψ ⟶ Ξ} {p : Ξ ⟶ Φ} {w : ∀ _, _}
  (h : ∀ K, ShortExact ⟨i K, p K, w K⟩) {a} x : comp (map Φ (.of _ a x)) (h G).extClass.toTotalH =
  (-1) ^ a • comp (h F).extClass.toTotalH (map Ψ x.toTotalH) := by
  induction' x with _ f T t
  simp [comp_of, (h _).extClass_naturality (h _) ⟨_, _, _, i.2 f, p.2 f⟩]
  convert comp_assoc_of_eq ‹_› (-map Ψ t.extClass.toTotalH) using 1 <;> simp [← comp_of, map_comp,
    pow_add, comp_assoc]
  rcases (h · |>.2), (h · |>.3), t.2, t.3
  have N {S A B} (h : ShortExact S) α [@Mono (AbFunctor C) _ A B α] a {b} w := have := h.3
    (h.1.desc' _ (by simp [← reassoc_of% w])).imp fun c e ↦
            Exists.intro e (h.extClass_naturality ⟨exact_cokernel α⟩ ⟨a, b, c, w, e.symm⟩)
  obtain ⟨⟨u, hu, _⟩, v, hv, _⟩ := N (h _) (_ ≫ _) (𝟙 _) (i.2 T.f), N (t.map Ψ)
    (Ψ.map _ ≫ i _) (𝟙 _) rfl
  obtain ⟨⟨c, _, _⟩, b, hb⟩ := N (h _) (pushout.inl ..) v pushout.condition,
    (h _).1.desc' (cokernel.π _ ≫ pushout.inl v _ -
    Ξ.map T.g ≫ pushout.inr _ (i _)) (by simp [← reassoc_of% hv, pushout.condition])
  simp_all [comp_of, ← Abelian.Ext.comp_assoc_of_second_deg_zero, (t.map Φ).extClass_naturality
    ⟨exact_cokernel _⟩ (by use u, b, -c <;> simp [← cancel_epi (p _), ← p.naturality_assoc,
    *, reassoc_of% hu, ← Ξ.map_comp_assoc, reassoc_of% hb])]

/-- A short exact sequence 0 → G' → E → G → 0 of functors to abelian groups, G with flat values,
stays short exact after pointwise tensor product with any K. -/
lemma abTensor_shortExact {G' : AbFunctor C} [HasFlatValues G] {E f g w} (hS :
  ShortExact (@mk _ _ _ G' E G f g w)) K : ShortExact ⟨abTensor.flip.map f K, abTensor.flip.map g K,
  zero (ShortComplex.map ⟨f, g, w⟩ _)⟩ := have := HasFlatValues.flat
  by apply (shortExact_of_app ..).2 <;> intro c <;> have r := hS.map_of_exact ((evaluation ..)
    c) <;> apply_rules [lTensor_exact, r.ab_surjective_g, lTensor_surjective, r.ab_injective_f,
                  (g c).hom.toIntLinearMap.lTensor_injective_of_exact_of_flat,
    LongExactSeq.exact_of_shortComplex_exact r.1]

/-- The multiplicative group: the functor sending a commutative ring R to its unit group R^×,
written additively. -/
def Gm : AbFunctor CommRingCat :=
  liftCoeff (forget₂ .. ⋙ CommMonCat.units ⋙ CommGrpCat.toAddCommGrp)

lemma Gm.ext {A} {u v : Gm A} : u = v ↔ u.1.1 = v.1.1 := ULift.ext_iff.trans Units.ext_iff

/-- A 1-cocycle from F to G: homomorphisms D(f): F(c) → G(d) for f: c → d, with D(gf) = G(g)D(f)
+ D(g)F(f). -/
structure Cocycle (F G : AbFunctor C) where
  component {c d} : (c ⟶ d) → (F c ⟶ _)
  cocycle_comp {c d e} f g : component (f ≫ g) =
    @component c d f ≫ G.map g + F.map f ≫ @component d e g

/-- For a cocycle D, the sequence G → E → F with E(c) = G(c) × F(c), where f acts by (y,x) ↦
(G(f)y + D(f)x, F(f)x). -/
@[local simp] def Cocycle.extension (D : Cocycle F G) : ShortComplex (AbFunctor C) := .mk (X₂ :=
  ⟨_, fun f ↦ ofHom (((G.map f).hom.coprod (D.component f).hom).prod
  ((F.map f).hom.comp (.snd ..))), by have := (D.cocycle_comp (𝟙 _) <| 𝟙 ·); aesop, by
  aesop (add simp [cocycle_comp, add_assoc])⟩) {app _ := ofHom (.inl ..)} {app _ := ofHom (.snd ..)}

lemma Cocycle.shortExact_extension (D : Cocycle F G) :
  D.extension.ShortExact := by apply (shortExact_of_app ..).2 <;> aesop_cat

/-- For a cocycle D from F to G, the class in Ext^1(F,G) of its extension G → E → F, viewed in
the total Ext group. -/
noncomputable abbrev Cocycle.cohomClass (D : Cocycle F G) : TotalH F G :=
  Abelian.Ext.toTotalH D.shortExact_extension.extClass

lemma Cocycle.cohomClass_comp_eq_extClass (D : Cocycle F G) {S} (hS : ShortExact S) (α :
  F ⟶ S.X₃) β (σ : ∀ _, _) (h : ∀ c, σ c ≫ S.g c = α c) (h' : ∀ c d f, σ c ≫ S.X₂.map f =
  D.component f ≫ β d ≫ S.f d + F.map f ≫ σ d) : D.cohomClass.comp (.homClass β) = pullbackAlong α
  hS.extClass.toTotalH := by simp [comp_of, D.shortExact_extension.extClass_naturality hS (by use β,
  ⟨fun c ↦ ofHom (((β ≫ S.f) c).hom.coprod (σ c).hom),
  ?_⟩, α <;> intros <;> ext <;> simp [add_assoc, ← h, elementwise_of% h', ← S.f.comp_app_apply])]

variable {F' G' : AbFunctor C} (D : Cocycle F G) (D' : Cocycle F' G') {k : Type} [CommRing k]

lemma Cocycle.cohomClass_naturality α β (h : ∀ c d f, α c ≫ D'.component f = D.component f ≫ β d) :
  D.cohomClass.comp (.homClass β) = pullbackAlong α D'.cohomClass :=
  D.cohomClass_comp_eq_extClass D'.shortExact_extension _ _ (α · ≫ ofHom (.inr ..)) (by tauto)
  (by simp_all [AddCommGrpCat.ext_iff])

lemma Cocycle.map_cohomClass_restrict {φ : C ⥤ C} : D.cohomClass.map (restrictAlong φ) = cohomClass
  ⟨(by exact D.component <| φ.map ·), by simp [cocycle_comp]⟩ := map_extClass D.shortExact_extension

/-- For a ring map a: T → T' and an a-semilinear map m: M → M', the ring homomorphism ⋀_T M →
⋀_{T'} M' extending a and m. -/
def exteriorMap := letI := Algebra.compHom (ExteriorAlgebra T' M') a
       (ExteriorAlgebra.lift T ⟨⟨_, (ι _ ∘ₛₗ m).2⟩, by simp⟩).1

@[simp] lemma exteriorMap_iota x : exteriorMap m (ι T x) = ι _ (m x) := @lift_ι_apply ..

@[simp] lemma exteriorMap_smul r x : exteriorMap m (r • x) =
  a r • exteriorMap m x := by simp [exteriorMap]; rfl

attribute [local simp] Algebra.algebraMap_eq_smul_one ιMulti_apply Finsupp.single_apply
  Set.powersetCard.ofFinEmbEquiv map_list_prod

lemma exteriorMap_iotaMulti {d} v : exteriorMap m (ιMulti _ d v) =
  ιMulti _ d (m ∘ v) := by simp [comp_def]

instance : Category (HodgeTest k) where
  Hom X Y := Σ a : X.baseAlg ⟶ _,
    (_ → X.baseAlg) →ₛₗ[(a.hom : X.baseAlg →+* Y.baseAlg)] Y.Index → Y.baseAlg
  id _ := ⟨𝟙 _, .id⟩
  comp f g := ⟨f.1 ≫ g.1, g.2.1.comp f.2.1, by simp⟩

variable (ι : Type) [Fintype ι] {k' : Type} [CommRing k']

/-- For a finite set ι, the functor A ↦ (A, A^ι) from k-algebras to pairs, an algebra map acting
coordinatewise on A^ι. -/
abbrev HodgeTest.withIndex [LinearOrder ι] : CommAlg k ⥤ HodgeTest k := .mk (⟨·, ι⟩) fun a ↦
  ⟨a, ⟨(a ∘ ·), by simp⟩, by aesop⟩

variable (a) {ι} (v : ι → M') {C : Type _} [Category C] {A B : CommAlg k} (f : A ⟶ B)

/-- For a ring map a: T → T' and vectors v_i in M', the a-semilinear map T^ι → M', (t_i) ↦ Σ
a(t_i) v_i. -/
def semilinearOfBasis : (ι → T) →ₛₗ[a] M' := ∑ i,
  .toSpanSingleton _ _ (v i) ∘ₛₗ a.toSemilinearMap ∘ₛₗ .proj i

@[simp] lemma semilinearOfBasis_single i : semilinearOfBasis a v (Pi.single i 1) =
  v i := by simp [semilinearOfBasis]

/-- The functor sending a pair (A, M) to the square-zero extension A ⊕ M, as a k-algebra. -/
def HodgeTest.sqZeroExt : HodgeTest k ⥤ CommAlg k :=
  .mk (.of k <| TrivSqZeroExt _ <| _ → ·.baseAlg) fun f ↦ CommAlgCat.ofHom (by
  refine' { toFun x := (f.1 x.fst, f.2 x.snd), .. } <;> simp [TrivSqZeroExt.ext_iff])

/-- The functor sending a pair (A, M) to the exterior algebra ⋀_A M, as a k-algebra. -/
def exteriorAlg : HodgeTest k ⥤ AlgCat
  k := by refine' ⟨fun X ↦ .of k (ExteriorAlgebra X.baseAlg (X.Index → X.baseAlg)), fun f ↦
  AlgCat.ofHom (.mk' (exteriorMap f.2) (by simpa using exteriorMap_smul f.2 <| · • 1)), _, _⟩ <;>
  intros <;> ext <;> induction ‹_› using induction <;> aesop

/-- The functor (A, M) ↦ ⋀_A M with values in abelian groups: the coefficient of Hodge
cohomology. -/
abbrev hodgeCoeff := moduleCoeff (@exteriorAlg k _ ⋙ forget₂ _ (ModuleCat k))

/-- For a functor Φ to k-algebras with underlying functor F to abelian groups, the pairing F ⊗ F
→ F given by multiplication. -/
def CategoryTheory.Functor.mulPairing (Φ : C ⥤ AlgCat k) : let F := moduleCoeff (Φ ⋙ forget₂ _
    (ModuleCat k)); abTensor F F ⟶ F := ⟨fun c ↦ ofHom (mul' ℤ (ULift (Φ c))).toAddMonoidHom,
  fun _ _ f ↦ addCommGrp_tensor_hom_ext fun _ _ ↦ congrArg _ (map_mul (Φ.map f).1 ..).symm⟩

/-- For a test (A, A^ι), the basis of the exterior algebra ⋀_A A^ι over A formed by the wedge
products of standard basis vectors. -/
noncomputable abbrev HodgeTest.formBasis {c : HodgeTest k} :=
  (basisFun c.baseAlg c.Index).ExteriorAlgebra

variable [LinearOrder ι] {P Q : HodgeTest k} {N : AbFunctor (CommAlg k)} {q : ℕ} {N' :
  AbFunctor (CommAlg k)} {q : ℕ} (α : N' ⟶ N) (t : k) {E : Type}

lemma exteriorMap_formBasis (f : P ⟶ Q) (j : _ ↪o _) (h : ∀ i, f.2 (Pi.single i 1) = Pi.single (j i)
  1) s : exteriorMap f.2 (P.formBasis s) = Q.formBasis (s.map j.1) := by simp [basis_apply_ofCard,
  h, comp_def, ← Finset.orderEmbOfFin_unique' (f := (s.orderEmbOfFin _).trans j)]

lemma HodgeTest.repr_withIndex_map x s : formBasis.repr (exteriorMap ((withIndex ι).map f).2 x) s =
  f (formBasis.repr x s) := formBasis.sum_repr x ▸ by simp [-Module.Basis.sum_repr,
  exteriorMap_formBasis ((withIndex _).map f) (.refl _), funext_iff]

/-- For a test pair C=(A,M), the k-algebra projection A⊕M→A, (a,m)↦a, from the square-zero
extension. -/
abbrev HodgeTest.baseProj C : @sqZeroExt k _ C ⟶ C.baseAlg :=
  CommAlgCat.ofHom (TrivSqZeroExt.fstHom ..)

lemma HodgeTest.hom_ext : ∀ {f g : P ⟶ Q}, f.1 = g.1 → (∀ i, f.2 (Pi.single i 1) =
  g.2 (Pi.single i 1)) → f = g := by rintro ⟨⟩ _ ⟨⟩ _; congrm ⟨_, $((basisFun ..).ext (by simpa))⟩

/-- Hodge cohomology: for a functor N from k-algebras to abelian groups, Ext^q from (A, M) ↦ N(A
⊕ M) to (A, M) ↦ ⋀_A M, in functors on pairs. -/
abbrev HodgeH N q := H (@HodgeTest.sqZeroExt k _ ⋙ N) hodgeCoeff q

/-- For α: N' → N, the k-linear pull-back from the degree-q Hodge cohomology of N to that of N'. -/
noncomputable abbrev HodgeH.map : HodgeH N q →ₗ[k] HodgeH N' q :=
  H.mapₗ _ _ (Functor.whiskerLeft _ α) q

/-- For t in k and a functor F on the tests (A, M), the endomorphism of F induced by the
identity of A and multiplication by t on M. -/
def HodgeTest.scaleModule {C} [Category C] (F : HodgeTest k ⥤ C) : F ⟶ F :=
  Functor.whiskerRight (⟨fun _ ↦ ⟨𝟙 _, t • .id⟩, fun _ _ f ↦ hom_ext rfl fun _ ↦ by simpa using!
  (f.2.2 (t • 1) _).symm⟩ : 𝟭 (HodgeTest k) ⟶ 𝟭 (HodgeTest k)) F

/-- For t ∈ k, the endomorphism s_t of the degree-q Hodge cohomology of N induced by (a, m) ↦
(a, tm) on A ⊕ M. -/
noncomputable abbrev HodgeH.scale : HodgeH N q →+ HodgeH N q :=
  H.map _ (HodgeTest.scaleModule t _) _

lemma HodgeTest.existsUnique_lift_away g (h : (Submonoid.powers g).IsLocalizationMap f) Z φ (u :
  IsUnit (φ.1 g)) :
  ∃! y : _ ⟶ Z, (withIndex ι).map f ≫ y = φ := have s i : f ∘ _ = Pi.single i 1 := by bound
  let := f.1.toAlgebra; have : Away g B := ⟨h⟩
    Injective.existsUnique_of_mem_range (fun _ _ e ↦ hom_ext (CommAlgCat.Hom.ext
      (algHom_ext (.powers g) (by congrm $e.1.1))) (s · ▸ congr($e.2 _))) ⟨⟨CommAlgCat.ofHom
      (Away.liftAlgHom _ u), semilinearOfBasis ..⟩,
      hom_ext (by ext; apply lift_eq) (s · ▸ semilinearOfBasis_single ..)⟩

/-- For an E-algebra k, the comparison from Hodge coefficients over E to those over k, given by
restriction of scalars on pairs and the identity of ⋀_A M. -/
def HodgeTest.baseComparison [CommRing E] [Algebra E k] : Comparison (@hodgeCoeff E _)
  (@hodgeCoeff k _) := ⟨.mk (⟨_, ·.Index⟩) fun f ↦ ⟨(restrictAlg ..).map f.1, f.2⟩, by apply 𝟙⟩

/-- Base change: for an E-algebra k, the additive map from the Hodge cohomology over E of N to
that over k of N restricted to k-algebras. -/
noncomputable def HodgeH.baseChange [CommRing E] [Algebra E k] {N : AbFunctor (CommAlg E)} :
  HodgeH N q →+ HodgeH (restrictAlg E k ⋙ N) q := HodgeTest.baseComparison.pull
  (Functor.whiskerRight (𝟙 (HodgeTest.sqZeroExt ⋙ restrictAlg E k)) N) q

@[simp] lemma HodgeH.baseChange_map [Algebra k' k] {N N' : AbFunctor (CommAlg k')} (α : N' ⟶ N) (x :
  HodgeH N q) : baseChange (k := k) (map α x) = map (Functor.whiskerLeft _ α) x.baseChange :=
  (Comparison.map_pull_eq_pull_map (by aesop) ..).symm

/-- For a chart a over a field E, with ring R and q étale coordinates, some E-algebra section u of
R ⊕ R^q → R is universal: composing with u is a bijection from maps of tests (R, R^q) → (A, M) to
E-algebra maps R → A ⊕ M. -/
lemma EtaleChart.exists_univPoint [Field E] {X : CommAlg E ⥤ Type 1} (a : EtaleChart q X) : ∃ u : _
  ⟶ HodgeTest.sqZeroExt ⟨_, Fin q⟩, LeftInverse TrivSqZeroExt.fst u ∧ AllBijective (pointMap (Y := _
  ⋙ reprBy a.R) ⟨u⟩ ·) := have ⟨u, ⟨h, e⟩, _⟩ := etale_polyEval_iff.1 a.etale (HodgeTest.baseProj _)
                            fst_surjective_and_kerIdeal_sq (𝟙 _) (_, Pi.single · 1) (by tauto)
  ⟨u, (congr($h ·)), fun c ↦ bijective_iff_has_inverse.2 ⟨(⟨·.1 ≫ c.baseProj, semilinearOfBasis
    ..⟩), fun f ↦ congrArg _ (HodgeTest.hom_ext (h =≫ _) (by simpa using! congr(f.1.2 $(e ·).2))),
    fun _ ↦ congrArg ULift.up (lift_unique _ (π := c.baseProj) fst_surjective_and_kerIdeal_sq
    (h =≫ _ ≫ c.baseProj) (congr(HodgeTest.sqZeroExt.map _ $(e ·)).trans
    (TrivSqZeroExt.ext rfl (semilinearOfBasis_single ..))))⟩⟩

instance [Field E] [CharZero E] (F) : HasFlatValues (@moduleCoeff E _ C _ F) :=
  ⟨(.trans ℤ E <| ULift <| F ·)⟩
