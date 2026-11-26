import GRH.Lib.General.Geometry.ChartedSchemes
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Local cohomology vanishes below the depth; Zariski descent for Hodge tests. -/

open Localization CategoryTheory Fin Function Ideal IsLocalizedModule LinearMap MvPolynomial RingHom
  ConcreteCategory CategoryTheory.Functor IsLocalization.Away RingTheory.Sequence

variable {k ι : Type} [CommRing k] {c : HodgeTest k} {n} [Fintype ι] {f : ι → c.baseAlg} {d}

/-- For a pair c = (A,M) and a family (f_i) in A, the subfunctor of h_c of morphisms whose ring
map sends some f_i to a unit. -/
def someUnitLocus (f : ι → c.baseAlg) : Subfunctor (reprBy c) :=
    ⟨fun _ ↦ {y | ∃ i, IsUnit (y.1.1 (f i))}, fun a _ ↦ .imp fun _ ↦ .map a.1.1⟩

/-- Depth vanishing (Rees, Grothendieck): suppose each H^n(M) is I-power torsion elementwise,
and each M-regular r is regular on H^n(M) once H^m(M/rM) = 0 for m < n. Then H^n(M) = 0 if I
contains a weakly M-regular sequence longer than n. -/
lemma depth_vanishing (H : ℕ → _ → ModuleCat k) {I l} (hI : ∀ n M x, I ≤
    (torsionOf k (H n M) x).radical) (hδ : ∀ n (M : ModuleCat k) (r : k), IsSMulRegular M r → (∀ m <
    n, Subsingleton (H m (.of k (QuotSMulTop r M)))) → IsSMulRegular (H n M) r) (hl : ofList l ≤ I)
    (hn : n < l.length) (M : ModuleCat k) (h : IsWeaklyRegular M l) : Subsingleton (H n M) := by
  induction l generalizing M n <;> simp at *
  exact subsingleton_of_forall_eq 0 (hI _ _ · hl.1 |>.elim ((hδ _ _ _ h.1 (by bound)).pow ·
    |>.right_eq_zero_of_smul))

seal exteriorMap in
/-- For a pair c = (A,M) and finitely many f_i in A whose ideal contains a weakly A-regular
sequence l, the cohomology with coefficients ⋀M of h_c relative to the locus where some f_i
is a unit vanishes below the length of l. -/
lemma DepthVanishing.subsingleton_of_isWeaklyRegular l (hl : ofList l ≤ span (.range f)) (hn :
  n < l.length) (h : IsWeaklyRegular c.baseAlg l) :
  Subsingleton (H (relFreeAb (someUnitLocus f)) hodgeCoeff n) := by
  let L {C} [Category C] (φ : C ⥤ _) x s : C ⥤ Comma (𝟭 _) (coyoneda ⟨c⟩) :=
    .mk (⟨x ⟶ ·, _, ↾(s ≫ φ.map ·)⟩) fun a ↦ .mk (↾(· ≫ a)) (φ.map a)
  let ψ := L (𝟭 _) c (𝟙 _); let P := ObjectProperty.ι fun B : CommAlg c.baseAlg ↦
    Module.Flat c.baseAlg B
  let U g : Subfunctor (Comma.fst (𝟭 _) (coyoneda ⟨c⟩) ⋙ uliftFunctor) := ⟨fun X ↦ {t |
    IsUnit ((X.3 t.1).1 g)}, fun a _ ↦ congr(IsUnit (($a.w _).1 g)).mpr ∘ .map a.2.1.1⟩
  have bij B (b : P B) := (@pointMap_bijective_of_existsUnique _ _ B ⟨_, B.2.trans ..⟩) ⟨fun _ ↦
    {x | IsUnit (x.1.1 b)}, fun a _ ↦ .map a.1.1⟩ ⟨⟨⟨B.1.toAway b⟩⟩, algebraMap_isUnit _⟩ fun _ _
    h ↦ ⟨⟨ofHom (liftAlgHom _ h)⟩, by aesop (add simp Algebra.algHom)⟩; let W := ⨆ i, U (f i)
  have ind {Q} (hP : IsClosedClass Q) (h : ∀ g, Q (freeAb (U g).toFunctor)) :=
    (hP.2 _ (relFreeAb.shortExact W).2 (hP.freeAb_iSup
    (.range U) (by simpa [h] using (⟨· * ·, by ext; simp [U]⟩)) (by simp))).1
    ((hP.iff_of_isIso (freeAb.map (Subfunctor.ι ⊤))).1 (by simpa [U] using! h 1))
  let γ : Comparison hodgeCoeff (piAbFunctor fun _ ↦ moduleCoeff (asModules P ⋙ tensorWith c.baseAlg
    _)) := ⟨P ⋙ restrictAlg k _ ⋙ HodgeTest.withIndex c.Index, fun B ↦ (AddEquiv.ulift.trans
    ((Pi.basisFun B.1 c.Index).ExteriorAlgebra.equivFun.toAddEquiv.trans (.piCongrRight fun _ ↦
    .symm (.trans .ulift (TensorProduct.lid ..).toAddEquiv)))).toAddCommGrpIso.hom,
    fun B D a ↦ by ext; congrm (⟨1 ⊗ₜ $(HodgeTest.repr_withIndex_map a.1 _ ·)⟩)⟩
  let ψ' := L γ.φ ⟨.of .., .self⟩ ⟨ofHom ⟨.id _, by tauto⟩, .id⟩
  let η : ψ' ⟶ γ.φ ⋙ ψ := .mk fun B ↦ .mk (ψ' B).3 (𝟙 _)
  refine (by ext; simp [W, Subfunctor.whisker]; rfl : W.whisker ψ = someUnitLocus f) ▸ have :=
      (depth_vanishing (fun n M ↦ .of _ (H (ψ' ⋙ relFreeAb W) (moduleCoeff (asModules P ⋙ tensorWith
      _ M)) n)) (fun n M _ ↦ span_le.2 (fun | _, ⟨i, rfl⟩ => exists_exists_eq_and.1 (mem_ker_iff
      (.powers _) (g := TensorProduct.mk _ (Away (f i)) _ 1).1 ((ind (FP.isClosedClass.comap
      (restrictAlong ψ')) (bij ⟨.of .., _⟩ · |> FP.isClosedClass.of_bijective _ <|
      hasFlatBaseChange_reprFunctor _) _ c.baseAlg ..).1 (((relFreeAb.isCohomEquiv_iff_subsingleton
      (W.whisker _)).1 (IsCohomDense.isCohomEquiv (.mono (U := (U _).whisker ψ') ?_ fun _ ↦ le_iSup
      (U ∘ f) i _)) n).1 ..))))) (fun _ M r h i _ _ ↦ eq_of_tensorPush_eq (exact_lsmul_mkQ_smul_top
      M r) Quot.exists_rep (·.2.rTensor_preserves_injective_linearMap _ h) i) hl hn (.of ..) h)
    ((H.pi_bijective ..).comp (ind (γ.isClosedClass η) (fun g ↦ ((γ.isBijective_congr (pointMap_comp
      _ (whiskerRight η (U g).toFunctor)) (.of_bijective (pointMap_bijective_of_existsUnique
      ((U g).whisker ψ) _ (HodgeTest.existsUnique_lift_away _ g isLocalization.1)))
      (.of_bijective (bij ⟨.of .., .self⟩ g))).2 (γ.isBijective_of_repr (u :=
      pointMap ⟨𝟙 _⟩) ⟨𝟙 _⟩ (pointMap_id_bijective_of_fullyFaithful (𝟭 _) _) (.comp
      (AddEquiv.bijective _) (bijective_of_isIso (hodgeCoeff.map (_ ≫ _))))) :)) n)).1.subsingleton
  rintro B ⟨⟨y⟩⟩; cases show y = structureMap by ext
  exact (Comparison.isBijective_of_repr _ (bij B _) (ULift.map_bijective.2 (congr(Bijective $(show _
    = lTensor .. by ext; simp [TensorProduct.smul_tmul']; rfl)).mp (isBaseChange (.powers (f i)) _
    ((TensorProduct.assoc ..).1 ∘ₗ TensorProduct.map (TensorProduct.mk c.baseAlg _ _ 1)
    (IsScalarTower.toAlgHom _ B.1 (Away (algebraMap _ _ (f i)))).toLinearMap))))).eqv

lemma isCohomEquiv_someUnitLocus (h : span (.range f) = ⊤) : IsCohomEquiv hodgeCoeff
  (freeAb.map (someUnitLocus f).ι) := (relFreeAb.isCohomEquiv_iff_subsingleton _).2 fun n ↦
  DepthVanishing.subsingleton_of_isWeaklyRegular
  (.replicate n.succ 1) (by aesop) (by simp) ⟨by simp⟩

/-- For a pair c = (R, M) over k and étale coordinates x_1, …, x_{2d} on R, the cohomology of
h_c with coefficients ⋀M and supports in the common zeros of the x_i − x_{d+i} vanishes in
degrees below d. -/
lemma hodge_vanishing_along_diagonal {x : _ → c.baseAlg} (hx : (polyEval x).Etale) (hn : n < d) :
  Subsingleton (H (relFreeAb (someUnitLocus (x ∘ castAdd d - x ∘ natAdd d))) hodgeCoeff n) :=
  DepthVanishing.subsingleton_of_isWeaklyRegular _ (by simp [ofList, Set.range, algebraMap])
  (by simpa) (@.of_flat _ _ _ _ (_) (Flat.comp (.of_bijective (f := (bind₁ (append (X ∘ castAdd d
  - X ∘ natAdd d) (-X ∘ natAdd d))).1) (Involutive.bijective (by apply ·.induction_on <;> simp_all
  [forall_fin_add, -natAdd_eq_addNat]))) (Etale.iff_flat_and_formallyUnramified.1 hx).1)
  (.ofFn (X ∘ castAdd d)) ⟨fun i _ ↦ (isSMulRegular_quotient_iff_mem_of_smul_mem ..).2 fun p h ↦ by
  rw [smul_eq_mul, mul_top, ofList, show {r | r ∈ _} = X '' castAdd d '' {j | j < i} by
    grind [List.mem_take_iff_getElem], mem_ideal_span_X_image] at *
  exact fun m _ ↦ (h (.single ⟨i, by grind⟩ 1 + m) (by simp_all)).imp (by simp; grind)⟩)

/-- Open covers are dense for Hodge cohomology: the coefficients (A,M) ↦ ⋀_A M satisfy Zariski
descent `HasZariskiDescent` for the rings A ⊕ M. -/
lemma hasZariskiDescent_hodgeCoeff : HasZariskiDescent (@HodgeTest.sqZeroExt k _ ⋙ forget₂ _ _)
  hodgeCoeff := fun Y U h X y ↦ ((span_eq_top_iff_finite _).1
  (ne_top_iff_exists_maximal.not_right.2 fun ⟨m, l, e⟩ ↦ (h X y m l).elim fun _ a ↦ a.1
  (e (subset_span a.2)))).elim fun s ⟨l, e⟩ ↦ (IsCohomDense.mono (U := someUnitLocus fun i : s ↦
  X.baseProj _) (fun _ g ↦ isCohomEquiv_someUnitLocus (by erw
  [← Set.image_eq_range (X.baseProj ≫ _), ← Ideal.map_span, e, Ideal.map_top])) fun _ _ ⟨i, u⟩ ↦
  l i.2 _ _ (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 u)).isCohomEquiv
