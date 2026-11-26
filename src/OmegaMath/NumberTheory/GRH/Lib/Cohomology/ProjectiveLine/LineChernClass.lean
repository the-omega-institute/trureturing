import OmegaMath.NumberTheory.GRH.Lib.Cohomology.Duality.Contraction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Kummer sequence, Chern class of O(1), projective line formula (tilted O/p coefficients)
(known result; see Lib.Cohomology.ProjectiveLine.NormalizationPullback).

This file: Kummer sequence, trivialised Tate twist, and its cup action on torsion coefficient
theories. Projective line as functor, cocycle of O(1), first Chern class and its cup operator. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

noncomputable section

open AddCommGrpCat CategoryTheory FreeAbelianGroup Ideal NeZero Polynomial TotalH TensorProduct
  Abelian

set_option backward.isDefEq.respectTransparency false

variable {C} [Category C] {A} [CommRing A] (g : C ⥤ TestOver A)

/-- The Kummer short complex T → Hom(ℚ, G_m) → G_m of functors along g, formed by evaluation at
1 and its kernel T, the Tate module. -/
abbrev kummerSeq := kerComplex (M := .mk (AddCommGrpCat.of <| ℚ →+ (ringOf g ⋙ Gm) ·) fun f ↦ ofHom
    (.compHom ((_ ⋙ Gm).map f).hom)) (G := _ ⋙ Gm) {app _ := ofHom (.eval 1)}

/-- The Tate module of the multiplicative group: the functor sending c to the group of
homomorphisms χ from ℚ to the units of g(c) with χ(1) = 1. -/
abbrev tateModule := (kummerSeq g).X₁

instance : HasFlatValues (tateModule g) :=
  ⟨fun c ↦ have : HasUniqueDiv (ℚ →+ (ringOf g ⋙ Gm).obj c) := ⟨fun n hn t t' h ↦
    AddMonoidHom.ext fun s ↦ by
      simpa [← map_nsmul, mul_div_cancel₀, hn, -Functor.comp_obj] using congr($h (s / n))⟩
    inferInstanceAs (Module.Flat ℤ (AddMonoidHom.ker _))⟩

variable {ℓ} {A : Type} [CommRing A] {g : C ⥤ TestOver A} [u : InvertsPrime A ℓ] {S' F :
  AbFunctor C}

/-- For a functor g from C to tests over A, the Kummer sequence 0 → T → Hom(ℚ, G_m) → G_m → 0 of
functors along g is short exact; T is the Tate module and the last map is evaluation at 1. -/
lemma shortExact_kummerSeq (g : C ⥤ TestOver A) : (kummerSeq g).ShortExact :=
  kerComplex_shortExact fun c y ↦
  (@exists_compatible_roots _ _ (g c).2.1 _).imp' (.comp (.mk' _ (by tauto)) ·) fun _ ↦ congrArg _

/-- A chosen homomorphism χ from ℚ to the units of A with χ(1) = 1 and χ(1/ℓ) a root of the ℓ-th
cyclotomic polynomial. -/
def cyclotomicRootSystem : {χ : Multiplicative ℚ →* Aˣ // χ (.ofAdd 1) = 1 ∧
  (cyclotomic ℓ A).IsRoot (χ (.ofAdd (1 / ℓ)))} := Nonempty.some
  ((IsAIC.exists_root _ (cyclotomic.monic ℓ A) (by simp [natDegree_cyclotomic, pos])).elim fun ζ h ↦
  (exists_compatible_roots (.ofMul (.ofPowEqOne ζ ℓ (isRoot_of_unity_of_root_cyclotomic
  (by aesop) h) (ne ℓ)))).elim fun x _ ↦ ⟨(ℓ • x).toMultiplicativeLeft, by simpa [← map_nsmul, *]⟩)

variable (g) in
/-- The section of the Tate module `tateModule` given by a chosen χ: ℚ → Aˣ with χ(1) = 1 and
χ(1/ℓ) a root of the ℓ-th cyclotomic polynomial. -/
def tateGen : freeAb (pointFunctor C) ⟶ tateModule g := freeAb.desc (fun c _ ↦
  ⟨.comp (.mk' .up (by tauto)) ((Units.map (algebraMap A (g c).1).1).comp _).toAdditiveRight,
  congrArg _ (congr(Units.map _ $(cyclotomicRootSystem.2.1)).trans
  (map_one _))⟩) (by intros; congr; ext; exact Gm.ext.2 ((g.map _).1.hom.2 _).symm)

/-- Let ℓ be invertible in A. If ℓ kills S' and F satisfies Zariski descent along g, then the map
S' → S'⊗T, x ↦ x⊗ε (T the Tate module, ε = `tateGen`), induces bijections on all Ext^n(−, F). -/
lemma isCohomEquiv_tateGen (hS : ∀ c (x : S' c), ℓ • x = 0) (hF : HasZariskiDescent (ringOf g) F) :
  IsCohomEquiv F (tensorPoint (tateGen g) S') := by
  have D {c} (t : tateModule g c) : ℓ • t.1.comp (.mulRight ℓ⁻¹) = t.1 := by
    ext; simp [← map_nsmul, mul_left_comm]
  refine LocalIso.isCohomEquiv ⟨fun c (s : S' c) e ↦ hF fun d f m M ↦ ?_,
    fun c t ↦ t.inductionOn (fun s t ↦ hF fun d f m M ↦ ?_) fun _ _ ↦ add_mem⟩
  all_goals
    let ε := tateGen g c (.of ⟨⟩)
    let ψ := (algebraMap _ (Localization.AtPrime m)).comp ((ringOf g).map f.1).1
    let x := (restrictRootsOfUnity ψ ℓ).toAdditive.comp (.mk' (fun t ↦ ⟨(t.1 (1 / ℓ)).1,
      congr($(congr($(D t) 1).trans t.2).1)⟩) (by tauto))
    let φ := ψ.comp (algebraMap A (g c).1)
    rcases NeZero.mk (map_natCast φ ℓ ▸ (u.3.map φ).ne_zero),
      (IsTest.exists_valuationSubring_atPrime (by exact (g d).2) m).1
    have h : IsPrimitiveRoot (x ε).1 ℓ := .coe_units_iff.1 (isRoot_cyclotomic_iff.1 (by
      simpa only [ε, tateGen, freeAb.desc_of] using
        map_cyclotomic ℓ φ ▸ cyclotomicRootSystem.2.2.map))
  · obtain ⟨_, l⟩ := AddCommGroup.zmodModule (hS c), (h.zpowers_eq ▸ h.zmodEquivZPowers).symm
    use 1, m.one_notMem, fun _ _ _ ↦ (smul_eq_zero_iff_right (l.map_ne_zero_iff.2 (h.ne_one
      Fact.out congr($(·).1)))).1 (congrArg (TensorProduct.lift ((l.toAddMonoidHom.comp
      x).toIntLinearMap.smulRight 1).flip) e : _ • s = 0) ▸ map_zero (S'.2 _).1
  exact (h.zpowers_eq.ge (x t).2).elim fun i e ↦ (Localization.isLocalization.exists_of_eq (.trans
    congr($(x.sub_mem_ker_iff.2 ((x.map_zsmul ..).trans (Subtype.ext e)).symm).1.1) (map_one
    _).symm)).elim fun a k ↦ ⟨a, a.2, fun _ _ w ↦ (congrArg ((abCoker _).map _)
    (QuotientAddGroup.eq_iff_sub_mem.2 ⟨i • s, (by simp [tmul_sub]; rfl : _ = _ - s ⊗ₜ (t - i •
    ε))⟩)).trans (congrArg _ ((congrArg (_ ⊗ₜ ·) (Subtype.ext (D _).symm : _ = ℓ • ⟨_, Gm.ext.2 (by
    erw [((ringOf g).map_comp_apply ..).congr_left, ← w.mul_eq_left, ← map_mul, k,
      mul_one])⟩)).trans (by rw [← smul_tmul, hS, zero_tmul])))⟩

/-- The action of the Tate module T on a coefficient M: the class in Ext⁰(M⊗T, M) whose
pull-back along x ↦ x⊗ε, ε = `tateGen`, is the identity. -/
def TorsionCoeff.tateAction (M : TorsionCoeff g) :=
  Function.surjInv (isCohomEquiv_tateGen M.killed M.zariski_descent 0).2 (.mk₀ (𝟙 _))

variable {C'} [Category C'] (K : TorsionCoeff g) (φ : C' ⥤ C) (M' : TorsionCoeff (φ ⋙ g)) (T :
  TotalH (φ ⋙ K.F) M'.F) [HasFlatValues F]

lemma TorsionCoeff.tateGen_comp_tateAction y : pullbackAlong (tensorPoint (tateGen g) S') (.comp
  (.map _ y) K.tateAction.toTotalH) = y := by erw [← TotalH.comp_assoc_of_sq (y.naturality _),
  y.map_id, homClass_comp_of, Function.surjInv_eq (f := H.map ..), y.comp_id]

/-- For coefficients K along g and M' along g∘φ, every class T in total Ext(K∘φ, M') commutes
with the actions `TorsionCoeff.tateAction` of the Tate module: T∘μ_K = μ_{M'}∘(T⊗1). -/
lemma TorsionCoeff.tateAction_comm : mapThenComp (restrictAlong φ) T K.tateAction.toTotalH =
  .comp (.map _ T) M'.tateAction.toTotalH := (isCohomEquiv_tateGen (S' := φ ⋙ _)
  (fun _ ↦ K.killed _) M'.zariski_descent).bijective_totalH.1 (by simpa only [map_comp_assoc,
  map_homClass, id_comp, tateGen_comp_tateAction, CategoryTheory.Functor.map_id] using!
  congr((TotalH.map (restrictAlong φ) $(K.tateGen_comp_tateAction (.homClass (𝟙 _)))).comp T))

/-- For S flat, ξ in total Ext(P, T), T the Tate module: y ↦ y·ξ from total Ext(S, M) to Ext(S ⊗
P, M), composing S ⊗ ξ, y ⊗ T, `TorsionCoeff.tateAction`. -/
def TorsionCoeff.mulClass {S P : AbFunctor C} (M : TorsionCoeff g) [HasFlatValues S] (ξ : TotalH P
  _) := (ξ.map (abTensor S)).comp.comp (mapThenComp (abTensor.flip _) M.tateAction.toTotalH)

lemma TorsionCoeff.mulClass_naturality {C C'} [Category C] [Category C'] {ℓ A} [CommRing A] {g :
  C ⥤ TestOver A} [u : InvertsPrime A ℓ] {S P : AbFunctor C} (K : TorsionCoeff g) (φ : C' ⥤ C) (M' :
  TorsionCoeff (φ ⋙ g)) (T : TotalH (φ ⋙ K.F) M'.F) [HasFlatValues S] ξ y : mapThenComp
  (restrictAlong φ) T (K.mulClass ξ y) = M'.mulClass (S := φ ⋙ S) (P := φ ⋙ P) (.map (restrictAlong
  φ) ξ) (mapThenComp (restrictAlong φ) T y) := .trans (by erw [map_comp_assoc, map_comp_assoc,
  K.tateAction_comm, TotalH.map_map, TotalH.map_map (abTensor.flip _),
  ξ.map_map (restrictAlong φ) _, TotalH.map_map (restrictAlong φ)]; rfl)
  (congrArg _ (map_comp_assoc ..)).symm

/-- Let ξ be a class in H² with values in the Tate module, relative to the locus where J is the
unit ideal. If a, a': S' → S (S, S' flat) agree wherever J_c = 0, then (a^*y)·ξ = (a'⊗1)^*(y·ξ)
for every class y. -/
lemma Theory.mulClass_congr_of_eq_on_zeros {S S' : AbFunctor C} [HasFlatValues S] [HasFlatValues S']
  (Θ : Theory g) (J : IdealFamily (ringOf g)) (ξ : H (relFreeAb J.topLocus) _ 2)
  {a a' : S' ⟶ S} (h : ∀ c, J.I c = ⊥ → a c = a' c) y : Θ.mulClass ξ.toTotalH (pullbackAlong a y) =
  pullbackAlong (abTensor.map a' _) (Θ.mulClass ξ.toTotalH y) :=
  have r {N} [HasFlatValues N] ξ : ∃ w, ∀ S [HasFlatValues S] z, (z.map (abTensor.flip N)).comp w =
    Θ.mulClass (S := S) (.of _ 2 ξ) z := (exists_tensor_class ξ).imp' _ fun _ k S _ z ↦ by
    erw [comp_assoc_of_sq ((k C (𝟭 C) S).1 ..), (k ..).2.1, TotalH.map_id]; rfl
  have ⟨w, r⟩ := (isCohomEquiv_quotient_of_acyclic ((kerComplex_shortExact fun _ ↦
    Quot.mk_surjective).map_of_exact (abTensor.flip _)) (cohomology_eq_zero_of_locallyZero fun c t ↦
    t.induction_on (by simp) (fun s p ↦ (Θ.zariski_descent (Θ.isLocallyEverything_ker_toZerosCoeff
    J)).of_preimage_le (pointMap s) fun b f ↦ Or.rec (congr($(·) ⊗ₜ _).trans (by simp))
    fun q ↦ congr(_ ⊗ₜ $(relFreeAb.mem_of_mk_mem ⊥ (fun _ ↦ relFreeAb.mk_eq_zero q) _)).trans
    (by simp)) fun _ _ ↦ add_mem)).bijective_totalH.2.exists.1 (r ξ)
  by simpa only [← r, map_comp_assoc, map_homClass] using! congr(TotalH.comp (.map (abTensor.flip
    _) $(((Θ.isCohomDense_botLocus J).isCohomEquiv_of_bijective_on
    fun c k ↦ (Equiv.subtypeUnivEquiv (by simp [h c k])).bijective).bijective_totalH.1
    (((homClass_comp_homClass_comp ..).congr (homClass_comp_homClass_comp ..)).2 (congrArg
    ((y.comp (.homClass _)).pullbackAlong ·) (sub_eq_zero.1 (kerComplex (a - a')).zero))))) w)

/-- The equivalence relation (1 + uv)v' = v(1 + u'v') on pairs (u, v) in B × B: equality of the
points (1 + uv : v) of the projective line. -/
def projLineSetoid B [CommRing.{0} B] : Setoid (B × B) :=
    ⟨fun x y ↦ (1 + x.1 * x.2) * y.2 = x.2 * (1 + y.1 * y.2), by grind [Equivalence.mk]⟩

/-- The projective line as a functor on rings: B goes to the set of points (1 + uv : v) with u,
v in B, that is, pairs (u, v) modulo `projLineSetoid`. -/
def projLine : PointFunctor := by refine ⟨(ULift <| Quotient <| projLineSetoid ·),
  fun f ↦ ↾(⟨·.1.map (.map f.hom f.hom) fun
  _ _ (h : _ = _) ↦ by simpa using! congr(f $h)⟩), ?_, ?_⟩ <;> intros <;> ext ⟨⟨⟩⟩ <;> rfl

variable (g : C ⥤ TestOver A) {B B'} (f : B ⟶ B') (q : projLine B) (x :
  B) {A' : Type} [CommRing A']

/-- The ι-fold power of the projective line `projLine`: the functor sending a ring B to
the families of points of P¹(B) indexed by ι. -/
def projLinePow (ι : Type) : PointFunctor := .mk (ι → projLine ·) fun f ↦ ↾(projLine.map f <| · ·)

/-- For a functor of points X, the projection (c, x) ↦ c from pairs of a test c over A and x ∈
X(c) to tests over A. -/
abbrev testOfPoint A [CommRing A] X := elementsProj (ringOf (𝟭 (TestOver A)) ⋙ X) ⋙ 𝟭 _

/-- The projective line along g: the set-valued functor on C sending c to P¹(g(c)), with P¹ the
functor `projLine` on rings. -/
abbrev projLineAlong := ringOf g ⋙ projLine

/-- For a point q of P¹(B) with chosen representing pair (u, v), its row (1 + uv, v) in B × B of
homogeneous coordinates. -/
def projLine.unimodularRow := (1 + q.1.out.1 * q.1.out.2, q.1.out.2)

/-- For a pair x = (u, v) in a commutative ring B, the row (1 + uv, v) is a unit of B times the
chosen row `projLine.unimodularRow` of the point of P¹(B) represented by x. -/
lemma projLine.exists_unit_smul_unimodularRow (x : B × B) : ∃ ε : Bˣ, (1 + x.1 * x.2, x.2) =
  ε.1 • unimodularRow ⟨⟦x⟧⟩ :=
  have ⟨y, _, (_ : _ = _)⟩ := exists_eq_left'.2 ((projLineSetoid B).symm' (Quotient.mk_out x))
  by use ⟨1 + (x - y).1 * x.2, 1 + (y - x).1 * y.2, ?_, ?_⟩ <;> simp [unimodularRow] <;> grind

lemma projLine.smul_unimodularRow_inj {q q'} {a b : Bˣ} (h : a.1 • @unimodularRow B q =
  b.1 • unimodularRow q') : a = b ∧ q = q' := by
  simp [unimodularRow] at h
  grind [Units.ext, @ULift.ext _ q q' (Quotient.out_equiv_out.1 (a.mul_right_inj.1 (by grind)))]

/-- For f: B → B' and q in P¹(B), a chosen unit ε of B' such that the image under f of the row
of q is ε times the row of f(q). -/
def projLine.rowUnit := @FreeAbelianGroup.lift _ (Gm B') _ fun q :
    projLine B ↦ ⟨(exists_unit_smul_unimodularRow (q.1.out.map f f)).choose⟩

lemma projLine.unimodularRow_map : (unimodularRow q).map f f = (rowUnit f (.of q)).1.toMul.1 •
  unimodularRow (projLine.map f q) := by erw [lift_apply_of, ← congr(projLine.map f
  ⟨$(q.1.out_eq)⟩), ← (exists_unit_smul_unimodularRow _).choose_spec]; simp [unimodularRow]

lemma projLine.add_rowUnit_eq {q' a b} (k : (a.1 • unimodularRow q).map f f =
  b.1 • unimodularRow q') : Gm.map f ⟨a⟩ + rowUnit f (.of q) = ⟨b⟩ :=
  congrArg _ (smul_unimodularRow_inj (by erw [mul_smul, ← unimodularRow_map, ← k]; simp!; tauto)).1

/-- The point (x : 1) of the projective line over B. -/
def projLine.affinePt : projLine B := ⟨⟦(x - 1, 1)⟧⟩

lemma projLine.map_affinePt : projLine.map f (affinePt x) =
  affinePt (f x) := by simp [affinePt, projLine]

lemma projLine.isUnit_unimodularRow_affinePt_iff {x : B} : IsUnit (unimodularRow (affinePt x)).1 ↔
  IsUnit x := have ⟨_, k⟩ := exists_unit_smul_unimodularRow (x - 1, 1)
  by simpa using! congr(IsUnit $k.1).symm

lemma projLine.affinePt_injective : (@affinePt B).Injective :=
  fun _ _ ↦ by simp [affinePt, projLine, projLineSetoid, Quotient.eq]

lemma projLine.affinePt_eq_map x (h : f (unimodularRow q).1 = f (unimodularRow q).2 * x) : affinePt
  x = projLine.map f q := congr(⟨$(q.1.out_eq ▸ Quot.sound (by grind [unimodularRow] : _ = _))⟩)

lemma projLine.isUnit_unimodularRow_map (h : IsUnit (f (unimodularRow q).1)) : IsUnit (unimodularRow
  (projLine.map f q)).1 := (IsUnit.mul_iff.1 (congr($(unimodularRow_map ..).1).subst h)).2

/-- The subfunctor of the projective line of points whose row has a unit as first coordinate:
the complement of (0 : 1). -/
def projLine.affineChart : Subfunctor projLine :=
  ⟨fun _ ↦ {q | IsUnit (unimodularRow q).1}, (isUnit_unimodularRow_map · · ∘ .map _)⟩

/-- The section of the projective line along g whose value at every object c is the base point
(1 : 1) over the ring g(c). -/
def projLine.basePt : (projLineAlong g).sections :=
  ⟨fun _ ↦ affinePt 1, fun _ ↦ by simp [map_affinePt]⟩

/-- The 1-cocycle from ℤ[P¹] to G_m along g sending a morphism f and a point q to the transition
unit `projLine.rowUnit` of the chosen rows. -/
def projLine.cocycle : Cocycle (freeAb (projLineAlong g)) (ringOf g ⋙ Gm) :=
  ⟨(ofHom <| rowUnit <| (ringOf g).map ·), by intros; ext : 2; exact
  (add_rowUnit_eq _ _ (by erw [← unimodularRow_map, ← unimodularRow_map]; simp!)).symm⟩

/-- The class η in Ext²(ℤ[P¹], T) along g, T the Tate module of G_m: the Yoneda product of the
class of the cocycle of O(1) and the Kummer class. -/
@[irreducible] def etaClass : H (freeAb (projLineAlong g)) (tateModule g) 2 :=
  (projLine.cocycle g).shortExact_extension.extClass.comp (shortExact_kummerSeq _).extClass rfl

/-- A chosen family of classes S ⊗ η in Ext²(S ⊗ ℤ[P¹], S ⊗ T), for all S and all functors to
tests over A, with the compatibilities of `exists_tensor_class`. -/
abbrev TorsionCoeff.etaTensor :=
  Classical.indefiniteDescription _ (exists_tensor_class (etaClass (𝟭 (TestOver A))))

/-- The family `TorsionCoeff.etaTensor` along g: for each S, the chosen class S ⊗ η in
Ext²(S ⊗ ℤ[P¹], S ⊗ T), with T the Tate module `tateModule`. -/
def etaHomClass := TorsionCoeff.etaTensor.1 C g

variable {g : C ⥤ TestOver A} {Y : C ⥤ Type 1} (M : TorsionCoeff g)

/-- For a section q of a set-valued functor Y, the morphism from the constant functor ℤ = ℤ[pt]
to ℤ[Y] sending the generator at c to [q(c)]. -/
abbrev freeAbSectionMap (q : Y.sections) := freeAb.map (sectionMap q)

lemma map_restrictAlong_etaClass {C C'} [Category C] [Category C'] {A} [CommRing A] {g :
  C ⥤ TestOver A} (φ : C' ⥤ C) : TotalH.map (restrictAlong φ) (etaClass g).toTotalH =
  (etaClass (φ ⋙ g)).toTotalH := by simp -dsimp [etaClass]; rfl

lemma map_etaClass_eq_zero_of_coboundary (b : freeAb Y ⟶ _) (u : ∀ _ _, _) (h : ∀ c d f x,
  (_ ⋙ Gm).map f (u c x) = (projLine.cocycle g).component f (b c (.of x)) + u d (Y.map f x)) :
  H.map _ b 2 (etaClass g) = 0 := (freeAb.hom_ext (by aesop) : b = freeAb.desc (fun c x ↦
  (-u c x, b c (.of x))) (by intros; simp_all [Cocycle.extension]; exact (b.naturality_apply
  _ (.of _))) ≫ (projLine.cocycle g).extension.g) ▸ by simp [etaClass, ↓H.map_comp, H.map]

lemma comp_etaClass_eq_zero_of_isUnit (b : Y ⟶ projLineAlong g) (h : ∀ c x,
  IsUnit (projLine.unimodularRow (b c x)).1) :
  pullbackAlong (freeAb.map b) (etaClass g).toTotalH = 0 := by rw [homClass_comp_of,
  map_etaClass_eq_zero_of_coboundary _ (⟨h · · |>.unit⟩) fun _ _ _ _ ↦ Gm.ext.2
  (congr($(projLine.unimodularRow_map ..).1).trans (b.naturality_apply .. ▸ rfl)), map_zero]

/-- For sections q, q' of P¹ along g there are compatible ideals J_c, with q = q' wherever J_c =
0, such that q^*η + q'^*η (η = `etaClass`) comes from H² relative to the locus where
J is the unit ideal. -/
lemma exists_etaClass_supported_diagonal (q q' : (projLineAlong g).sections) : ∃ J : IdealFamily
  (ringOf g), (∀ c, J.I c = ⊥ → q.1 c = q'.1 c) ∧ ∃ ξ, pullbackAlong (relFreeAb.π J.topLocus)
  (.of _ 2 ξ) = pullbackAlong (freeAbSectionMap q + freeAbSectionMap q') (etaClass g).toTotalH :=
  let D c :=
    (· - ·).uncurry (projLine.unimodularRow (q.1 c) * (projLine.unimodularRow (q'.1 c)).swap)
  have h c d f : (ringOf g).map f (D c) =
    ((projLine.cocycle g).component f (.of (q.1 c) + .of (q'.1 c))).1.1 * D d := by
    have := projLine.unimodularRow_map ((ringOf g).map f)
    simp_all -dsimp [D, Function.uncurry, Prod.ext_iff, ← q.2 f, ← q'.2 f]
    exact .trans (by ring!) (mul_rotate ..)
  ⟨⟨(span {D ·}), by simp_all [span_singleton_mul_left_unit]⟩, fun _ k ↦
    congr(⟨$(Quotient.out_equiv_out.1 (sub_eq_zero.1 (span_singleton_eq_bot.1 k)))⟩), .imp
    (by simp [homClass_comp_of]; tauto) (((LongExactSeq.contravariant (relFreeAb.shortExact _).2
    _).exact_f_g 2 _).1 ((H.map_comp ..).symm.trans (map_etaClass_eq_zero_of_coboundary _ (fun _ x ↦
    ⟨(span_singleton_eq_top.1 x.2).unit⟩) (by simp [Gm.ext]; tauto))))⟩

/-- The homomorphism sending b: ℤ[pt] → ℤ[P¹] to the class in Ext²(M, M) given by M ⊗ b, then M
⊗ η, then the action `TorsionCoeff.tateAction` of the Tate module. -/
@[irreducible] def TorsionCoeff.etaAt (M : TorsionCoeff g) :
  (freeAb (pointFunctor C) ⟶ freeAb (projLineAlong g)) →+ H M.F M.F 2 := .mk'
  (fun b ↦ H.map _ (tensorPoint b _) 2 ((etaHomClass g _).comp M.tateAction rfl)) fun a b ↦ by
  simp [H.map, ← Ext.add_comp, ← Ext.mk₀_add]; congr; ext; apply tmul_add

lemma TorsionCoeff.comp_etaAt b y : TotalH.comp y (M.etaAt b).toTotalH = pullbackAlong
  (tensorPoint b S') (TotalH.comp (etaHomClass g S').toTotalH (mapThenComp (abTensor.flip _)
  M.tateAction.toTotalH y)) := by erw [etaAt, ← TotalH.comp_assoc_of_sq ((etaTensor.2 ..).1 ..),
  ← TotalH.comp_assoc_of_sq (y.naturality _), y.map_id, comp_of, homClass_comp_of]; rfl

lemma TorsionCoeff.etaAt_naturality (M' : TorsionCoeff (φ ⋙ g)) (T : TotalH (φ ⋙ M.F) M'.F) b :
    mapThenComp (restrictAlong φ) T (M.etaAt b).toTotalH =
  TotalH.comp T (M'.etaAt (φ.whiskerLeft b)).toTotalH := by
  erw [comp_etaAt, ← M.tateAction_comm φ, etaAt, Ext.toTotalH, ← homClass_comp_of, ← comp_of,
    map_comp_assoc, map_comp_assoc, map_homClass, (etaTensor.2 ..).2.2]; rfl

variable {A : Type} [CommRing A] {g : C ⥤ TestOver A} {S : AbFunctor C} [InvertsPrime A ℓ] (M :
  TorsionCoeff g) [HasFlatValues S] {P : AbFunctor C}

lemma TorsionCoeff.mulClass_eq_comp_etaAt (ξ : TotalH P _) ρ {b} (e : pullbackAlong ρ ξ =
  pullbackAlong b (etaClass g).toTotalH) y :
  pullbackAlong (tensorPoint ρ S) (M.mulClass ξ y) = TotalH.comp y (M.etaAt b).toTotalH := by
  erw [comp_etaAt, (etaTensor.2 ..).2.1, map_restrictAlong_etaClass, TotalH.map_of]
  simpa [mulClass, map_comp_assoc,
    homClass_comp_homClass_comp] using! congr(pullbackAlong (tensorPoint (𝟙 _) S) (M.mulClass $e y))

lemma TorsionCoeff.comp_etaAt_basePt y :
  TotalH.comp (M := S) y (M.etaAt (freeAbSectionMap (projLine.basePt g))).toTotalH = 0 := by
  rw [← M.mulClass_eq_comp_etaAt _ _ id_comp, comp_etaClass_eq_zero_of_isUnit] <;> simp -dsimp
    [mulClass, projLine.basePt, sectionMap, projLine.isUnit_unimodularRow_affinePt_iff]

/-- On the category of points of P¹ along g, the class in Ext²(M, M) of multiplication by η =
`etaClass` at the tautological point. -/
abbrev TorsionCoeff.cupClass := M.onElements.etaAt (freeAb.map (tautSection (X := projLineAlong g)))

/-- The two self-Ext classes of M pulled back to the category of points of P¹: the identity in
degree 0 and the operator η of the tautological section in degree 2. -/
def TorsionCoeff.lineBasis i : H (restrictAlong (elementsProj _) M.F)
  (elementsProj (projLineAlong g) ⋙ M.F) (cond i 0 2) := i.rec M.cupClass (.mk₀ (𝟙 _))

/-- The projective line formula for M: for every S, the map (a, b) ↦ a + ηb from two copies of
total Ext(S, M) to total Ext of the pull-backs to P¹ is bijective. -/
def TorsionCoeff.HasLineFormula := ∀ S, IsLerayHirschBasis M.lineBasis S

lemma TorsionCoeff.map_etaAt_onElements X b : TotalH.map (restrictAlong (elementsProj X))
  (M.etaAt b).toTotalH = (M.onElements.etaAt ((elementsProj X).whiskerLeft b)).toTotalH :=
  (comp_id.congr id_comp).1 (etaAt_naturality _ _ (.onElements _) ..)
