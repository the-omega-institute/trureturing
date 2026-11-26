import GRH.Lib.General.LinearAlgebra.Base
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Cohomology as Ext of presheaves: equivalences, dense subfunctors, comparisons, fibre
powers, additivity. -/

noncomputable section

open CategoryTheory Functor AddCommGrpCat AddMonoidHom Function Abelian Ext FreeAbelianGroup



variable (C) {C'} [Category.{0,1} C] [Category.{0,1} C'] {D T : Type*} [Category* D] [Category* T]

/-- A functor is applied to an object. -/
instance : CoeFun (D ⥤ T) fun _ ↦ D → T := ⟨obj⟩

/-- A map of functors is applied to an object. -/
instance {F G : D ⥤ T} : CoeFun (F ⟶ G) fun _ ↦ ∀ A, F A ⟶ G A := ⟨(·.app)⟩

/-- A subfunctor is applied to an object. -/
instance {F : D ⥤ _} : CoeFun (Subfunctor F) fun _ ↦ ∀ A, Set (F A) := ⟨(·.obj)⟩

/-- The category of covariant functors from C to abelian groups. -/
abbrev AbFunctor := C ⥤ AddCommGrpCat.{1}

/-- The assertion that Ext groups in the category of functors from C to abelian groups exist,
with values in a larger universe. -/
@[reducible] def HasH := HasExt.{2} (AbFunctor C)

variable {C} {Y E : D ⥤ Type 1} (p : E ⟶ Y) {J : Type 1} (X : J → C ⥤ Type 1)

/-- For p: E → Y, the (m+1)-fold fibre power of E over Y: tuples of m+1 points of E(A) with the
same image in Y(A). -/
def cech m := mk ({e : Fin (m + 1) → _ // ∀ i j, p.app · (e i) = p _ (e j)})
  fun f ↦ ↾fun e ↦ ⟨(E.map f <| e.1 ·), by simp; grind⟩

/-- The projection from the (m+1)-fold fibre power of p: E → Y to E taking the j-th coordinate. -/
def cech.proj m (j : Fin (m + 1)) : cech p m ⟶ E where app _ := ↾(·.1 j)

/-- For a family X_i of set-valued functors on C, the functor sending A to the disjoint union of
the X_i(A). -/
def sigma := mk (Σ i, X i ·) fun f ↦ ↾(⟨_, (X _).map f ·.2⟩)

/-- The inclusion of X_i into the disjoint union of the family of functors X. -/
def sigma.ι i : X i ⟶ sigma X where app _ := ↾(⟨i, ·⟩)

variable {Y E W : C ⥤ Type 1} (ι : C ⥤ CommRingCat.{0}) (R) [Ring R] (N F G : AbFunctor C) (n : ℕ)
  (U : Subfunctor Y) (φ : C' ⥤ C) (u : W ⟶ Y) (p : E ⟶ Y)

instance : HasH C := .standard _

/-- The group Ext^n(N,F) in the category of functors from C to abelian groups; for N = Z[Y] it
is the cohomology H^n(Y,F). -/
abbrev H := Ext N F n

/-- The functor sending a set-valued functor Y on C to Z[Y], whose value at A is the free
abelian group on Y(A). -/
def freeAb : (D ⥤ Type 1) ⥤ D ⥤ Ab.{1} := (whiskeringRight ..) free

/-- A functor from C to small abelian groups, regarded as taking values in abelian groups of the
next universe. -/
def liftCoeff (F : C ⥤ Ab.{0}) : AbFunctor C := F ⋙ uliftFunctor

/-- The contravariant functor sending an object A of C to the set-valued functor h_A = Hom(A,−),
lifted to the next universe. -/
def reprFunctor := @uliftCoyoneda.{1} C _

/-- The functor h_A = Hom(A,−) represented by the object A. -/
abbrev reprBy (A : C) := reprFunctor ⟨A⟩

/-- For a morphism f: A → B of C, the map h_B → h_A of representable functors h_A = Hom(A,−)
given by precomposition with f. -/
abbrev reprMap {A B : C} (f : A ⟶ B) := reprFunctor.map f.op

/-- For a functor φ: C' → C and any category D, the restriction functor N ↦ N∘φ from functors C
→ D to functors C' → D. -/
abbrev restrictAlong : (C ⥤ D) ⥤ C' ⥤ D := (whiskeringLeft ..) φ

/-- For α: N' → N, the homomorphism Ext^n(N,F) → Ext^n(N',F) given by precomposition with α. -/
def H.map {N N'} F (α : N' ⟶ N) n : @H C _ N F n →+ H N' F n := (mk₀ α).precomp F n.zero_add

/-- For β: F → F', the homomorphism Ext^n(N,F) → Ext^n(N,F') given by postcomposition with β. -/
def H.push {F F'} (β : F ⟶ F') n : H N F n →+ H N F' n := (mk₀ β).postcomp N rfl

/-- The additive map sending a morphism β: F → G to the induced homomorphism Ext^n(N,F) →
Ext^n(N,G). -/
def H.pushHom := mk' (@push _ _ N F G · n) (by simp [push, mk₀_add])

/-- An action of the ring R on the functor F, that is, a ring homomorphism from R to the
endomorphism ring of F. -/
class CoeffAction where act : R →+* End F

instance [CoeffAction R F] n : Module R (H N F n) := (ModuleCat.mkOfSMul (.comp
  (.mk' ((extFunctorObj N n).mapEnd F) fun _ _ ↦ End.ext (extFunctorObj N n).map_add)
    CoeffAction.act)).isModule

/-- α: N' → N is an equivalence for F: the pull-back Ext^n(N,F) → Ext^n(N',F) is bijective for
every n. -/
def IsCohomEquiv {N N'} α := ∀ n, Bijective (@H.map C _ N N' F α n)

/-- A comparison from F on C to F' on C': a functor φ: C' → C with a natural transformation β:
F∘φ → F'. -/
structure Comparison (F' : AbFunctor C') where of :: (φ) coeffHom : φ ⋙ F ⟶ F'

/-- The comparison from F to itself given by the identity functor of C and the identity of F. -/
abbrev Comparison.id := of (𝟭 C) (𝟙 F)

/-- For a comparison (φ,β) and α: N' → N∘φ, the homomorphism Ext^n(N,F) → Ext^n(N',F') obtained
by restricting along φ, pushing by β and pulling by α. -/
def Comparison.pull {F F'} (c : Comparison F F') {N : AbFunctor C} {N' : AbFunctor C'} (α :
  N' ⟶ c.φ ⋙ N) n : H N F n →+
  H N' F' n := (H.map _ α n).comp ((H.push _ c.coeffHom n).comp ((restrictAlong _).mapExtAddHom ..))

/-- The functor sending a natural transformation p between functors D → T to the functor A ↦ p_A
from D to the category of arrows of T. -/
def toArrowFunctor {T} [Category* T] := (evaluation D T ⋙ mapArrowFunctor ..).flip

/-- The functor sending a map p: E → Y of set-valued functors on C to the (m+1)-fold fibre power
of E over Y. -/
def cechFunctor m := toArrowFunctor ⋙ (whiskeringRight C ..) (cech Arrow.leftToRight m)

/-- For u: W → Y and p: E → Y, the fibre product W ×_Y E: pairs in W(A) × E(A) with the same
image in Y(A). -/
def fibreProd := mk ({x // u.app · x.1 = p _ x.2})
  fun f ↦ ↾fun x ↦ ⟨(W.map f x.1.1, E.map f x.1.2), by aesop⟩

/-- The first projection W ×_Y E → W from the fibre product of u: W → Y and p: E → Y. -/
def fibreProd.fst : fibreProd u p ⟶ W where app _ := ↾(·.1.1)

/-- The second projection W ×_Y E → E from the fibre product of u: W → Y and p: E → Y. -/
def fibreProd.snd : fibreProd u p ⟶ E where app _ := ↾(·.1.2)

/-- The map h_A → Y corresponding to a point y of Y(A) by the Yoneda lemma. -/
def pointMap {A} (y : Y A) : reprBy A ⟶ Y := uliftCoyonedaEquiv.symm y

/-- For maps f_i: X_i → Y of set-valued functors, the map from the disjoint union of the X_i to
Y that is f_i on X_i. -/
def sigma.desc {ι X} (f : ∀ i : ι, X i ⟶ Y) : sigma X ⟶ Y :=
  ⟨fun A ↦ ↾(f _ A ·.2), by aesop (add simp sigma)⟩

/-- For a subfunctor U of Y and φ: C' → C, the subfunctor U∘φ of Y∘φ. -/
def CategoryTheory.Subfunctor.whisker : Subfunctor (φ ⋙ Y) := ⟨_, fun _ ↦ U.map _⟩

/-- The subfunctor U of Y is dense for F: for every point h_A → Y, the inclusion of the preimage
of U in h_A is an equivalence for F. -/
def IsCohomDense := ∀ A y, IsCohomEquiv F (freeAb.map (U.preimage (pointMap (A := A) y)).ι)

/-- π: A → B is universal among the morphisms f from A with ι(f)(e) = 0, and ι(π) is surjective
with kernel contained in the ideal (e). -/
def IsIdemQuotient {A B} e π := @ι.map A B π e = 0 ∧ (∀ B' f, @ι.map A B' f e = 0 →
  ∃! g, π ≫ g = f) ∧ Surjective (ι.map π) ∧ RingHom.ker (ι.map π).hom ≤ .span {e}

/-- Each idempotent e ≠ 1 of ι(A) has a `IsIdemQuotient` A → B, and ι(A) ≅ ι(B₁) × ι(B₂) via
maps A → B₁, B₂ implies F(A) ≅ F(B₁) × F(B₂). -/
structure HasPartitions where
  exists_quotient A e : IsIdempotentElem e → e ≠ 1 → ∃ B π, @IsIdemQuotient _ _ ι A B e π
  bijective_prod {A B₁ B₂} π₁ π₂ : Bijective (fun x ↦ (@ι.map A B₁ π₁ x, @ι.map A B₂ π₂ x)) →
    Bijective fun x ↦ (F.map π₁ x, F.map π₂ x)

/-- For every y ∈ Y(A) and maximal ideal m of ι(A), some a ∉ m has: y maps into U along every A
→ B making a invertible. -/
abbrev IsLocallyEverything := ∀ A y m, Ideal.IsMaximal m → ∃ a ∉ m, ∀ B f, IsUnit (@ι.map A B f a) →
  Y.map f y ∈ U B

/-- Zariski descent for F: U ⊂ Y is dense (`IsCohomDense`) if for each y in Y(X) and maximal ideal m
of ι(X), some f ∉ m puts y into U along every X → X' inverting f. -/
def HasZariskiDescent := ∀ ⦃Y U⦄, IsLocallyEverything ι U → @IsCohomDense C _ Y F U

lemma IsLocallyEverything.whisker {ι U} (h : @IsLocallyEverything C _ Y ι U) :
  IsLocallyEverything (φ ⋙ ι) (U.whisker φ) := fun _ ↦ forall₃_imp (by tauto) (h _)

/-- The property of p: E → Y that E(A) → Y(A) is surjective for every object A. -/
def IsPointwiseSurjective := ∀ A, Surjective (p A)

variable {R φ} {ι : Type} (F : ι → AbFunctor C) {I V V'} [Fintype I]

/-- For u: Y' → Y∘φ, the induced map of free abelian group functors Z[Y'] → Z[Y]∘φ. -/
abbrev freeAbMap {Y Y'} (u : Y' ⟶ φ ⋙ Y) : freeAb Y' ⟶ φ ⋙ freeAb Y := freeAb.map u

/-- For f: A → R, R a ring: any a, b in R have an idempotent e of A with a ∣ f(e)b and b ∣ (1 −
f(e))a. -/
def IsComparableRing {A} [Mul A] (f : A → R) :=
  ∀ a b, ∃ e, IsIdempotentElem e ∧ a ∣ f e * b ∧ b ∣ (1 - f e) * a

/-- ∑ m_i h_i = 0 for every family h_i in an abelian group depending only on v_i; equivalently,
the integers m_i sum to zero on every fibre of v. -/
def Cancels (m : I → ℤ) (v : I → V) := ∑ i, m i • of (v i) = 0

lemma Cancels.mono {m v v'} (h : @Cancels I V _ m v) (H : FactorsThrough v' v) : @Cancels I V' _
    m v' := by simpa [(H.comp_left _).extend_apply] using! congr(lift (extend v (of ∘ v') 0) $h)

/-- For a family F_i of abelian-group-valued functors on C, the functor sending A to the product
of the groups F_i(A). -/
def piAbFunctor : AbFunctor C := .mk _ fun f ↦ ofHom (.piMap (F · |>.map f |>.hom))

/-- The projection from the product of the family of functors to its i-th factor F_i. -/
def piAbFunctor.π i : piAbFunctor F ⟶ F i where app _ := ofHom (Pi.evalAddMonoidHom ..)

/-- For a family of maps f_i : A_i → B_i, the assertion that every f_i is bijective. -/
abbrev AllBijective {ι} {A B : ι → Type*} (f : ∀ i, A i → B i) := ∀ i, Bijective (f i)

/-- A natural transformation γ: F → G that is bijective on every object, as an isomorphism F ≅
G; the target is a concrete category whose forgetful functor reflects isomorphisms. -/
abbrev isoOfAppBijective {C} [Category C] {P T} [∀ X Y, FunLike (P X Y) ..] {F G : C ⥤ D}
  [@ConcreteCategory D _ P T _] [(forget D).ReflectsIsomorphisms] (γ : F ⟶ G) (h : AllBijective (γ
  ·)) := @asIso _ _ _ _ γ (by simpa [γ.isIso_iff_isIso_app, ConcreteCategory.isIso_iff_bijective])
