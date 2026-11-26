import GRH.Lib.Cohomology.Etale.Functoriality
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Half of the holomorphic Lefschetz (Woods Hole) formula for h-forms and correspondences
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Functor of points on k-algebras; module-valued coefficient functors with scalar action.
Global functions on the projective line are constants (polynomials in X and 1/X). Points, tangent
polynomial at a coincidence, null local terms, congruence relation, Galois coverings. -/

open AlgebraicGeometry CategoryTheory Polynomial LaurentPolynomial CommAlgCat TrivSqZeroExt Module
variable {k} [CommRing.{0} k] {C} [Category.{0,1} C] (F : C ⥤ ModuleCat k)

/-- A functor F from C to k-modules, regarded as a functor to abelian groups, so that it can
serve as the coefficients of cohomology. -/
def moduleCoeff := liftCoeff (F ⋙ forget₂ ..)

instance : CoeffAction k (moduleCoeff F) := ⟨.comp ⟨((Functor.whiskeringRight ..)
    (forget₂ .. ⋙ AddCommGrpCat.uliftFunctor)).mapEnd F, rfl, by tauto⟩ (algebraMap ..)⟩

/-- The category of (small) commutative algebras over a commutative ring k. -/
abbrev CommAlg k [CommRing k] := CommAlgCat.{0,0} k

/-- For k-algebras A and T, a ring homomorphism f: A → T compatible with the structure maps from
k, viewed as a morphism of k-algebras. -/
abbrev CommAlg.homOfRingHom {A T : CommAlg k} f e := (ConcreteCategory.ofHom ⟨f, e⟩ : A ⟶ T)

variable (k k') [CommRing.{0} k'] [Algebra k k'] (R : CommRingCat.{0}) [Algebra R k]

/-- Restriction of scalars along k → k': the functor regarding a commutative k'-algebra as a
k-algebra. -/
def restrictAlg : CommAlg k' ⥤ CommAlg k := .mk (id (@.of _ _ · _ {Algebra.restrictScalars .. with
  smul := (algebraMap k k' · • ·)})) (@id _ fun f ↦ CommAlg.homOfRingHom _ fun _ ↦ f.1.2 _)

/-- For an R-algebra k, the contravariant functor from commutative k-algebras to schemes over
Spec R sending A to Spec A, with structure map given by R → k → A. -/
noncomputable def specAlg : CommAlg k ⥤ (Over (Spec R))ᵒᵖ := { restrictAlg .. ⋙
  (algSpec R).rightOp with obj A := ⟨.mk (Spec.map (CommRingCat.ofHom ((algebraMap k A).comp _)))⟩ }

/-- For an R-algebra k, the functor sending a scheme X over Spec R to its functor of points A ↦
X(A) on commutative k-algebras A. -/
noncomputable def algPoints := uliftYoneda.{1} ⋙ restrictAlong (specAlg k R)

/-- For an R-algebra k and a scheme X over Spec R, the functor sending a commutative k-algebra A
to the set X(A) of morphisms Spec A → X over Spec R. -/
noncomputable abbrev algPointsOf := (algPoints k R).obj

/-- If polynomials P, Q over k satisfy P(T) = Q(T⁻¹) as Laurent polynomials, then P and Q are
the same constant; this is the statement H⁰(ℙ¹, 𝒪) = k. -/
lemma eq_C_of_toLaurent_eq {k : Type} [CommRing k] (P Q : k[X]) (h : toLaurent P =
    invert Q.toLaurent) : ∃ c, (P, Q) = (.C c, .C c) := have := congr(trunc $(Q.as_sum_range ▸ h))
  by simp_all [← invert.symm_apply_eq, ← Q.toLaurent_inj]

variable {k M : Type} [CommRing k] [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k
  M] {R : CommRingCat} [Algebra R k] {Z W : Over (Spec R)} {A B : CommAlg k} (c : W ⟶ Z)

lemma fst_surjective_and_kerIdeal_sq : (@fst k M).Surjective ∧ kerIdeal k M ^ 2 = ⊥ :=
  ⟨fst_surjective, by simp⟩

/-- The k-algebra homomorphism k ⊕ M → k from the trivial square-zero extension, sending (a, m)
to a. -/
def SqZeroExt.fst := ofHom (fstHom k k M)

/-- The points X(A) of a scheme X over Spec R with values in the k-algebra A, that is, the
morphisms Spec A → X over Spec R. -/
abbrev PointsIn X A := algPointsOf k R X A

/-- For a k-algebra homomorphism φ: A → B and a point y in W(A), the point in W(B) obtained by
composing y with Spec φ. -/
noncomputable abbrev PointsIn.map (φ : A ⟶ B) : PointsIn W A → PointsIn W B :=
  (algPointsOf ..).map φ

/-- For some finitely generated k-module T of rank d, v in W(k ⊕ T^*) over y and A in End T: on
the points v(x) of W(k[ε]), x in T, x ↦ c(v(x)) is injective, u(v(x)) = c(v(Ax)), and P(t) =
P(0) det(1 − tA) on k. -/
def IsTangentPoly {W Z : CommAlg k ⥤ Type 1} d (c u : W ⟶ Z) y P := ∃ᵉ (T : FGModuleCat k) (v)
  (A : End k T), let f x := W.map (ofHom (TrivSqZeroExt.map (Dual.eval k T x))) v
  finrank k T = d ∧ W.map SqZeroExt.fst v = y ∧ (c _ ∘ f).Injective ∧
    (∀ φ, u _ (f φ) = c _ (f (A φ))) ∧ ∀ t, Polynomial.eval t P = P.eval 0 * (1 - t • A).det

/-- ∑ a_i[u_i] is h-null: for all c, P, if each coincidence c(y) = u_i(y), y ∈ W(k), a_i ≠ 0,
has d-dimensional tangent polynomial P (`IsTangentPoly`), P(1) ≠ 0, they are finitely
many and ∑ a_i[z^h]P/P(1) = 0. -/
def IsNullFamily {k I : Type} [Field k] [Algebra R k] (u : I → (W ⟶ Z)) (a : I →₀ k) d h := ∀ c,
  let S := {y : Σ _ : a.support, PointsIn .. | y.2.1 ≫ c = y.2.1 ≫ u y.1}; ∀ P : _ → _, (∀ y ∈ S,
    IsTangentPoly d ((algPoints k R).map c) ((algPoints ..).map (u y.1)) y.2 (P y) ∧
    (P y).eval 1 ≠ 0) → S.Finite ∧ ∑ᶠ y ∈ S, a y.1 * (P y).coeff h / (P y).eval 1 = 0

/-- Congruence relation: ∑ mᵢ [Frob_p^(aᵢ) uᵢ(x)] = 0 as a formal sum, for every field k of
characteristic p and every k-point x of W killing 𝔭. -/
def CongruenceRelation {I} [Fintype I] m (𝔭 : Set R) p [Fact (Nat.Prime p)] (a : I → ℕ) (u : _ →
  (W ⟶ Z)) := ∀ k [Field k] [CharP k p] x, (∀ r ∈ 𝔭, (Spec.preimage (x ≫ W.hom)).hom r = 0) →
  Cancels m fun i ↦ Spec.map (CommRingCat.ofHom (iterateFrobenius k p (a i))) ≫ x ≫ (u i).left

/-- A covering: the finite group Δ acts on W over c: W → Z, c is surjective, and two points of W
in a field of characteristic 0 with the same image under c differ by exactly one element of
Δ. -/
structure IsGaloisCovering {Δ : FiniteGrp.{0}} (a : Δ →* End W) where
  comp_eq δ : (a δ).asHom ≫ c = c
  onto_geometric : Surjective c.left
  torsor k [Field k] [CharZero k] (x y : Spec ⟨k⟩ ⟶ _) : x ≫ c.1 = y ≫ c.1 → ∃! g,
    x ≫ (a g).asHom.1 = y
