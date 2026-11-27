/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/ValuativeDensity
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/ValuativeDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.ProperBaseChange.ValuativeDensity. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/ProperBaseChange/ValuativeDensity.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.ConnectedComponents
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of commutative and general algebra (textbook or folklore).

Known result: Tilting and untilting for products of perfectoid valuation rings over O_C. Only
products of p-complete absolutely integrally closed valuation rings over O_C are treated here. Such
a ring is recovered from the Witt vectors of its tilt, tilting is fully faithful, and maps from a
perfect algebra to the tilt are maps from its untilt. Source: B. Bhatt, M. Morrow, P. Scholze,
Integral p-adic Hodge theory, Publ. Math. IHES 128 (2018), Lemma 3.10; P. Scholze, Perfectoid
spaces, Publ. Math. IHES 116 (2012), Theorem 5.2.

Part of: Proper base change; invariance under extension of algebraically closed fields (known
result; see Lib.Cohomology.ProperBaseChange.ProperBaseChange).

Part of: Almost acyclicity of the structure sheaf for the v-topology (known result; see
Lib.PadicComparison.Descent.AlmostAcyclic).

Part of: Faltings' toric towers and their Koszul complexes (known result; see
Lib.PadicComparison.ToricTower.CrystallineLines).

Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Proper functors and the Riemann-Zariski type space of places covering them. Homotopy
quotient by one endomorphism: Wang sequence and criterion via gamma minus one. Maps from perfect b
to the tilt equal maps from O_C tensor W(b). Perfect algebras, perfection, and the two-chart exact
sequence forcing f|g or g|f. A_inf-structures on tilted algebras; tensor with W(b) has no p-torsion.
Coefficients tensored with the maximal ideal of the tilt; the ideal is idempotent. Affine maps
surjective on valuation-ring points are covers: descent along v-covers. -/

noncomputable section

section

attribute [-simp] RingHomCompTriple.comp_apply

open Pi CategoryTheory CommRingCat IsLocalRing RingHom Ideal ResidueField Set algebraMap
variable {Z} {D P C C' : CommRingCat} (α : D ⟶ P) {s : Z ⟶ reprBy D} {F} [Field.{0} F]

/-- Z is proper over D: coincidence of two points is cut out by an ideal, and for one a ∈ Z(T)
each geometric point sending D into a valuation ring O comes from a through some T → O. -/
structure IsProperOver (s : Z ⟶ reprBy D) where
  diagonal_closed C x y : ∃ I, ∀ C' f, @Z.map C C' f x = Z.map f y ↔ I ≤ ker f.hom
  valuative_cover : ∃ T a, ∀ {K} [Field K] [IsAlgClosed K] (O : ValuationSubring K) z,
    (∀ d, baseRingMap (B := of K) s z d ∈ O) → ∃ u, @Z.map T _ (u ≫ ofHom O.subtype) a = z

lemma IsProperOver.ext_of_jointly_injective (h : IsProperOver s) {J} {K : J → _} (π : ∀ j, C ⟶ K j)
  (hπ : ∀ c, (∀ j, π j c = 0) → c = 0) {x y} (e : ∀ j, Z.map (π j) x = Z.map (π j) y) : x = y :=
  (h.1 ..).rec fun _ h ↦ by simpa using (h _ (𝟙 _)).2 (by simp_all +singlePass [LE.le])

lemma IsProperOver.injective_map_valuationSubring (h : IsProperOver s) (U : ValuationSubring F) :
  (Z.map (ofHom U.subtype) ·).Injective :=
  fun _ _ e ↦ h.ext_of_jointly_injective _ (by simp) fun _ : ℕ ↦ e

/-- For α: D → P, a place: a prime q of P with a valuation ring O of the residue field κ(q) that
contains the image of D. -/
structure ResiduePlace where
  prime : PrimeSpectrum P
  valSubring : ValuationSubring prime.1.ResidueField
  base_mem d : ↑(α d) ∈ valSubring

namespace ResiduePlace

/-- For α: D → P, the product of the valuation rings O over all places (q, O) of
`ResiduePlace`. -/
abbrev prodValRing := of (∀ j : ResiduePlace α, j.valSubring)

variable {α} (s) (f : prodValRing α ⟶ C) (t : P) (j : ResiduePlace α)

/-- For a place j, the projection ring homomorphism from the product of all the valuation rings
to the valuation ring of j. -/
abbrev projRing : prodValRing α ⟶ of j.valSubring := ofHom (evalRingHom ..)

/-- For a place j=(q,O), the residue field κ(q) of the prime q of P. -/
abbrev PlaceField := j.prime.1.ResidueField

/-- The componentwise inclusion ∏ O → ∏ κ(q), both products over all places (q, O). -/
abbrev toFieldProd : prodValRing α ⟶ ⟨∀ j : ResiduePlace α, j.PlaceField⟩ := ofHom (algebraMap ..)

/-- For t∈P and a place (q,O), the element of O equal to 1 if the image of t in κ(q) lies in O,
and its inverse otherwise. -/
def denominator : j.valSubring := if h :
  ↑t ∈ j.valSubring then 1 else ⟨_, (j.valSubring.2 _).resolve_left h⟩

/-- For t∈P and a place (q,O), the element of O given by the image of t in κ(q) times the
denominator b(t). -/
def numerator : j.valSubring :=
  ⟨t * j.denominator t, by simp [denominator, apply_dite]; grind [zero_mem, one_mem]⟩

lemma isCoprime_denominator_numerator : IsCoprime (f (denominator t)) (f (numerator t)) :=
  .map ⟨1 - numerator t, 1, by ext; simp [numerator, denominator, apply_dite]; grind [zero_mem]⟩ _

/-- For f: ∏O_j → C, the subring of (t, c) in P × C with a = bt in ∏κ_j and f(a) = f(b)c for
some a, b in ∏O_j, f(b) a unit. -/
def fractionGraph := letI := f.hom.toAlgebra
  ((⊥ : Subalgebra (prodValRing α) _).saturation (_ ⊓ (IsUnit.submonoid C).comap (snd ..))
              inf_le_left).toSubring.comap
    ((algebraMap P (∀ j : ResiduePlace α, j.PlaceField)).prodMap (.id C))

/-- For Z proper over D, P absolutely flat with algebraically closed residue fields and ξ ∈
Z(P): a point z of Z over the product of the valuation rings of all places, agreeing with ξ
in the residue fields of P. -/
structure ValuativeLift (ξ : Z P) where
  point : Z (prodValRing (baseRingMap s ξ))
  map_point_eq : Z.map toFieldProd point = Z.map (ofHom (algebraMap ..)) ξ
  isProperOver : IsProperOver s
  absolutely_flat (a : P) : ∃ y, y * a * a = a
  isAlgClosed_residueField (q : Ideal P) [q.IsPrime] : IsAlgClosed q.ResidueField

variable {f t s} {ξ : Z P} (z : ValuativeLift s ξ)

lemma mem_fractionGraph {c} : (t, c) ∈ fractionGraph f ↔ f (numerator t) = f (denominator t) * c :=
  ⟨fun ⟨_, ⟨⟨_, rfl⟩, u⟩, _, h⟩ ↦ by
  erw [← u.mul_right_inj, mul_left_comm, ← congr(_ * $h.2), ← map_mul, ← map_mul f.hom]
  congr 1 with; exact (congr(_ * $h.1 _).trans (mul_rotate' ..)).symm, fun h ↦ ⟨_, ⟨⟨_, rfl⟩,
  (isCoprime_denominator_numerator ..).isUnit_of_dvd ⟨c, h⟩⟩, _, Prod.ext (.symm (mul_comm ..)) h⟩⟩

/-- The space of places of z ∈ Z(∏O_j): maps f: ∏O_j → C, identified when they give the same point
f(z) and the same values (f a(t) : f b(t)), t ∈ P. -/
def placeSpace : PointFunctor := by use fun C ↦ ULift (Quotient ⟨fun f g : _ ⟶ C ↦ Z.map f z.1 =
  Z.map g z.1 ∧ ∀ t, f (numerator t) * g (denominator t) = g (numerator t) * f (denominator
  t), by constructor <;> intros <;> grind [!isCoprime_denominator_numerator, IsCoprime]⟩), fun k ↦
  ↾(⟨·.1.map' (· ≫ k) (by simp_all [← map_mul])⟩) <;> (repeat intro) <;> ext ⟨⟨⟩⟩ <;> rfl

/-- For z ∈ Z(∏O_j), the map from the place space W to Z sending the class of f: ∏O_j → C to
f(z) ∈ Z(C). -/
def placeSpaceMap : placeSpace z ⟶ Z := ⟨fun _ ↦ ↾(·.1.lift _ fun _ _ ↦ And.left), by
  intros; ext ⟨⟨⟩⟩; apply Z.map_comp_apply⟩

variable {z} {R} [CommRing R] [IsLocalRing R] {q : Ideal P} [M : q.IsMaximal] (x : placeSpace z C)

lemma exists_factor_residueField (g : P ⟶ of F) : ∃ᵉ (q : PrimeSpectrum P) (l),
  ofHom (algebraMap P q.1.ResidueField) ≫ l = g := have := ker_isPrime _
  ⟨⟨_, this⟩, ofHom (lift _ _ le_rfl (id fun _ ↦ .mk0 _)), by aesop⟩

/-- The graph of a place x in `ResiduePlace.placeSpace` over C: the subring of pairs (t, c) in P × C
with f(a_t) = f(b_t)·c for any map f representing x. -/
def placeGraph := x.1.lift fractionGraph (by rintro _ _ ⟨⟩; grind +extAll [mem_fractionGraph,
  isCoprime_denominator_numerator, IsCoprime])

lemma placeGraph_map {k : C ⟶ C'} {c} : ∀ {x}, (t, c) ∈ placeGraph x → (t, k c) ∈ placeGraph
  ((placeSpace z).map k x) := by rintro ⟨⟨⟩⟩; erw [mem_fractionGraph, mem_fractionGraph]; aesop

variable (z) (J : Ideal D) (B : Subring q.ResidueField)

/-- For an ideal I of P, the subfunctor of the space of places W of points that give every t ∈ I
the value 0. -/
def killingPlaces (I : Ideal P) : Subfunctor (placeSpace z) :=
  ⟨fun _ ↦ {x | ∀ t ∈ I, (t, 0) ∈ placeGraph x}, fun _ _ ↦ (by simpa using placeGraph_map <| · · ·)⟩

/-- For a maximal ideal q of P and a place y killing q, the subring of κ(q) = P/q formed by the
images of the t ∈ P finite at y. -/
def finiteSubring (y : killingPlaces z q C) :=
  (domRestrict (.comp (algebraMap P q.ResidueField) (fst ..)) (placeGraph y.1)).range

/-- For an ideal J of D and a subring B of κ(q), the subfunctor of places vanishing on q that
are finite on B and whose structure map from D kills J. -/
def placesFiniteOn := zeroPoints ((killingPlaces ..).ι ≫ placeSpaceMap z ≫ s) J ⊓ ⟨fun _ ↦
  {y | B ≤ finiteSubring z y}, fun k _ h _ i ↦ (h i).imp' (⟨_, placeGraph_map ·.2⟩) (by simp)⟩

variable {z J B x}

lemma placeGraph_unique {c d} : (t, c) ∈ placeGraph x → (t, d) ∈ placeGraph x → c = d :=
  x.rec (Quot.ind (by grind [placeGraph, mem_fractionGraph, isCoprime_denominator_numerator · t,
  IsCoprime]))

lemma isRelAffine_killingPlaces I : IsRelAffine (killingPlaces z I).ι :=
  isRelAffine_of_zero_unit_locus (by rintro _ ⟨⟨f⟩⟩; use f '' numerator '' I, ∅, fun _ _ ↦
  (forall₂_congr fun _ _ ↦ mem_fractionGraph).trans (by simp))

lemma mem_finiteSubring_iff {f} h : ↑t ∈ finiteSubring z (⟨⟨⟦f⟧⟩, h⟩ : killingPlaces z q C) ↔ IsUnit
  (f (denominator t)) := ⟨fun ⟨⟨⟨u, c⟩, v⟩, _⟩ ↦ (isCoprime_denominator_numerator ..).isUnit_of_dvd
  ⟨_, mem_fractionGraph.1 (by simpa using! add_mem v (h (t - u) (by simp_all
  [← algebraMap_residueField_eq_zero])))⟩, (·.dvd.rec fun _ ↦ (⟨⟨_, mem_fractionGraph.2 ·⟩, rfl⟩))⟩

lemma mem_fractionGraph_projRing {φ : _ ⟶ C} (t : P) h : (t, φ ⟨t, h⟩) ∈ fractionGraph
  (j.projRing ≫ φ) := by simp [mem_fractionGraph, numerator, denominator, h]

lemma projRing_mem_killingPlaces j φ : ⟨⟦projRing j ≫ φ⟧⟩ ∈ killingPlaces z j.prime.1 C := fun _ _ ↦
  mem_fractionGraph.2 (by simp_all [numerator, ← algebraMap_residueField_eq_zero,
  ← ZeroMemClass.zero_def])

lemma isRelAffine_placesFiniteOn : IsRelAffine (placesFiniteOn z J B).ι :=
  isRelAffine_of_zero_unit_locus (by rintro _ ⟨⟨⟨⟩⟩⟩; exact ⟨_, _, fun _ _ ↦ .trans (.and (by
  simp [zeroPoints]; erw [baseRingMap_map]; rfl) (q.algebraMap_residueField_surjective.forall.trans
  (forall₂_congr fun _ _ ↦ by apply mem_finiteSubring_iff)))
  (forall_mem_image.and forall_mem_image).symm⟩)

lemma baseRingMap_mem_placeGraph d : (baseRingMap s ξ d, baseRingMap (placeSpaceMap z ≫ s) x d) ∈
  placeGraph x := x.rec (Quot.ind fun _ ↦ ⟨1, one_mem _, baseRingMap s z.1 d,
  Prod.ext (by simpa using congr(baseRingMap s $z.map_point_eq d)) (baseRingMap_map .. ▸ by aesop)⟩)

/-- Let Z be proper over D, z ∈ Z(∏O_j) agree with ξ ∈ Z(P) over ∏ κ(q), R a local ring. Each
x ∈ W(R) has a place (q, O') and a local map O' → R with x the class of ∏O_j → O ⊂ O' → R for every
place (q, O), O ⊂ O'. -/
lemma exists_place_of_isLocalRing : ∀ x : placeSpace z _,
  ∃ (j : ResiduePlace (baseRingMap s ξ)) (φ : j.valSubring →+* R), IsLocalHom φ ∧ ∀ O k i, x =
  ⟨⟦projRing ⟨j.prime, O, k⟩ ≫ ofHom (φ.comp (O.inclusion _ i))⟧⟩ := by
  rintro ⟨⟨f⟩⟩; have := z.isAlgClosed_residueField
  obtain ⟨_, _, _, _, _, U, _, I⟩ :=
    IsTest.exists_valuationSubring_atPrime .pi (comap f.hom (maximalIdeal _))
  obtain ⟨ψ, ⟨⟩⟩ : ∃ ψ, ofHom _ ≫ ψ = f := ⟨_, hom_ext (I.lift_comp (by simp))⟩
  have ⟨G, e⟩ : _ ≫ ofHom U.subtype ∈ range (toFieldProd ≫ ·) :=
    ⟨_, hom_ext (IsLocalization.map_comp
    (M := .pi univ (nonZeroDivisors ·.valSubring)) fun _ _ ↦ I.nonZeroDivisors_le_comap
    _ _ (by simp_all [↓funext_iff, Submonoid.mem_pi, mem_nonZeroDivisors_iff]))⟩
  have ⟨q, l, o⟩ := exists_factor_residueField (ofHom (algebraMap P _) ≫ G)
  use ⟨q, U.comap l.hom, fun d ↦ congr($o _ ∈ U).trans congr($e (⟨_, ·.base_mem d⟩) ∈ _) ▸ by simp⟩,
    ψ.hom.comp (l.hom.restrict _ U (by simp)), ⟨fun _ ↦ not_imp_not.1 fun _ ↦
    I.map_eq_maximalIdeal.ge.trans (comap ψ.hom (maximalIdeal R)).map_comap_le (by simp_all
    [Submonoid.isUnit_iff_and])⟩, fun O k i ↦ congr((placeSpace z).map ψ ⟨$(Quot.sound (b :=
    _ ≫ ofHom (restrict _ O U i)) ⟨z.isProperOver.injective_map_valuationSubring _ (by
    have := congr(Z.map G $z.map_point_eq =
      Z.map (ofHom (evalRingHom PlaceField ⟨q, O, k⟩) ≫ l) $z.map_point_eq)
    simp_rw [← Z.map_comp_apply, e, ← o] at *
    tauto), fun t ↦ Subtype.ext (congr($(congr($e _).symm.trans ((map_mul G.hom ..).trans
    congr($o.symm t * $e _))) * _ = $(map_mul l.hom ..) * _).mpr (mul_right_comm ..))⟩)⟩)

lemma isProperOver_placeSpace : IsProperOver (placeSpaceMap z ≫ s) :=
  ⟨by rintro _ ⟨⟨f⟩⟩ ⟨⟨g⟩⟩; exact ((z.isProperOver.1 _ (Z.map f z.1) (Z.map g z.1)).imp' (· ⊔ ⨆ t,
  span {f (numerator t) * g (denominator t) - g (numerator t) * f (denominator t)}) (by
  intros; erw [ULift.up_inj, Quotient.eq]; simp [*])), _, ⟨⟦𝟙 _⟧⟩, fun O x H ↦
  (exists_place_of_isLocalRing x).elim fun j ⟨φ, n, e⟩ ↦
  ⟨projRing ⟨_, ⟨(O.1.comap φ).map j.valSubring.subtype, fun x ↦ by
  wlog h : x ∈ j.valSubring generalizing x; grind [j.valSubring.mem_or_inv_mem]
  exact or_not.imp_right fun c ↦ (n.1 ⟨_, h⟩ (by aesop)).elim fun u _ ↦ ⟨↑u⁻¹, by cases O.2 (φ
    u) <;> aesop⟩⟩, fun d ↦ ⟨⟨_, j.base_mem d⟩, (placeGraph_unique (baseRingMap_mem_placeGraph d)
  (e _ _ le_rfl ▸ j.mem_fractionGraph_projRing ..)).subst (H d), rfl⟩⟩ ≫ ofHom
  ((φ.comp _).codRestrict O (by rintro ⟨_, _, _, ⟨⟩⟩; tauto)), (e _ _ image_val_subset).symm⟩⟩

lemma finiteSubring_total_and_exists_place {x : placeSpace z ⟨R⟩} m :
  (∀ t, t ∈ finiteSubring z ⟨x, m⟩ ∨ t⁻¹ ∈ finiteSubring z ⟨x, m⟩) ∧ ∀ O h,
  O.1 ≤ finiteSubring z ⟨x, m⟩ → ∃ φ, x = ⟨⟦projRing ⟨⟨q, M.isPrime⟩, O, h⟩ ≫ φ⟧⟩ := by
  obtain ⟨⟨⟨_, p⟩, V, k⟩, φ, n, e⟩ := exists_place_of_isLocalRing x; cases e _ k le_rfl
  cases M.eq_of_le p.1 fun t i ↦ (z.absolutely_flat t).elim fun y _ ↦ (@p.2 (1 - y * t) t (by simp
               [sub_mul, *])).resolve_left (one_ne_zero <| placeGraph_unique (one_mem _) <| by
    simpa using add_mem (m _ (q.smul_mem y i)) <| projRing_mem_killingPlaces _ _ _ ·)
  refine (Subring.ext ?_ : finiteSubring .. = V.1) ▸ ⟨V.2, by tauto⟩
  simp [q.algebraMap_residueField_surjective.forall, mem_finiteSubring_iff, denominator]; intro
  split <;> simp_all [Submonoid.isUnit_iff_and]; erw [inv_inv]; tauto

end ResiduePlace

end

section

open CategoryTheory Function FreeAbelianGroup AddCommGrpCat
variable (C) {C'} [Category C] [Category C'] {F : AbFunctor C} {F' : AbFunctor C'} {U}

/-- For a category C, the product category C × Bℕ, where Bℕ is the one-object category whose
endomorphism monoid is the additive natural numbers. -/
abbrev TimesBNat := C × SingleObj (Multiplicative ℕ)

/-- The projection functor from the product category C × Bℕ to its first factor C. -/
abbrev TimesBNat.fst : TimesBNat C ⥤ C := .mk (·.1) (·.1)

/-- The functor C → C × Bℕ sending an object A to (A, ∗) and a morphism f to (f, identity). -/
abbrev TimesBNat.incl : C ⥤ TimesBNat C := .mk (·, ⟨⟩) (·, 𝟙 _)

open TimesBNat Abelian.Ext Comparison freeAb ShortComplex LongExactSeq MonoidalCategory
  CartesianMonoidalCategory AddChar
variable {C} (Y : TimesBNat C ⥤ Type 1)

/-- The functor on C × Bℕ represented in the factor Bℕ: the set ℕ, constant on C, with the
generator acting by the shift. -/
abbrev TimesBNat.natWithShift : TimesBNat C ⥤ Type 1 := .mk (·.2) (·.2) ⋙ uliftCoyoneda ⟨⟨⟩⟩

/-- For a set-valued functor Y on C × Bℕ and a natural number k, the endomorphism of the
restriction of Y to C given at A by Y(id_A, k). -/
def TimesBNat.shiftEnd : AddChar ℕ (End (incl C ⋙ Y)) :=
  toMonoidHomEquiv.2 ((Y.curryObj.flip.mapEnd _).comp (SingleObj.toEnd _).toMonoidHom)

variable {Y} (F) in /-- the cohomology of U is that of the homotopy quotient Y -/

abbrev IsLine (a : Y ⟶ TimesBNat.fst C ⋙ U) := IsBijective (.restrict _ F) (freeAbMap a)

/-- For a set-valued functor X on C, the projection X(A) × ℕ → X(A) induces bijections from
Hⁿ(X, F) to the cohomology of X × ℕ on C × Bℕ, ℕ acting by translation, with coefficients F
pulled back. -/
lemma TimesBNat.isBijective_induced {X} : IsLine F (SemiCartesianMonoidalCategory.fst (fst C ⋙ X)
  natWithShift) := HasUnivPoints.isBijective (⟨⟨·, ⟨⟩⟩, ⟨·, ⟨.zero⟩⟩, 𝟙 _, by aesop,
  fun _ _ f e ↦ ⟨(f, _), ⟨congr(($e.symm, _)), by simp⟩, by bound⟩, by simpa using! bijective_id⟩)

/-- Known result: Faltings' toric towers and their Koszul complexes. -/
lemma TimesBNat.shortExact_induced : ∃ w, ShortExact ⟨Sub.sub (freeAb.map
  ((fst C).whiskerLeft (shiftEnd Y 1).asHom ▷ natWithShift))
    (freeAb.map (_ ◁ {app _ := ↾.map .succ})),
  freeAb.map ⟨fun _ ↦ ↾fun x ↦ (shiftEnd Y x.2.1).asHom.app _ x.1, fun _ _ f ↦ by
    ext; exact congr($((Y.map_commSq ⟨by simp; rfl⟩).w) _)⟩, w⟩ := by
  refine have h A : ShortExact ⟨ofHom (map (Prod.map ((shiftEnd Y 1).asHom.app A) id) - map
    (Prod.map id
    (ULift.map .succ))), ofHom (map fun (x, ⟨k⟩) ↦ (shiftEnd Y k).asHom.app A x), ?_⟩ :=
      Splitting.shortExact ⟨ofHom (lift fun x ↦ x.2.1.rec 0 (fun k h x ↦
      h ((shiftEnd Y 1).asHom.app A x) - of (x, ⟨k⟩)) x.1), ofHom (map (·, ⟨0⟩)), ?_, by
        ext; simp, ?_⟩
    shortExact_of_app (h ·.1 |>.ab_injective_f) (exact_of_shortComplex_exact <|
      h ·.1 |>.1) (h ·.1 |>.ab_surjective_g) <;> ext ⟨x, ⟨k⟩⟩ <;> revert x <;> induction k <;>
    simp_all [map_add_eq_mul, sub_add, sub_eq_iff_comm]

/-- The map i is injective, every fixed point of g lies in its image, and z ↦ g(z) − z is onto. -/
abbrev KoszulExact {A B} [Sub B] (i : A → B) g :=
  Injective i ∧ fixedPoints g ⊆ .range i ∧ Surjective (g - id)

/-- Let Y restricted to C be Hom(E, ψ−), with q: Y → h_A induced by i: ψA → E and the generator
of ℕ acting by g. If restriction along ψ preserves H(h_E, F') and F'(i), F'(g) satisfy
`KoszulExact`, then q^* is bijective for F'∘ψ. -/
lemma IsLine.of_acyclic {Y ψ A E} {q : Y ⟶ TimesBNat.fst C ⋙ reprBy A} (e : ψ ⋙ reprBy E ≅ incl C ⋙
  Y) (a : IsAcyclicAt ψ F' E) i g (hi : ∀ D f, ψ.map (q _ (e.1 D f)).1 = i ≫ f.1) (hg : CommSq
  (ψ.whiskerLeft (reprMap g)) e.1 e.1 (shiftEnd Y 1).asHom)
    (h : KoszulExact (F'.map i) (F'.map g)) :
  IsLine (ψ ⋙ F') q := let r := homOfValue (.restrict (_ ⋙ ψ) F') (SemiCartesianMonoidalCategory.fst
    _ natWithShift ≫ (TimesBNat.fst C).whiskerLeft e.2)
  have ⟨(b : Bijective r), o⟩ := isBijective_reprBy_iff.1 ((a.precomp_of_bijective _ rfl (e.app ·
    |>.toEquiv.symm.bijective)).trans isBijective_induced)
  let S := mk _ _ (shortExact_induced Y).1
  have E z : S.f ≫ r z = r (F'.map g z - z) :=
    hom_ext fun D x ↦ by erw [map_sub (r z D).1, homOfValue_app,
    homOfValue_app, homOfValue_app, congr($(hg.vert_inv.w) _ x.1), map_sub, F'.map_comp_apply]; rfl
  have t y : S.g ≫ homOfValue (.restrict _ (_ ⋙ _)) q y = r (F'.map i y) := hom_ext fun D x ↦ by
    erw [homOfValue_app (c := .restrict ..) q y D, q.naturality_apply, homOfValue_app,
      ← F'.map_comp_apply, ← hi, e.inv_hom_id_app_apply]; aesop
  isBijective_reprBy_iff.2 ⟨⟨fun _ _ k ↦ h.1 (b.1 (t _ ▸ k ▸ t _)), (S.g ≫ · |> b.2 |>.elim fun z
    k ↦ (@h.2.1 z (sub_eq_zero.1 (b.1 (by simp [← E, k])))).imp fun _ _ ↦ (shortExact_induced
    Y).2.3.1 _ _ (by aesop))⟩, (o · |> @Injective.subsingleton _ _ _ ((contravariant
    (shortExact_induced Y).2 _).f_injective_of_g_surjective fun m _ ↦ m.casesOn ((((mk₀_bijective
    ..).2.comp b.2).comp h.2.2).forall.2 (⟨_, E · ▸ mk₀_comp_mk₀ ..⟩)) (⟨0, o · |>.1 _ ·⟩)))⟩

end

section

open NeZero CategoryTheory Functor Function ConcreteCategory WittVector Perfection PadicTest CharP
variable {p} [ThePrime p]

/-- For a perfect O^♭-algebra b, the natural isomorphism Hom(b, S^♭) ≅ Hom(O_C ⊗_{A_inf} W(b),
S) of functors on p-adic tests S, sending f to θ∘W(f). -/
def homTiltIso {b : CommAlg _} [PerfectRing b p] : tilt ⋙ reprBy b ≅ algFunctor ⋙ reprBy
  ((wittFunctor ⋙ algBaseChange _) b) := isoOfAppBijective (whiskerLeft _ (pointMap (Y :=
  _ ⋙ algBaseChange _ ⋙ reprBy _) ⟨𝟙 _⟩) ≫ whiskerRight thetaIso.1 (reprBy _)) fun c ↦ by
  erw [← (Equiv.ulift.trans (algBaseChangeAdj.homEquiv ..)).comp_bijective,
    bijective_iff_existsUnique]
  rintro ⟨g : WittVector p b →+* c.ProdRing, k⟩
  let φ := constantCoeff.liftOfRightInverse (teichmuller p) .refl
    ⟨.comp (Ideal.Quotient.mk (.span {↑p})) g, by simp [cast_eq_zero, witt_reduction_spec OFlat]⟩
  have := @of_ringHom_of_ne_zero _ _ _ _ _ φ.domain_nontrivial b.3.2 p out _
  let ψ := Perfection.lift p b _ φ
  use ⟨ofHom ⟨ψ, (ψ.comp _).congr_fun (hom_ext p fun x ↦ by
    erw [← coeff_tiltMap _ (teichmuller p x).mk_fontaineTheta, ← k, map_teichmuller]
    rfl)⟩⟩, ext_apply (RingHom.congr_fun (witt_hom_ext (g := g) fun _ ↦ by
    erw [c.thetaIso_hom_one_tmul, map_teichmuller, fontaineTheta_teichmuller]
    exact teichmuller_spec fun _ ↦ ⟨_, rfl, by simp [← map_pow]⟩)), fun ⟨_⟩ h ↦ congr(⟨$(ext_apply
    (RingHom.congr_fun (hom_ext p fun x ↦ (@mk_fontaineTheta c.ProdRing ..).symm.trans
    (c.thetaIso_hom_one_tmul _ ▸ congr(⟦$h.1 (teichmuller p x)⟧)))))⟩)

/-- Known result: Tilting and untilting for products of perfectoid valuation rings over O_C. -/
instance : tilt.Full := ⟨fun _ ↦ ⟨_, congr($((homTiltIso (b := .of ..).app
  _).toEquiv.injective congr(⟨$((thetaIso.1.2 _).trans (IsIso.hom_inv_id_assoc ..))⟩)).1)⟩⟩

instance : algFunctor.Faithful := ⟨congrArg hom⟩

instance : tilt.Faithful := .of_comp_iso thetaIso

end

section

open Algebra.TensorProduct AddMonoidAlgebra CategoryTheory CharP Fact Function Ideal PerfectClosure
  Polynomial TensorProduct Limits Ideal.Quotient

attribute [-instance] instCharZeroOfIsSemireal instCoeTCOfCoe

variable {p} (S) [CommRing.{0} S]

/-- The full subcategory of commutative S-algebras on which x ↦ x^p is bijective. -/
abbrev PerfectAlg [ThePrime p] := @ObjectProperty.FullSubcategory (CommAlg S) _ (PerfectRing · p)

variable {S} [ThePrime p] (b : PerfectAlg S) (h : (p : S) = 0) (B) [CommRing.{0} B] [Algebra S B]

instance : PerfectRing b.1 p := b.2

/-- The maximal ideal 𝔪 of the local ring O^♭. -/
abbrev MaxIdealFlat := ↥(IsLocalRing.maximalIdeal OFlat)

/-- The functor from p-adic tests to perfect O^♭-algebras sending S to its tilt S^♭. -/
def PadicTest.perfectTilt : PadicTest ⥤ PerfectAlg OFlat :=
  ObjectProperty.lift _ _ (·.isPerfectTorsionFree_tilt.1)

lemma p_eq_zero_of_algebra_oFlat [Algebra OFlat S] :
  (p : S) = 0 := by simp [← map_natCast (algebraMap OFlat S), cast_eq_zero]

/-- For a commutative additive monoid G that is a module over the non-negative rationals, the
monoid algebra O^♭[G] is perfect: x ↦ x^p is bijective on it. -/
lemma perfectRing_monoidAlgebra G [AddCommMonoid.{0} G] [Module ℚ≥0 G] : PerfectRing OFlat[G] p :=
  ⟨(congr(⇑$(show (mapDomainRingEquiv _ (DistribMulAction.toAddEquiv₀ G (p : ℚ≥0) (NeZero.ne _)) *
  mapRingEquiv G (frobeniusEquiv OFlat p)).toRingHom = frobPow p_eq_zero_of_algebra_oFlat 1 by ext
  <;> simp [← Nat.cast_smul_eq_nsmul ℚ≥0] <;> rfl)).trans (by aesop)).subst (RingEquiv.bijective _)⟩

lemma isReduced_of_perfectRing : PerfectRing S p → IsReduced S :=
    ((isReduced_iff_pow_one_lt p out).2 fun _ _ ↦ ·.1.1 (by simpa [NeZero.ne]))

/-- Every Laurent polynomial over S is a polynomial in T plus a polynomial in T⁻¹ without
constant term: S[T, T⁻¹] = S[T] + T⁻¹ S[T⁻¹], that is, H¹(ℙ¹, 𝒪) = 0. -/
lemma laurent_split : Surjective fun (P, Q) ↦ @toLaurent S _ P + LaurentPolynomial.invert
    (X * Q).toLaurent := (·.induction_on' (fun _ _ ⟨x, a⟩ ⟨y, b⟩ ↦ ⟨x + y, by grind⟩)
    (·.rec (⟨⟨monomial · ·, 0⟩, by simp⟩) (⟨⟨0, monomial · ·⟩, by simp [Int.negSucc_eq]⟩)))

include h

omit [ThePrime p] in
lemma natCast_eq_zero_of_algebra : (p : B) = 0 := by grind [map_natCast (algebraMap S B) p]

lemma PerfectAlg.closed_under_widePushoutShape J : ObjectProperty.IsClosedUnderColimitsOfShape (C :=
  CommAlg S) (PerfectRing · p) (WidePushoutShape J) := pow_one p ▸ ⟨fun _ ⟨c⟩ ↦
  ⟨(ConcreteCategory.isIso_iff_bijective _).1 <| @isIso_app_coconePt_of_preservesColimit _ _ _ _ _ _
  _ _ _ (⟨fun B ↦ CommRingCat.ofHom (frobPow (natCast_eq_zero_of_algebra h B) 1), by
  aesop (add simp commAlgCatEquivUnder)⟩ : (commAlgCatEquivUnder ⟨S⟩).1 ⋙ Under.forget _ ⟶
      (commAlgCatEquivUnder (.of S)).1 ⋙ Under.forget _ )
  (isoOfAppBijective _ (c.2 · |>.1)).isIso_hom _ c.1.3 _ _⟩⟩

/-- The perfection of B/t, for p = 0 in S: a map e from B to a perfect S-algebra with e(t) = 0,
through which every such map factors; e(r) = e(s) implies t ∣ r^{p^n} − s^{p^n} for some n,
and every element has a p^n-th power in the image. -/
lemma exists_perfection_quotient t : ∃ (c : PerfectAlg S) (e : B →ₐ[S] c.1),
  (∀ {d : PerfectAlg S} (φ : B →ₐ[S] d.1), φ t = 0 → ∃ ψ, .comp ψ e = φ) ∧ (∀ r s, e r = e s → ∃ n,
  t ∣ r ^ p ^ n - s ^ p ^ n) ∧ e t = 0 ∧ ∀ y, ∃ n r, e r = y ^ p ^ n := let Q := B ⧸ span {t}; by
  by_cases! Subsingleton Q
  exact ⟨⟨.of S Q, ⟨bijective_of_subsingleton _⟩⟩, mkₐ .., fun φ _ ↦ ⟨liftₐ _ φ
    (by grind [mem_span_singleton']), rfl⟩, by simp [← eq_zero_iff_dvd, nontriviality]⟩
  have (B) [CommRing B] [Algebra S B] [Nontrivial B] :=
    of_eq_zero out (natCast_eq_zero_of_algebra h B)
  algebraize [(PerfectClosure.of Q p).comp (algebraMap S Q)]
  use ⟨.of S (PerfectClosure Q p), inferInstance⟩, ⟨(PerfectClosure.of ..).comp (Ideal.Quotient.mk
    _), by tauto⟩, @fun d φ _ ↦ by nontriviality d.1; exists ⟨PerfectClosure.lift _ p _
    (Ideal.Quotient.lift _ φ (by simp_all [mem_span_singleton'])), φ.2⟩
  simpa [Q, PerfectClosure.of_apply, mk_eq_iff, iterate_frobenius, ← eq_zero_iff_dvd,
    (mkₐ_surjective S _).exists] using (isPRadical Q p).1

/-- A reduced ring S with p = 0 in which every element is a p-th power is perfect: x ↦ x^p is
bijective. -/
lemma perfectRing_of_pow_surjective [IsReduced S] (s : Surjective (· ^ p : S → S)) :
    PerfectRing S p := ⟨pow_one p ▸ .of_ker (frobPow h 1) (by simp [NeZero.ne]), s⟩

lemma perfectRing_tensor [PerfectRing S p] (B D : PerfectAlg S) : PerfectRing (B.1 ⊗[S] D.1) p :=
  (PerfectAlg.closed_under_widePushoutShape h _).1 _ ⟨⟨_, _, (IsPushout.of_is_coproduct
  (B.1.binaryCofanIsColimit _) CommAlgCat.isInitialSelf).isColimit⟩, (·.rec ‹_› (·.rec B.2 D.2))⟩

/-- For S perfect with p = 0 and f, g in a perfect S-algebra B, there are perfect S-algebras B₁,
B₂ under B and B₀ with g ∣ f in B₁, f ∣ g in B₂ and B → B₁ × B₂ → B₀ → 0 exact as S-modules,
the first map injective after tensoring with any perfect S-algebra. -/
lemma exists_perfect_blowup_charts [PerfectRing S p] (B : PerfectAlg S) f g :
  ∃ (B₁ B₂ B₀ : PerfectAlg S) (i₁ : B.1 →ₐ[S] B₁.1)
  (i₂ : _ →ₐ[S] B₂.1) (j : _ →ₗ[S] B₀.1), i₁ g ∣ i₁ f ∧ i₂ f ∣ i₂ g ∧ Surjective j ∧ Exact
  (i₁.prod i₂) j ∧ ∀ D : PerfectAlg S, Injective ((i₁.prod i₂).toLinearMap.rTensor D.1) := by
  obtain ⟨⟨B₁, E₁, l₁, -, t₁, s₁⟩, ⟨B₂, E₂, l₂, -, t₂, s₂⟩, B₀, E₀, -, k₀, t₀, s₀⟩ :=
    exists_perfection_quotient h _ (C f - C g * X), exists_perfection_quotient h _ (C g - C f * X),
    exists_perfection_quotient h _ (C f - C g * X).toLaurent
  simp [laurent_split.exists, dvd_def, AlgHom.ext_iff] at *
  obtain ⟨⟨j₁, v₁⟩, j₂, v₂⟩ := l₁ (E₀.comp ⟨toLaurent, by simp⟩) (by simpa), l₂ (E₀.comp ⟨.comp
    LaurentPolynomial.invert.toRingHom toLaurent, by simp⟩) (by simp [*, ← map_mul])
  have b {c : PerfectAlg S} n := (c.2.pow _ p n).1
  refine ⟨_, _, B₀, E₁.comp CAlgHom, ⟨_, t₁⟩, E₂.comp CAlgHom, ⟨_, t₂⟩,
    .coprod j₁ (-j₂), (have ⟨n, P, Q, _⟩ := s₀ ·
    (((b n).prodMap (b n)).2 (E₁ P, E₂ (Q * X))).elim fun ⟨y, z⟩ _ ↦ ⟨(y, -z), (b n).1
      (by simp_all [add_pow_prime_pow_eq out, natCast_eq_zero_of_algebra h, ← map_pow])⟩), fun (y,
    z) ↦ ⟨fun e ↦ ?_, by aesop⟩, fun D ↦ .of_ker _ fun x hx ↦ (isReduced_of_perfectRing
    (perfectRing_tensor h ..)).1 _ (nilpotent_iff_mem_prime.2 fun J _ ↦ ?_)⟩
  · have ⟨n, P, hP⟩ := s₁ y; have ⟨m, Q, hQ⟩ := s₂ (z ^ p ^ n); simp [add_neg_eq_zero] at *
    have ⟨N, U, V, hr⟩ := k₀ (P.toLaurent ^ p ^ m) _ (.trans (by simp [*, ← v₁]) (v₂ Q))
    exact ((b (n + m + N)).2.exists.1 (eq_C_of_toLaurent_eq ((P ^ p ^ m) ^ p ^ N - (C f - C g *
      X) * U) (Q ^ p ^ N - (C g - C f * X) * V) (by simp; grind [@LaurentPolynomial.T_sub B.1 _ 1 1,
      LaurentPolynomial.T_zero]))).imp
      fun x a ↦ by simpa [*, -a, pow_add, pow_mul, (b _).1.eq_iff] using congr($(a.symm).map E₁ E₂)
  let φ := IsScalarTower.toAlgHom S (type_of% x) J.ResidueField
  obtain ⟨⟨w, e | e⟩, K, η, -, k, -⟩ := ValuationRing.cond (φ (g ⊗ₜ 1)) (φ (f ⊗ₜ 1)),
    exists_perfection_quotient h _ (φ 0) <;> [skip; have l₁ := @l₂] <;> obtain ⟨ψ, e⟩ :=
    l₁ (η.comp (aevalTower (φ.comp includeLeft) w)) (by simp [← e]) <;> simpa [φ, NeZero.ne] using
    k (φ x) 0 (by convert congrArg (productMap (ψ.comp (by apply_rules [AlgHom.fst, AlgHom.snd]))
    (η.comp (φ.comp includeRight))) hx <;> clear hx <;> induction x <;> simp [*, ← map_mul])

end

open TensorProduct WittVector CategoryTheory CommRingCat Ideal Subfunctor Function Pi RingHom
variable {p} [ThePrime p] (b : CommAlg OFlat)

instance : Algebra Ainf b := .compHom _ constantCoeff

instance : IsScalarTower Ainf OFlat b := .of_compHom ..

/-- For an O^♭-algebra b, the A_inf-linear map W(b) → b sending a Witt vector to its zeroth
coefficient. -/
def wittConstCoeff := (⟨constantCoeff, by tauto⟩ : wittFunctor.obj b →ₐ[Ainf] b).toLinearMap

lemma isSMulRegular_tensor_witt {𝒜} [AddCommGroup.{0} 𝒜] [Module Ainf 𝒜] (h :
  IsSMulRegular 𝒜 p) {b} : IsPerfectTorsionFree b → IsSMulRegular (𝒜 ⊗[Ainf] wittFunctor.obj b) p
  | ⟨_, hb⟩ => have := isTorsionFree_of_dvd_pow hb (OFlat.exists_dvd_pow not_isUnit_pFlat)
    isSMulRegular_tensor_of_flat_mod (wittConstCoeff b) (witt_reduction_spec OFlat _).1
      (witt_reduction_spec OFlat _).1 (witt_reduction_spec OFlat _).2.1.1 h

variable {p : _} [ThePrime p]

/-- For an O^♭-module M, the functor b ↦ b ⊗ M, tensor product over O^♭, from commutative
O^♭-algebras to O^♭-modules. -/
abbrev tensorCoeff (M : ModuleCat OFlat) := asModules (𝟭 _) ⋙ MonoidalCategory.tensorRight M

/-- For an O^♭-module N, the functor b ↦ b ⊗ N ⊗ 𝔪 from commutative O^♭-algebras to O^♭-modules,
𝔪 the maximal ideal of O^♭ and tensor products over O^♭. -/
abbrev almostCoeff N [AddCommGroup N] [Module OFlat N] :=
  tensorCoeff (.of _ (N ⊗[OFlat] MaxIdealFlat))

/-- For m in the maximal ideal 𝔪 of O^♭ and t ≠ 0 in O^♭, one can write m = s·k with k in 𝔪 and
s in O^♭ such that t divides a power of s. -/
lemma MaxIdealFlat.exists_smul_eq (m : MaxIdealFlat) {t : OFlat} (h : t ≠ 0) : ∃ s k, s • k = m ∧
  ∃ n, t ∣ s ^ n :=
  (OFlat.isAIC.exists_pow_eq 2 m).imp (by aesop (add simp [sq, OFlat.exists_dvd_pow]))

/-- If p: X → Y is relatively representable and surjective on O-points for every valuation
subring O of every algebraically closed field, then the image of p on test rings is dense in
Y for coefficients the locally constant Λ-valued functions.

Known result: Descent of torsion étale cohomology along v-covers; excision, transfer, limits. -/
lemma IsRelAffine.hasCohomDenseImage_of_lifts {X Y p Λ} (hp : @IsRelAffine X Y p) (h :
  ∀ {K} [Field K] [IsAlgClosed K] (O : ValuationSubring K), Surjective (p ⟨O⟩)) : HasCohomDenseImage
  Λ p := fun A y ↦ let U := (range p).preimage (pointMap y); (hp _).elim fun ⟨_⟩ ⟨_, _, g⟩ ↦
    ((Comparison.isBijective_congr (p' := fromPreimage (U.whisker _) _) rfl
    (.of_bijective (pointMap_id_bijective_of_fullyFaithful testIncl A))
    (.of_bijective (pointMap_id_bijective_of_fullyFaithful testIncl A · |>.restrictPreimage _))).1
    (Components.isCohomEquiv_of_connected (.of_atlas ((hp.baseChange g).baseChange
    (.of_horiz_isIso_mono ⟨(U.lift_ι (𝟙 _ ≫ _) fun | _, _, ⟨x, rfl⟩ => ⟨_, congr($g.w.1 _
    x)⟩).symm⟩)) (.of_top_le fun _ ⟨_, _, e⟩ _ ↦ ((isPullback_iff.1 g).2 _ _ _ e).imp (by aesop)))
    (.of_atlas (IsRelAffine.id_mem _) .of_top_le) U.ι (by tauto) (isRelAffine_zeroPoints (𝟙 (reprBy
    A.1)) ·.carrier) (ker ·.1.1 |>.1) .rfl (fun _ ↦ ⟨eq_of_zero_eq_one (by aesop)⟩) (fun _ i ↦
    .of_preimage_le (hasPartitions_locConstCoeff.isCohomDense_partition _ i) (by exact {app _ :=
    ↾(⟨⟨·.1⟩⟩)}) fun _ _ ↦ by apply Or.imp <;> use (span_singleton_le_iff_mem (ker _)).2) fun J T
    g ↦ (J.exists_le_maximal T).elim fun q ⟨M, l⟩ ↦ (A.2.exists_valuationSubring_atPrime q).2.2.elim
    fun _ ⟨_, _, O, _, _⟩ ↦ .of_bijective fun _ ↦ bijective_iff_has_inverse.2 ⟨fun ⟨f, z⟩ ↦
    ⟨⟨_, (unitPoints_le_range_reprMap O q.primeCompl).trans (fun | _, _, ⟨_, rfl⟩ => U.2 _ (h ..)) _
    fun b i ↦ (exists_idempotent_dvd_of_notMem A.2.2 M i).elim fun _
    ⟨n, j, d⟩ ↦ isUnit_of_dvd_unit (map_dvd _ d) ((sub_mem_ker_iff _).1 ((g _ j).elim (by tauto)
    (z _)) ▸ by simp)⟩, z⟩, by tauto⟩).bij).eqv

/-- Let V_i ⊂ Y be finitely many relatively representable subfunctors. A subfunctor U of Y on
test rings is dense for Λ if every point of Y in a valuation ring of an algebraically closed
field lies in some V_i contained in U on test rings. -/
lemma IsCohomDense.of_affine_cover {Y Λ U J} [Finite.{1} J] {V : J → _} (r : ∀ i,
  IsRelAffine (ι (V i))) (h : ∀ {K} [Field K] [IsAlgClosed K] (O : ValuationSubring K) y, ∃ i,
  (V i).whisker _ ≤ U ∧ y ∈ V i ⟨O⟩) : IsCohomDense (Y := testIncl ⋙ Y) (locConstCoeff Λ) U :=
  fun A y ↦ let G i := isPullback_iff.1 ((r i).isPullback (pointMap y))
  (IsRelAffine.hasCohomDenseImage_of_lifts (p := reprMap (ofHom (.pi fun i : {i // (V i).whisker _ ≤
    U} ↦ ((r i).snd _).1.1))) (.map uliftCoyoneda _) fun _ f ↦ (h ..).elim fun i ⟨a, b⟩ ↦
    ((G i).2 _ f ⟨_, b⟩ rfl).imp' (⟨ofHom (evalRingHom _ ⟨i, a⟩) ≫ ·.1⟩) (by tauto)).trans (U :=
    U.preimage (mapOnTests (pointMap y))) (hasPartitions_locConstCoeff.hasZariskiDescent (𝟙 _)
    (by simp) (·.2.2) fun _ ⟨_, ⟨g⟩, rfl⟩ m M ↦ have ⟨_, ⟨i, rfl⟩, k⟩ := (Set.not_subset.1
      (comap_ne_top g.hom M.1.1 ∘ (eq_top_mono · (span_single_eq_top _)) ∘ span_le.2))
    ⟨_, k, fun D ⟨l⟩ v ↦ (((evalRingHom _ i).liftOfSurjective (surjective _)).symm.surjective ⟨(g ≫
                                                         l).hom, by simp_all [IsConcreteLE.le_iff,
      ← v.mul_right_eq_zero, ← map_mul, ← single_mul_left]⟩).elim
      fun u j ↦ i.2 D (congr(Y.map (_ ≫ ofHom $j.1) _) ▸ (G _).1 _ ⟨_⟩ ▸ Subtype.mem _)⟩) A ⟨𝟙 _⟩
