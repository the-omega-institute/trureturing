import OmegaMath.NumberTheory.GRH.Lib.Cohomology.ProjectiveLine.LineChernClass
import OmegaMath.NumberTheory.GRH.Lib.Cohomology.ProperBaseChange.FieldExtension
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Proper base change; invariance under extension of algebraically closed fields (known
result; see Lib.Cohomology.ProperBaseChange.ProperBaseChange).

This file: Proper base change with supports: classes detected on geometric points, field-extension
invariance. -/

open AddEquiv CategoryTheory CommRingCat Function Ideal projLine MonoidalCategory

lemma isProperOver_projLinePow ι :
  IsProperOver ((zIsInitial.op.isTerminalObj uliftCoyoneda _).from (projLinePow ι)) := ⟨fun _ x y ↦
  ⟨⨆ i, span {HSub.hSub.uncurry (unimodularRow (x i) * (unimodularRow (y i)).swap)}, fun _ f ↦
  funext_iff.trans ((forall_congr' fun i ↦ ULift.up_inj.trans ((x i).1.out_eq ▸ (y i).1.out_eq ▸ by
  simp [Quotient.eq, projLineSetoid, unimodularRow])).trans iSup_le_iff.symm)⟩,
  of (FreeCommRing _), fun i ↦ ⟨⟦⟨.of (Sum.inl i), .of (.inr i)⟩⟧⟩, fun O x _ ↦ by
  choose u v e using fun i ↦ (x i).1.ind (motive := (∃ u v : O, ⟦⟨u, v⟩⟧ = ·)) fun a ↦ by
    obtain ⟨c, _⟩ | ⟨c, _⟩ := le_total (O.valuation a.2) ⟦_⟧ <;>
      [use 0, c; use c - 1, 1] <;> simp [Quotient.eq, projLineSetoid] <;> tauto
  use ofHom (FreeCommRing.lift (Sum.elim u v)), congr((⟨$(e · ▸ by simp)⟩))⟩

variable {A} [CommRing A] {D} [Category D] (g : D ⥤ TestOver A) {X} (I :
  IdealFamily (elementsProj (X ⊗ reprBy (of A)))) {ℓ : ℕ}

/-- For a test c over A and a prime P of c, the map of tests over A from c to its residue field
at P, as an object under c. -/
def residueTest (c : TestOver A) (P : PrimeSpectrum c.1) : Under c :=
  .mk (Y := ⟨.of A P.1.ResidueField, have := (c.2.exists_valuationSubring_atPrime
    P).1; isTest_of_preValuationRing⟩) ⟨CommAlg.homOfRingHom (algebraMap ..) (by tauto)⟩

/-- Each class in Extⁿ(ℤ[Hom(c, g(−))], F), c a test, vanishes at the residue fields of an open
set of primes, all primes only if zero; and maps of field tests induce bijections on these
groups. -/
def IsDetectedAtPoints F := (∀ c n x, let z := {P | H.map F (freeAb.map
    (g.whiskerLeft (reprMap (residueTest c P).hom))) n x = 0}; IsOpen z ∧ (z = .univ → x = 0)) ∧ ∀ V
  k (φ : V ⟶ k), IsField V.1 → IsField k.1 → IsCohomEquiv F (freeAb.map (g.whiskerLeft (reprMap φ)))

/-- From ideals I indexed by the points of X × Spec A in rings, the family assigning to a test B
over A and x ∈ X(B) the ideal of I at x and the structure map A → B. -/
def IdealFamily.pullToTests : IdealFamily (ringOf (testOfPoint A X)) :=
  I.whisker (sectionLift (ringOf (testOfPoint A X))
  ⟨(·.2, ⟨ofHom _⟩), fun f ↦ congr(⟨$(f.2), ⟨ofHom $(f.1.1.1.comp_algebraMap)⟩⟩)⟩)

/-- Proper base change: ℓ invertible in A, X proper over ℤ. On pairs (test over A, point of X),
if β from locally constant ℤ/ℓ-valued functions to F is bijective where I vanishes, and this
locus is dense for F, then F satisfies `IsDetectedAtPoints`. -/
lemma IdealFamily.isDetectedAtPoints_of_proper (I : IdealFamily _) [InvertsPrime A ℓ] {p} (hX :
  @IsProperOver X ⟨ℤ⟩ p) {F} (β : locConstAlong (testOfPoint A X) ⟶ F) (hβ : ∀ a,
  I.pullToTests.I a = ⊥ → Bijective (β a)) (hΓ : IsCohomDense F I.pullToTests.botLocus) :
  IsDetectedAtPoints (testOfPoint A X) F := let W : Subfunctor (baseChangeOf _ (zIsInitial.to _)) :=
    ⟨_, fun f x ↦ @I.botLocus.map ⟨x.1⟩ _ ⟨f, rfl⟩ ⟨⟩⟩
  have ⟨h, T, a, ha⟩ := hX.baseChange _
  let s := W.ι ≫ fibreProd.snd ..
  have k {C} f := @I.2 ⟨a.1⟩ (.mk (obj := C) ((baseChangeOf ..).map f a).1) ⟨f, rfl⟩
  have hs : IsProperOver s := ⟨(by convert h · ·.1 ·.1; exact Subtype.ext_iff), _, ⟨_, (k (ofHom
    _)).symm.trans (map_quotient_self _)⟩, fun O z i ↦ (ha O z.1 i).elim fun u e ↦ ⟨ofHom
    (Ideal.Quotient.lift _ _ fun _ b ↦ Subtype.ext (((k _).trans (e ▸ z.2)).le (le_comap_map b))),
    Subtype.ext ((Functor.map_comp_apply ..).symm.trans e)⟩⟩
  let κ : Comparison (locConstCoeff _) F := ⟨_ ⋙ TestOver.toTest A, β⟩
  let u c : (I.pullToTests.botLocus.preimage (toUnit (testOfPoint A X ⋙ reprBy c))).toFunctor ⟶ κ.φ
    ⋙ testIncl ⋙ baseChangeOf s (ofHom _) := ⟨fun _ ↦ ↾fun x ↦ ⟨(⟨⟨_, congr(⟨$(zIsInitial.hom_ext
    ..)⟩)⟩, x.2⟩, ⟨_⟩), congr(⟨ofHom $(x.1.1.1.1.comp_algebraMap.symm)⟩)⟩, fun _ _ f ↦
    .symm congr(↾fun _ ↦ ⟨(⟨$(baseChangeOf.ext f.2 f.1.1.1.2), _⟩, _), _⟩)⟩
  have t c := Comparison.HasUnivPoints.isBijective (u :=
    u c) fun T y ↦ let : Algebra A T.1 := y.1.1.1.1.2.1.1.toAlgebra
    ⟨.mk (obj := ⟨_, T.2⟩) _, ⟨⟨⟨CommAlgCat.ofHom ⟨_, (congr($(y.2).1.1 ·).symm)⟩⟩⟩, y.1.1.2⟩,
      𝟙 T, .symm
      (Functor.map_id_apply ..), fun _ _ f k ↦ ⟨⟨⟨CommAlg.homOfRingHom _ (congr($k.1.1.1.1.2.1.1
      ·).symm)⟩, congr($k.1.1.1.1.1).symm⟩, ⟨congr(⟨⟨⟨CommAlg.homOfRingHom $k.symm.1.2.1.1 _⟩⟩, _⟩),
      rfl⟩, fun _ e ↦ e.2 ▸ rfl⟩, .comp (hβ _ y.1.1.2) bijective_id⟩
  let e {c n} := (ofBijective _ ((hΓ.preimage _).isCohomEquiv n)).trans (ofBijective _ (t c n)).symm
  have w {c k} φ n x : HV.map _ (baseChangeTransition s ((ringOf (𝟭 _)).map φ) (hom_ext
    φ.1.1.comp_algebraMap)) n _ = e _ := (t k n).1 (.trans (κ.map_pull_eq_pull_map (a :=
    freeAbMap (u c)) (a' := freeAb.map (Subfunctor.fromPreimage _
    (Functor.whiskerLeft _ (reprMap φ)))) ..).symm (by simp [e, H.map_map, -Functor.map_comp]; rfl))
  ⟨fun c n x ↦ by simpa only [← e.map_eq_zero_iff, ← w] using!
    hs.isOpen_zero_set_and_eq_zero InvertsPrime.isUnit_prime ⟨of _, c.2⟩, fun V k φ a b n ↦
    (Comparison.bijective_iff_of_comm_sq (w φ n) e.bijective e.bijective).2
    (hs.isCohomEquiv_field_extension InvertsPrime.isUnit_prime _ a b V.2.1 k.2.1 n)⟩
