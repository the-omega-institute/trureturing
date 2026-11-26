import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.CommonEigenvectors
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Functoriality of adic completion; extending monoid actions to completions, localisations,
Witt vectors. -/

noncomputable section


open Ideal MulSemiringAction AdicCompletion IsLocalization Algebra algebraMap
variable (M) {R S : Type*} [Monoid M] [CommRing R] [MulSemiringAction M R] [CommRing S] {I J}
  (f : R →+* S) (h : I ≤ comap f J) {π : R} (x : AdicCompletion (span {π}) R)
attribute [local simp] span_singleton_pow mem_span_singleton mul_smul

/-- For a ring homomorphism f: R → S carrying the ideal I into J, the induced ring homomorphism
from the I-adic completion of R to the J-adic completion of S. -/
@[irreducible] def adicMap : AdicCompletion I R →+* AdicCompletion J S := liftRingHom J (fun n ↦
  (quotientMap _ f (by grw [← le_comap_pow, ← h])).comp (evalₐ I n)) fun e ↦ by
  ext x; simp [evalₐ, ← x.2 e, eval]; rcases x.1 _; rfl

@[simp] lemma evalₐ_adicMap n x : evalₐ J n (adicMap f h x) = quotientMap _ f (by grw [h,
    le_comap_pow]) (evalₐ I n x) := by rw [adicMap]; generalize_proofs; aesop

@[simp] lemma adicMap_algebraMap (x : R) : adicMap f h x = f x := ext_evalₐ (by simp)

variable {A B} [CommRing A] [CommRing B] [Algebra A R] (i : R →+* B) (f : M → B →+* B) (m : M)

/-- The action of a monoid M on a ring B by ring endomorphisms given by a family f(m) with f(1)
the identity and f(ab) = f(a)∘f(b). -/
abbrev actionOfHoms (h1 : f 1 = 1) (hm : ∀ a b, f (a * b) = f a * f b) :=
  { compHom B ⟨⟨f, h1⟩, hm⟩ with smul := (f ·) }

@[simp] lemma smul_natCast' (n : ℕ) : m • (n : R) = n := smul_algebraMap m n

/-- The M-action on B given by endomorphisms f(m) compatible with the action on R along i: R →
B, when endomorphisms of B are determined on the image of i. -/
abbrev extendAction (hf : ∀ m a, f m (i a) = i (m • a)) (h : ∀ {F G : B →+* B},
  (∀ a, F (i a) = G (i a)) → F = G) := actionOfHoms M f (by aesop) fun _ _ ↦ h (by simp [*])

/-- The action of M on the localisation B = R[1/x] extending the action on R, given that the
image in B of m·x is a unit for every m in M. -/
abbrev locAction x [Algebra R B] [Away x B] (h : ∀ m,
  IsUnit ((algebraMap R B).comp (toRingHom M R m)
  x)) := extendAction M _ (Away.lift x <| h ·) (by simp) (ringHom_ext (.powers x) <| RingHom.ext ·)

instance (priority := 50) wittAction p [Fact p.Prime] : MulSemiringAction M (WittVector p R) :=
  actionOfHoms M (WittVector.map <| toRingHom M R ·) (by aesop) (by aesop)

variable {M} [SMul M A]

instance : SMulDistribClass M R R := ⟨by simp⟩

@[simp] lemma smul_algebraMap_eq_algebraMap_smul [SMulDistribClass M A R] (a : A) : m • (a : R) =
  ↑(m • a) := (smul' ..).symm

lemma smulDistribClass_of_tower [Algebra A B] [Algebra B R] [IsScalarTower A B R]
  [MulSemiringAction M B] [SMulDistribClass M A B] (h : ∀ {m : M} (b : B), m • (b : R) = ↑(m • b)) :
  SMulDistribClass M A R := ⟨by simp [*, smul_def, IsScalarTower.algebraMap_eq A B R]⟩


@[local simp] lemma evalₐ_eq_zero n : cast π ^ n ∣ x ↔ evalₐ _ n x = 0 := by simpa [evalₐ,
  -quotientEquivAlgOfEq_coe_eq_factorₐ] using! congr(x ∈ $(pow_smul_top_eq_ker_eval ⟨{π}, by simp⟩))

lemma exists_approx n : ∃ y : R, cast π ^ n ∣ x - y := ⟨(x.evalₐ _ n).out, by simp⟩

variable {x} {X} [AddCommGroup X] [Module R X]

lemma pow_dvd_iff {n} {y : R} : (π : type_of% x) ^ n ∣ y ↔ π ^ n ∣ y := by
  simp [Quotient.eq_zero_iff_mem]

lemma eq_zero_of_forall_pow_dvd (h : ∀ n, cast π ^ n ∣ x) : x = 0 := ext_evalₐ (by aesop)

lemma isAdicComplete : IsAdicComplete (span {(π : type_of% x)}) (type_of% x) := by
  simpa using isAdicComplete_self (span {π}) ⟨{π}, by simp⟩

/-- If multiplication by the natural number n is injective on the R-module X, then it is
injective on the n-adic completion of X. -/
lemma isSMulRegular_completion {n : ℕ} (h : IsSMulRegular X n) :
  IsSMulRegular (AdicCompletion (span {(n : R)}) X) n :=
  (map_ext _ (by tauto)).subst ((ofPowSMul_injective _ 1).comp (congr _ (.ofInjective
  (n : Module.End R X) h ≪≫ₗ .ofEq _ _ (by ext; simp [Submodule.ideal_span_singleton_smul,
  Submodule.pointwise_smul_def, Nat.cast_smul_eq_nsmul]))).injective)
