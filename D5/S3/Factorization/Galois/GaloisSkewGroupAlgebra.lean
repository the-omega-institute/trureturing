/- GID: D5/S3/Factorization/Galois/GaloisSkewGroupAlgebra
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/GaloisSkewGroupAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The canonical skew action of a finite Galois group is the full endomorphism algebra. -/

import Mathlib.Algebra.SkewMonoidAlgebra.Lift
import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! The classical finite Galois skew-group algebra acts as the full endomorphism algebra.
Artin independence recovers coefficients; the Galois degree computes both dimensions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Factorization.Galois.GaloisSkewGroupAlgebra

variable (K L G : Type*) [Field K] [Field L] [Algebra K L]
  [Group G] [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- Coefficients act by left multiplication and group elements by their given action. -/
def skewAction : SkewMonoidAlgebra L G →ₐ[K] Module.End K L :=
  SkewMonoidAlgebra.liftNCAlgHom (Algebra.lsmul K K L)
    (DistribMulAction.toModuleEnd K L) (by
      intro a g
      ext x
      exact (smul_mul' g a x).symm)

private theorem skewAction_single_apply (g : G) (a x : L) :
    skewAction K L G (SkewMonoidAlgebra.single g a) x = a * (g • x) := by
  change (SkewMonoidAlgebra.liftNC (Algebra.lsmul K K L).toAddMonoidHom
    (DistribMulAction.toModuleEnd K L) (SkewMonoidAlgebra.single g a)) x = _
  rw [SkewMonoidAlgebra.liftNC_single]
  rfl

private theorem skewAction_eq_linearCombination (s : SkewMonoidAlgebra L G) :
    skewAction K L G s = Finsupp.linearCombination L
      (fun g : G => (MulSemiringAction.toAlgHom K L g).toLinearMap) s.coeff := by
  change (s.coeff.sum fun g a =>
    Algebra.lsmul K K L a * DistribMulAction.toModuleEnd K L g) = _
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro g _
  ext x
  rfl

private theorem skewAction_injective : Function.Injective (skewAction K L G) := by
  let : FaithfulSMul G L := IsGaloisGroup.faithful K
  have independent : LinearIndependent L
      (fun g : G => (MulSemiringAction.toAlgHom K L g).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap K L L).comp
      (MulSemiringAction.toAlgHom K L) (MulSemiringAction.toAlgHom_injective K L)
  intro s t h
  apply SkewMonoidAlgebra.coeff_injective
  apply independent
  simpa only [← skewAction_eq_linearCombination K L G] using h

/-- The finite Galois skew-group algebra, acting canonically on the field, is its
full algebra of linear endomorphisms over the fixed base field. -/
def equiv [Finite G] : SkewMonoidAlgebra L G ≃ₐ[K] Module.End K L := by
  letI : Fintype G := Fintype.ofFinite G
  letI : FiniteDimensional K L := IsGaloisGroup.finiteDimensional G K L
  let coefficients : SkewMonoidAlgebra L G ≃ₗ[K] (G →₀ L) :=
    SkewMonoidAlgebra.coeffLinearEquiv
  letI : FiniteDimensional K (SkewMonoidAlgebra L G) :=
    Module.Finite.equiv coefficients.symm
  have card_degree : Fintype.card G = Module.finrank K L := by
    simpa only [Nat.card_eq_fintype_card] using IsGaloisGroup.card_eq_finrank G K L
  have dimensions : Module.finrank K (SkewMonoidAlgebra L G) =
      Module.finrank K (Module.End K L) := by
    calc
      _ = Module.finrank K (G →₀ L) := coefficients.finrank_eq
      _ = Fintype.card G * Module.finrank K L := by
        rw [Module.finrank, Module.finrank, rank_finsupp, ← Cardinal.mk_toNat_eq_card,
          Cardinal.toNat_mul, Cardinal.toNat_lift, Cardinal.toNat_lift]
      _ = Module.finrank K L * Module.finrank K L := by rw [card_degree]
      _ = Module.finrank K (Module.End K L) :=
        (Module.finrank_linearMap K K L L).symm
  exact AlgEquiv.ofBijective (skewAction K L G)
    ⟨skewAction_injective K L G,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dimensions
        (f := (skewAction K L G).toLinearMap)).mp
        (skewAction_injective K L G)⟩

/-- The canonical algebra equivalence retains the prescribed action of each single term. -/
theorem canonical_equivalence [Finite G] :
    ∃ e : SkewMonoidAlgebra L G ≃ₐ[K] Module.End K L,
      e.toAlgHom = skewAction K L G ∧
        ∀ (g : G) (a x : L), e (SkewMonoidAlgebra.single g a) x = a * (g • x) := by
  exact ⟨equiv K L G, rfl, skewAction_single_apply K L G⟩

#print axioms equiv
#print axioms canonical_equivalence

end D5.S3.Factorization.Galois.GaloisSkewGroupAlgebra
