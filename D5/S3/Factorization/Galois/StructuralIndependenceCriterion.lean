/- GID: D5/S3/Factorization/Galois/StructuralIndependenceCriterion
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/StructuralIndependenceCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Trivial field intersection makes the canonical Galois restriction product bijective. -/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.SetTheory.Cardinal.Finite

/- Library-search audit trail (2026-08-26):
   * Repository searches for intermediate-field intersections, linear
     disjointness, composita, and paired Galois restrictions found no exact D5
     theorem or restriction-product primitive.
   * The similarly named `Polynomial.Gal.restrictProd` is on splitting fields of
     polynomial products and is not the source carrier.
   * Exact pinned-Mathlib components are
     `IntermediateField.LinearDisjoint.iff_inf_eq_bot`,
     `IntermediateField.restrictNormalHom_ker`,
     `IntermediateField.fixingSubgroup_sup`,
     `IsGalois.card_aut_eq_finrank`, `Nat.card_prod`, and
     `Nat.bijective_iff_injective_and_card`; they are applied below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Factorization.Galois.StructuralIndependenceCriterion

/-- Restrict an automorphism of the compositum to both named Galois
subextensions. -/
def restrictionProduct
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A B : IntermediateField F E) [Normal F A] [Normal F B] :
    Gal(E / F) →* Gal(A / F) × Gal(B / F) :=
  MonoidHom.prod (AlgEquiv.restrictNormalHom A)
    (AlgEquiv.restrictNormalHom B)

/-- For finite Galois subextensions generating the ambient compositum, trivial
intersection makes the canonical pair of restrictions a bijection and is
equivalent to linear disjointness. Distinct extension names alone do not imply
independence: every nontrivial proper Galois subextension gives a dependent
pair with the ambient extension. -/
theorem structural_independence_criterion
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (A B : IntermediateField F E) [IsGalois F A] [IsGalois F B]
    (hspan : A ⊔ B = ⊤) :
    (A ⊓ B = ⊥ ->
      Function.Bijective (restrictionProduct A B) /\
        A.LinearDisjoint B) /\
    (forall C : IntermediateField F E,
      IsGalois F C → C ≠ ⊥ → C ≠ ⊤ →
        exists L1 L2 : IntermediateField F E,
          IsGalois F L1 /\ IsGalois F L2 /\
            L1 ≠ L2 /\ L1 ⊓ L2 ≠ ⊥ /\
              Not (L1.LinearDisjoint L2)) := by
  have galoisSup : IsGalois F ↥(A ⊔ B : IntermediateField F E) :=
    { to_isSeparable := inferInstance
      to_normal := inferInstance }
  have galoisTop : IsGalois F (⊤ : IntermediateField F E) := hspan ▸ galoisSup
  letI : IsGalois F E := isGalois_iff_isGalois_top.mp galoisTop
  constructor
  · intro hintersection
    have hdisjoint : A.LinearDisjoint B :=
      IntermediateField.LinearDisjoint.of_inf_eq_bot hintersection
    have hinjective : Function.Injective (restrictionProduct A B) := by
      apply (MonoidHom.ker_eq_bot_iff (restrictionProduct A B)).mp
      rw [restrictionProduct, MonoidHom.ker_prod,
        IntermediateField.restrictNormalHom_ker,
        IntermediateField.restrictNormalHom_ker,
        ← IntermediateField.fixingSubgroup_sup, hspan,
        IntermediateField.fixingSubgroup_top]
    have hfinrank :
        Module.finrank F E = Module.finrank F A * Module.finrank F B := by
      have h := hdisjoint.finrank_sup
      rw [hspan, IntermediateField.finrank_top'] at h
      exact h
    have hcard :
        Nat.card Gal(E / F) = Nat.card (Gal(A / F) × Gal(B / F)) := by
      rw [IsGalois.card_aut_eq_finrank, Nat.card_prod,
        IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
      exact hfinrank
    have hbijective : Function.Bijective (restrictionProduct A B) :=
      (Nat.bijective_iff_injective_and_card (restrictionProduct A B)).mpr
        ⟨hinjective, hcard⟩
    exact ⟨hbijective, hdisjoint⟩
  · intro C hC hCbot hCtop
    letI : IsGalois F C := hC
    refine ⟨⊤, C, galoisTop, hC, hCtop.symm, ?_, ?_⟩
    · simpa using hCbot
    · intro hdisjoint
      exact hCbot (by simpa using hdisjoint.inf_eq_bot)

#print axioms structural_independence_criterion

end D5.S3.Factorization.Galois.StructuralIndependenceCriterion
