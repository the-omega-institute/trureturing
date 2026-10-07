/- GID: D5/S3/HomologicalAlgebra/Solid/KProjectiveCoproduct
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/KProjectiveCoproduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.ComplexAdjunction

/-! Closure under arbitrary coproducts for an unbounded resolution construction. -/

noncomputable section
open CategoryTheory Limits HomologicalComplex

namespace CWSolid

set_option backward.isDefEq.respectTransparency false in
/-- Homotopies out of a coproduct of complexes assemble degreewise. -/
def homotopyFromCoproduct
    {C : Type*} [Category* C] [Preadditive C]
    {I : Type*} [HasColimitsOfShape (Discrete I) C]
    {ι : Type*} {c : ComplexShape ι} (K : I → HomologicalComplex C c)
    {L : HomologicalComplex C c} {f g : ∐ K ⟶ L}
    (h : ∀ a, Homotopy (Sigma.ι K a ≫ f) (Sigma.ι K a ≫ g)) :
    Homotopy f g := by
  let H i := isColimitOfHasCoproductOfPreservesColimit (eval C c i) K
  let hh (i j : ι) : (∐ K).X i ⟶ L.X j :=
    (H i).desc (Cofan.mk (L.X j) (fun a => (h a).hom i j))
  have fac (a : I) (i j : ι) : (Sigma.ι K a).f i ≫ hh i j = (h a).hom i j :=
    (H i).fac _ ⟨a⟩
  refine ⟨hh, ?_, ?_⟩
  · intro i j hij
    apply (H i).hom_ext
    intro ⟨a⟩
    change (Sigma.ι K a).f i ≫ hh i j = (Sigma.ι K a).f i ≫ 0
    rw [fac, (h a).zero _ _ hij, comp_zero]
  · intro i
    apply (H i).hom_ext
    intro ⟨a⟩
    change (Sigma.ι K a).f i ≫ f.f i =
      (Sigma.ι K a).f i ≫ (dNext i hh + prevD i hh + g.f i)
    rw [Preadditive.comp_add, Preadditive.comp_add]
    change (Sigma.ι K a).f i ≫ f.f i =
      (Sigma.ι K a).f i ≫ ((∐ K).d i (c.next i) ≫ hh (c.next i) i) +
        (Sigma.ι K a).f i ≫ (hh i (c.prev i) ≫ L.d (c.prev i) i) +
        (Sigma.ι K a).f i ≫ g.f i
    rw [← Category.assoc, (Sigma.ι K a).comm, Category.assoc, fac,
      ← Category.assoc, fac]
    exact (h a).comm i

/-- Arbitrary coproducts of K-projective cochain complexes are K-projective.
The members may have unrelated bounds, and may themselves be unbounded. -/
theorem isKProjective_coproduct
    {C : Type*} [Category* C] [Abelian C]
    {I : Type*} [HasColimitsOfShape (Discrete I) C]
    (K : I → CochainComplex C ℤ) [∀ a, (K a).IsKProjective] :
    CochainComplex.IsKProjective (∐ K) where
  nonempty_homotopy_zero {L} f hL := by
    refine ⟨homotopyFromCoproduct K (fun a => ?_)⟩
    exact (CochainComplex.IsKProjective.homotopyZero (Sigma.ι K a ≫ f) hL).trans
      (Homotopy.ofEq (by simp))

end CWSolid
