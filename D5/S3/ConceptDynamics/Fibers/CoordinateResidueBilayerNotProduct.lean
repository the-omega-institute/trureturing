/- GID: D5/S3/ConceptDynamics/Fibers/CoordinateResidueBilayerNotProduct
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/CoordinateResidueBilayerNotProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dependent coordinate residues need not admit a uniform product decomposition. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'coordinate_residue_bilayer_not_product' D5
     Golden/Frozen/accepted` returned no matches.
   * The required `fiber|Sigma|product.*decomposition|trivializ` search under
     `D5/S3/ConceptDynamics` found `ConceptFiberDecomposition` and its two positive
     wrappers in `Fibers`, but no obstruction to a product decomposition.
   * `ConceptFiberDecomposition.lean` was read in full. Its theorem
     `concept_fiber_decomposition` is reused for the dependent decomposition.
   * Pinned Mathlib searches found `Equiv.sigmaEquivProdOfEquiv` for the sufficient
     uniform-fiber condition, and `Finite.of_injective`, `Fintype.card_congr`, and
     `Fintype.card_prod` for the finite counterexample. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.CoordinateResidueBilayerNotProduct

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- The false coordinate has one residual point, while the true coordinate has two. -/
def coordinateResidue : Bool -> Type
  | false => Unit
  | true => Bool

/-- Each residue in the counterexample is finite. -/
instance coordinateResidueFintype (b : Bool) : Fintype (coordinateResidue b) := by
  cases b
  · change Fintype Unit
    infer_instance
  · change Fintype Bool
    infer_instance

/-- The three-point object obtained as the dependent sum of the unequal residues. -/
def BilayerObject := Sigma coordinateResidue

/-- The counterexample object is finite because its base and every residue are finite. -/
instance bilayerObjectFintype : Fintype BilayerObject := by
  change Fintype (Sigma coordinateResidue)
  infer_instance

/-- The counterexample concept reads the coordinate of a dependent pair. -/
def bilayerConcept : Concept BilayerObject Bool := Sigma.fst

/-- The three-point bilayer has its canonical dependent-fiber decomposition, but it is
not equivalent to a product of its two-point coordinate type with any uniform residue. -/
theorem coordinate_residue_bilayer_not_product :
    Nonempty (BilayerObject ≃ Σ b : Bool, ConceptFiber bilayerConcept b) ∧
      ∀ R : Type, ¬ Nonempty (BilayerObject ≃ Bool × R) := by
  constructor
  · exact concept_fiber_decomposition bilayerConcept
  · intro R productDecomposition
    rcases productDecomposition with ⟨productEquiv⟩
    let embed : R → BilayerObject := fun r => productEquiv.symm (false, r)
    have embed_injective : Function.Injective embed := by
      intro r s hrs
      exact (Prod.mk.inj (productEquiv.symm.injective hrs)).2
    letI : Finite R := Finite.of_injective embed embed_injective
    letI : Fintype R := Fintype.ofFinite R
    have card_eq := Fintype.card_congr productEquiv
    have bilayer_card : Fintype.card BilayerObject = 3 := by decide
    rw [bilayer_card, Fintype.card_prod] at card_eq
    norm_num at card_eq
    omega

/-- A chosen equivalence from every concept fiber to one residue type is precisely enough
extra structure to turn the dependent decomposition into a product decomposition. -/
theorem product_decomposition_of_uniform_residues
    {X B R : Type _} (q : Concept X B)
    (uniform : ∀ b, ConceptFiber q b ≃ R) :
    Nonempty (X ≃ B × R) := by
  rcases concept_fiber_decomposition q with ⟨dependent⟩
  exact ⟨dependent.trans (Equiv.sigmaEquivProdOfEquiv uniform)⟩

example : ¬ Nonempty (BilayerObject ≃ Bool × Unit) :=
  (coordinate_residue_bilayer_not_product.2 Unit)

#print axioms coordinate_residue_bilayer_not_product

end D5.S3.ConceptDynamics.Fibers.CoordinateResidueBilayerNotProduct
