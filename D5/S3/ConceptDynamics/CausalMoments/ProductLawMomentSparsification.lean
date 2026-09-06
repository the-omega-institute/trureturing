/- GID: D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction]
   digest: Sequential exact moment compression sparsifies both factors of a rational product law while preserving all nominated joint moments, and hence all finite linear data constraints and one target within the product family. -/

import D5.S3.ConceptDynamics.CausalMoments.ReducedResponseTableMoments

/- Library audit (2026-09-06): the existing Markovian event theorem gives the
   Boolean fixed-component slice. Here arbitrary rational coefficients cover
   a finite vector of joint data and query moments. Reuse exists_momentCompression
   and original-carrier sparse laws; do not convexify the product-law family.
   The second slice is recomputed using the already compressed first factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.CausalMoments.ProductLawMomentSparsification

open scoped BigOperators
open D5.S0.Certificates.RationalFarkas
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSupportReduction
open D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw
open D5.S3.ConceptDynamics.CausalMoments.ReducedResponseTableMoments

variable {Left Right : Type*} [Fintype Left] [Fintype Right]

/-- Any rational product-law moment is linear in the left law at fixed right law. -/
theorem product_linearObjective_eq_left
    (left : FiniteResponseLaw Left) (right : FiniteResponseLaw Right)
    (coefficient : Left × Right → ℚ) :
    linearObjective coefficient (productResponseLaw left right).mass =
      linearObjective (fun a => ∑ b, right.mass b * coefficient (a, b)) left.mass := by
  unfold linearObjective
  simp only [productResponseLaw, productResponseMass, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The symmetric fixed-left slice, expressed on the unchanged right carrier. -/
theorem product_linearObjective_eq_right
    (left : FiniteResponseLaw Left) (right : FiniteResponseLaw Right)
    (coefficient : Left × Right → ℚ) :
    linearObjective coefficient (productResponseLaw left right).mass =
      linearObjective (fun b => ∑ a, left.mass a * coefficient (a, b)) right.mass := by
  unfold linearObjective
  simp only [productResponseLaw, productResponseMass, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

variable [DecidableEq Left] [DecidableEq Right]

/-- Every finite vector of rational joint moments has an exactly equivalent
product-law witness with each factor supported on at most d+1 atoms, where d
is the number of retained moments. The joint law itself need not be preserved. -/
theorem productLaw_moment_sparse_replacements
    {Feature : Type*} [Fintype Feature]
    (left : FiniteResponseLaw Left) (right : FiniteResponseLaw Right)
    (feature : Left × Right → Feature → ℚ) :
    ∃ leftSparse : FiniteResponseLaw Left, ∃ rightSparse : FiniteResponseLaw Right,
      (finiteLawSupport leftSparse).card ≤ Fintype.card Feature + 1 ∧
      (finiteLawSupport rightSparse).card ≤ Fintype.card Feature + 1 ∧
      ∀ coordinate,
        linearObjective (fun pair => feature pair coordinate)
            (productResponseLaw leftSparse rightSparse).mass =
          linearObjective (fun pair => feature pair coordinate)
            (productResponseLaw left right).mass := by
  classical
  let leftFeature : Left → Feature → ℚ :=
    fun a coordinate => ∑ b, right.mass b * feature (a, b) coordinate
  obtain ⟨leftCompression⟩ := exists_momentCompression left leftFeature
  let leftSparse := leftCompression.sparseLaw
  have left_preserves : ∀ coordinate,
      linearObjective (fun pair => feature pair coordinate)
          (productResponseLaw leftSparse right).mass =
        linearObjective (fun pair => feature pair coordinate)
          (productResponseLaw left right).mass := by
    intro coordinate
    rw [product_linearObjective_eq_left, product_linearObjective_eq_left]
    exact momentCompression_sparse_coordinate_eq leftCompression coordinate
  let rightFeature : Right → Feature → ℚ :=
    fun b coordinate => ∑ a, leftSparse.mass a * feature (a, b) coordinate
  obtain ⟨rightCompression⟩ := exists_momentCompression right rightFeature
  let rightSparse := rightCompression.sparseLaw
  have right_preserves : ∀ coordinate,
      linearObjective (fun pair => feature pair coordinate)
          (productResponseLaw leftSparse rightSparse).mass =
        linearObjective (fun pair => feature pair coordinate)
          (productResponseLaw leftSparse right).mass := by
    intro coordinate
    rw [product_linearObjective_eq_right, product_linearObjective_eq_right]
    exact momentCompression_sparse_coordinate_eq rightCompression coordinate
  refine ⟨leftSparse, rightSparse, ?_, ?_, ?_⟩
  · exact (momentCompression_sparse_support_card_le leftCompression).trans leftCompression.card_le
  · exact (momentCompression_sparse_support_card_le rightCompression).trans rightCompression.card_le
  · intro coordinate
    exact (right_preserves coordinate).trans (left_preserves coordinate)

/-- All m linear data rows and one nominated objective remain exactly preserved
inside the two-component product family, with at most m+2 support points in each
factor. No global convexity or free selection of feasible factors is assumed. -/
theorem product_linear_problem_sparse_witness
    {Constraint : Type*} [Fintype Constraint]
    (A : Constraint → Left × Right → ℚ) (b : Constraint → ℚ)
    (objective : Left × Right → ℚ)
    (left : FiniteResponseLaw Left) (right : FiniteResponseLaw Right)
    (feasible : LinearFeasible A b (productResponseLaw left right).mass) :
    ∃ leftSparse : FiniteResponseLaw Left, ∃ rightSparse : FiniteResponseLaw Right,
      (finiteLawSupport leftSparse).card ≤ Fintype.card Constraint + 2 ∧
      (finiteLawSupport rightSparse).card ≤ Fintype.card Constraint + 2 ∧
      LinearFeasible A b (productResponseLaw leftSparse rightSparse).mass ∧
      linearObjective objective (productResponseLaw leftSparse rightSparse).mass =
        linearObjective objective (productResponseLaw left right).mass := by
  obtain ⟨leftSparse, rightSparse, left_card, right_card, preserves⟩ :=
    productLaw_moment_sparse_replacements left right (linearRowQueryFeature A objective)
  refine ⟨leftSparse, rightSparse, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using left_card
  · simpa [Nat.add_assoc] using right_card
  · intro constraint
    have row_eq : linearObjective (A constraint) (productResponseLaw leftSparse rightSparse).mass =
        linearObjective (A constraint) (productResponseLaw left right).mass :=
      preserves (some constraint)
    change linearObjective (A constraint) (productResponseLaw leftSparse rightSparse).mass ≤ b constraint
    rw [row_eq]
    exact feasible constraint
  · exact preserves none

#print axioms productLaw_moment_sparse_replacements
#print axioms product_linear_problem_sparse_witness

end D5.S3.ConceptDynamics.CausalMoments.ProductLawMomentSparsification
