/- GID: D5/S3/ConceptDynamics/PartialIdentification/ReducedResponseTableMoments
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/ReducedResponseTableMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/ConceptDynamics/PartialIdentification/FiniteMomentSparseLaw]
   digest: Three cells per Boolean response row determine its complete law; rational moment compression preserves every row with 3k+1 support points, or every row and one further query with 3k+2. -/

import D5.S3.ConceptDynamics.PartialIdentification.FiniteMomentSparseLaw
import D5.S3.ConceptDynamics.PartialIdentification.FiniteConditionalResponseTable

/- Library audit (2026-09-06): reuse MomentCompression, its original-carrier
   sparseLaw, coordinate_eq, sourceAtom, and existing tableEvaluationLaw.
   The omitted fourth cell is recovered from the normalization of each actual
   row law. Finite support below counts nonzero masses on the original carrier.
   No independence between different rows or full-table-law preservation is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.PartialIdentification.ReducedResponseTableMoments

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.CanonicalResponseSignature
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.QuaternaryResponseTableCoding
open D5.S3.ConceptDynamics.PartialIdentification.FiniteMomentSupportReduction
open D5.S3.ConceptDynamics.PartialIdentification.FiniteMomentSparseLaw
open D5.S3.ConceptDynamics.PartialIdentification.FiniteConditionalResponseTable

/-- Nonzero mass support on the unchanged finite response carrier. -/
def finiteLawSupport {Atom : Type*} [Fintype Atom]
    (law : FiniteResponseLaw Atom) : Finset Atom :=
  Finset.univ.filter (fun atom => law.mass atom ≠ 0)

/-- The original-carrier sparse law has no more support points than latent profiles. -/
theorem momentCompression_sparse_support_card_le
    {Atom Feature : Type*} [Fintype Atom] [DecidableEq Atom] [Fintype Feature]
    {law : FiniteResponseLaw Atom} {feature : Atom → Feature → ℚ}
    (compression : MomentCompression law feature) :
    (finiteLawSupport compression.sparseLaw).card ≤ compression.profiles.card := by
  classical
  have contained : finiteLawSupport compression.sparseLaw ⊆
      Finset.univ.image compression.sourceAtom := by
    intro atom hatom
    by_contra outside
    have misses : ∀ state : compression.profiles, compression.sourceAtom state ≠ atom := by
      intro state equal
      exact outside (Finset.mem_image.mpr ⟨state, Finset.mem_univ _, equal⟩)
    have zero : compression.sparseLaw.mass atom = 0 := by
      change (∑ state : compression.profiles,
        if compression.sourceAtom state = atom then compression.latentLaw.mass state else 0) = 0
      simp [misses]
    exact (Finset.mem_filter.mp hatom).2 zero
  calc
    (finiteLawSupport compression.sparseLaw).card ≤
        (Finset.univ.image compression.sourceAtom).card := Finset.card_le_card contained
    _ ≤ (Finset.univ : Finset compression.profiles).card := Finset.card_image_le
    _ = compression.profiles.card := by simp

/-- Every retained feature expectation survives pushforward to the original carrier. -/
theorem momentCompression_sparse_coordinate_eq
    {Atom Feature : Type*} [Fintype Atom] [DecidableEq Atom] [Fintype Feature]
    {law : FiniteResponseLaw Atom} {feature : Atom → Feature → ℚ}
    (compression : MomentCompression law feature) (coordinate : Feature) :
    linearObjective (fun atom => feature atom coordinate) compression.sparseLaw.mass =
      linearObjective (fun atom => feature atom coordinate) law.mass := by
  rw [compression.sparseLaw_linearObjective_eq]
  simpa [linearObjective, mul_comm] using compression.coordinate_eq coordinate

variable {Covariate : Type*} [Fintype Covariate] [DecidableEq Covariate]

/-- Retain digits 0,1,2 in every row of the existing quaternary response encoding.
Digit 3 is recovered from row normalization. -/
def reducedTableFeature (table : Covariate → Bool × Bool)
    (coordinate : Covariate × Fin 3) : ℚ :=
  if table coordinate.1 = responsePairDigitEquiv.symm coordinate.2.castSucc then 1 else 0

/-- The first three cells determine a normalized Boolean response-pair law. -/
theorem boolean_pair_law_eq_of_first_three
    (first second : FiniteResponseLaw (Bool × Bool))
    (agree : ∀ digit : Fin 3,
      first.mass (responsePairDigitEquiv.symm digit.castSucc) =
        second.mass (responsePairDigitEquiv.symm digit.castSucc)) :
    first.mass = second.mass := by
  have h00 : first.mass (false, false) = second.mass (false, false) := agree 0
  have h01 : first.mass (false, true) = second.mass (false, true) := agree 1
  have h10 : first.mass (true, false) = second.mass (true, false) := agree 2
  have first_total := first.total
  have second_total := second.total
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at first_total second_total
  funext response
  rcases response with ⟨control, treated⟩
  cases control <;> cases treated
  · exact h00
  · exact h01
  · exact h10
  · linarith

/-- A reduced feature moment is exactly the corresponding actual row cell. -/
theorem reducedTableFeature_moment_eq_cell
    (law : FiniteResponseLaw (Covariate → Bool × Bool))
    (c : Covariate) (digit : Fin 3) :
    linearObjective (fun table => reducedTableFeature table (c, digit)) law.mass =
      (tableEvaluationLaw law c).mass (responsePairDigitEquiv.symm digit.castSucc) := by
  unfold linearObjective
  change (∑ table, (if table c = responsePairDigitEquiv.symm digit.castSucc then
      (1 : ℚ) else 0) * law.mass table) =
    ∑ table, if table c = responsePairDigitEquiv.symm digit.castSucc then law.mass table else 0
  apply Finset.sum_congr rfl
  intro table _
  split <;> simp_all

/-- Equality of the 3k retained moments preserves all four cells in every row. -/
theorem reducedTableMoments_preserve_rows
    (first second : FiniteResponseLaw (Covariate → Bool × Bool))
    (agree : ∀ coordinate : Covariate × Fin 3,
      linearObjective (fun table => reducedTableFeature table coordinate) first.mass =
        linearObjective (fun table => reducedTableFeature table coordinate) second.mass) :
    ∀ c, (tableEvaluationLaw first c).mass = (tableEvaluationLaw second c).mass := by
  intro c
  apply boolean_pair_law_eq_of_first_three
  intro digit
  simpa only [reducedTableFeature_moment_eq_cell] using agree (c, digit)

/-- Every full table law has a replacement with all row laws unchanged and
at most 3k+1 nonzero original-table atoms. Cross-row coupling may change. -/
theorem exists_three_cell_table_compression
    (law : FiniteResponseLaw (Covariate → Bool × Bool)) :
    ∃ sparse : FiniteResponseLaw (Covariate → Bool × Bool),
      (finiteLawSupport sparse).card ≤ 3 * Fintype.card Covariate + 1 ∧
      ∀ c, (tableEvaluationLaw sparse c).mass = (tableEvaluationLaw law c).mass := by
  classical
  obtain ⟨compression⟩ := exists_momentCompression law reducedTableFeature
  refine ⟨compression.sparseLaw, ?_, ?_⟩
  · calc
      (finiteLawSupport compression.sparseLaw).card ≤ compression.profiles.card :=
        momentCompression_sparse_support_card_le compression
      _ ≤ Fintype.card (Covariate × Fin 3) + 1 := compression.card_le
      _ = 3 * Fintype.card Covariate + 1 := by simp [Nat.mul_comm]
  · apply reducedTableMoments_preserve_rows
    intro coordinate
    exact momentCompression_sparse_coordinate_eq compression coordinate

/-- Preserve every row and one arbitrary additional rational table query with
at most 3k+2 nonzero atoms on the original table carrier. -/
theorem exists_three_cell_query_compression
    (law : FiniteResponseLaw (Covariate → Bool × Bool))
    (query : (Covariate → Bool × Bool) → ℚ) :
    ∃ sparse : FiniteResponseLaw (Covariate → Bool × Bool),
      (finiteLawSupport sparse).card ≤ 3 * Fintype.card Covariate + 2 ∧
      (∀ c, (tableEvaluationLaw sparse c).mass = (tableEvaluationLaw law c).mass) ∧
      linearObjective query sparse.mass = linearObjective query law.mass := by
  classical
  let rows := fun (coordinate : Covariate × Fin 3)
      (table : Covariate → Bool × Bool) => reducedTableFeature table coordinate
  obtain ⟨compression⟩ := exists_momentCompression law (linearRowQueryFeature rows query)
  refine ⟨compression.sparseLaw, ?_, ?_, ?_⟩
  · calc
      (finiteLawSupport compression.sparseLaw).card ≤ compression.profiles.card :=
        momentCompression_sparse_support_card_le compression
      _ ≤ Fintype.card (Option (Covariate × Fin 3)) + 1 := compression.card_le
      _ = 3 * Fintype.card Covariate + 2 := by simp [Nat.mul_comm, Nat.add_assoc]
  · apply reducedTableMoments_preserve_rows
    intro coordinate
    simpa only [linearRowQueryFeature, rows] using
      momentCompression_sparse_coordinate_eq compression (some coordinate)
  · exact compression.sparseLawLinearObjective_eq rows query law

#print axioms boolean_pair_law_eq_of_first_three
#print axioms exists_three_cell_table_compression
#print axioms exists_three_cell_query_compression

end D5.S3.ConceptDynamics.PartialIdentification.ReducedResponseTableMoments
