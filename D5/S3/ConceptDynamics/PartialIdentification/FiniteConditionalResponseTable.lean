/- GID: D5/S3/ConceptDynamics/PartialIdentification/FiniteConditionalResponseTable
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/FiniteConditionalResponseTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite rational conditional response family has one covariate-independent full-table realization; two independent mechanism tables reproduce all conditional product kernels simultaneously. -/

import D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping

/- Library audit (2026-09-06): reuse independentSourceLaw and its exact
   source-restriction theorem, FiniteResponseLaw, productResponseLaw, and
   product_pushforward_factorizes. A singleton restriction supplies the
   coordinate marginal. The model class allows arbitrary cross-row dependence;
   row independence is used only to construct one attaining table law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.FiniteConditionalResponseTable

open scoped BigOperators
open D5.S3.ConceptDynamics.PartialIdentification.CanonicalResponseSignature
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping

variable {Covariate Response : Type*} [Fintype Covariate] [DecidableEq Covariate]
  [Fintype Response] [DecidableEq Response]

/-- The distribution of one row of a full response-table disturbance. -/
noncomputable def tableEvaluationLaw
    (tableLaw : FiniteResponseLaw (Covariate → Response)) (c : Covariate) :
    FiniteResponseLaw Response :=
  pushforwardResponseLaw tableLaw (fun table => table c)

/-- All prescribed row laws are realized by the same product-distributed table.
There is no restriction on dependence among coordinates inside Response. -/
theorem tableEvaluationLaw_independentSource
    (kernel : Covariate → FiniteResponseLaw Response) (c : Covariate) :
    (tableEvaluationLaw (independentSourceLaw kernel) c).mass = (kernel c).mass := by
  classical
  let Row := {i : Covariate // i ∈ ({c} : Finset Covariate)}
  let center : Row := ⟨c, by simp⟩
  have all_center : ∀ i : Row, i = center := by
    intro i
    apply Subtype.ext
    exact Finset.mem_singleton.mp i.2
  letI : Subsingleton Row := ⟨fun i j => (all_center i).trans (all_center j).symm⟩
  let oneRow : (Row → Response) ≃ Response :=
    { toFun := fun table => table center
      invFun := fun r _ => r
      left_inv := by
        intro table
        funext i
        change table center = table i
        rw [all_center i]
      right_inv := fun _ => rfl }
  let rowLaw := independentSourceLaw (fun i : Row => kernel i.1)
  have restriction := independentSource_pushforward_restrict kernel ({c} : Finset Covariate)
    (fun table => table c) (fun table => table center) (fun _ => rfl)
  change pushforwardSignatureMass (independentSourceLaw kernel).mass (fun table => table c) = _
  rw [restriction]
  funext r
  change (∑ table : Row → Response,
      if table center = r then rowLaw.mass table else 0) = (kernel c).mass r
  calc
    (∑ table : Row → Response, if table center = r then rowLaw.mass table else 0) =
        ∑ a : Response, if (oneRow.symm a) center = r then
          rowLaw.mass (oneRow.symm a) else 0 :=
      (oneRow.symm.sum_comp
        (fun table => if table center = r then rowLaw.mass table else 0)).symm
    _ = ∑ a : Response, if a = r then (kernel c).mass a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      have mass_eq : rowLaw.mass (oneRow.symm a) = (kernel c).mass a := by
        change (∏ i : Row, (kernel i.1).mass a) = (kernel c).mass a
        exact Fintype.prod_subsingleton (fun i : Row => (kernel i.1).mass a) center
      change (if a = r then rowLaw.mass (oneRow.symm a) else 0) = _
      rw [mass_eq]
    _ = (kernel c).mass r := by simp

/-- One table law realizes every finite conditional response kernel at once. -/
theorem finite_conditional_table_realization
    (kernel : Covariate → FiniteResponseLaw Response) :
    ∃ tableLaw : FiniteResponseLaw (Covariate → Response),
      ∀ c, (tableEvaluationLaw tableLaw c).mass = (kernel c).mass :=
  ⟨independentSourceLaw kernel, tableEvaluationLaw_independentSource kernel⟩

variable {Left Right : Type*} [Fintype Left] [Fintype Right]
  [DecidableEq Left] [DecidableEq Right]

/-- Two complete mechanism disturbances. Their laws may couple different rows
arbitrarily. Independence between mechanisms is imposed by fixedNoiseSourceLaw. -/
structure FixedNoisePairModel (Covariate Left Right : Type*)
    [Fintype Covariate] [DecidableEq Covariate] [Fintype Left] [Fintype Right] where
  leftTableLaw : FiniteResponseLaw (Covariate → Left)
  rightTableLaw : FiniteResponseLaw (Covariate → Right)

/-- A covariate root and two mutually independent full-table disturbances. -/
def fixedNoiseSourceLaw
    (weight : FiniteResponseLaw Covariate) (model : FixedNoisePairModel Covariate Left Right) :
    FiniteResponseLaw (Covariate × ((Covariate → Left) × (Covariate → Right))) :=
  productResponseLaw weight (productResponseLaw model.leftTableLaw model.rightTableLaw)

/-- Select both mechanism responses at the same covariate value. -/
noncomputable def selectedPairLaw
    (weight : FiniteResponseLaw Covariate) (model : FixedNoisePairModel Covariate Left Right) :
    FiniteResponseLaw (Covariate × (Left × Right)) :=
  pushforwardResponseLaw (fixedNoiseSourceLaw weight model)
    (fun source => (source.1, (source.2.1 source.1, source.2.2 source.1)))

/-- Exact joint law for arbitrary table disturbances. The division-free identity
also applies to zero-weight strata; it only identifies conditional probabilities
by division when the covariate mass is positive. -/
theorem selectedPairLaw_mass
    (weight : FiniteResponseLaw Covariate) (model : FixedNoisePairModel Covariate Left Right)
    (c : Covariate) (left : Left) (right : Right) :
    (selectedPairLaw weight model).mass (c, (left, right)) =
      weight.mass c *
        ((tableEvaluationLaw model.leftTableLaw c).mass left *
          (tableEvaluationLaw model.rightTableLaw c).mass right) := by
  classical
  have inner := congrFun
    (product_pushforward_factorizes model.leftTableLaw.mass model.rightTableLaw.mass
      (fun table => table c) (fun table => table c)) (left, right)
  change pushforwardSignatureMass (fixedNoiseSourceLaw weight model).mass
    (fun source => (source.1, (source.2.1 source.1, source.2.2 source.1))) (c, (left, right)) = _
  unfold pushforwardSignatureMass
  rw [Fintype.sum_prod_type]
  have select_row : ∀ d : Covariate,
      (∑ tables : (Covariate → Left) × (Covariate → Right),
        if (d, (tables.1 d, tables.2 d)) = (c, (left, right)) then
          (fixedNoiseSourceLaw weight model).mass (d, tables) else 0) =
      if d = c then weight.mass c *
        pushforwardSignatureMass
          (productResponseMass model.leftTableLaw.mass model.rightTableLaw.mass)
          (fun tables => (tables.1 c, tables.2 c)) (left, right) else 0 := by
    intro d
    by_cases same : d = c
    · subst d
      simp only [if_pos rfl]
      unfold pushforwardSignatureMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tables _
      by_cases hit : (tables.1 c, tables.2 c) = (left, right)
      · simp [fixedNoiseSourceLaw, productResponseLaw, productResponseMass, hit]
      · simp [fixedNoiseSourceLaw, productResponseLaw, productResponseMass, hit]
    · simp [same]
  simp_rw [select_row]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change weight.mass c *
    pushforwardSignatureMass
      (productResponseMass model.leftTableLaw.mass model.rightTableLaw.mass)
      (fun tables => (tables.1 c, tables.2 c)) (left, right) = _
  exact congrArg (fun value : ℚ => weight.mass c * value) inner

/-- A canonical attaining model for two arbitrary conditional response families. -/
def canonicalFixedNoisePair
    (leftKernel : Covariate → FiniteResponseLaw Left)
    (rightKernel : Covariate → FiniteResponseLaw Right) :
    FixedNoisePairModel Covariate Left Right where
  leftTableLaw := independentSourceLaw leftKernel
  rightTableLaw := independentSourceLaw rightKernel

/-- The canonical model simultaneously reproduces every specified stratum cell. -/
theorem canonicalFixedNoisePair_selected_mass
    (weight : FiniteResponseLaw Covariate)
    (leftKernel : Covariate → FiniteResponseLaw Left)
    (rightKernel : Covariate → FiniteResponseLaw Right)
    (c : Covariate) (left : Left) (right : Right) :
    (selectedPairLaw weight (canonicalFixedNoisePair leftKernel rightKernel)).mass
      (c, (left, right)) = weight.mass c * ((leftKernel c).mass left * (rightKernel c).mass right) := by
  rw [selectedPairLaw_mass]
  simp only [canonicalFixedNoisePair, tableEvaluationLaw_independentSource]

/-- Existence holds on one common source space for every stratum simultaneously. -/
theorem simultaneous_conditional_product_realization
    (weight : FiniteResponseLaw Covariate)
    (leftKernel : Covariate → FiniteResponseLaw Left)
    (rightKernel : Covariate → FiniteResponseLaw Right) :
    ∃ model : FixedNoisePairModel Covariate Left Right,
      ∀ c left right, (selectedPairLaw weight model).mass (c, (left, right)) =
        weight.mass c * ((leftKernel c).mass left * (rightKernel c).mass right) :=
  ⟨canonicalFixedNoisePair leftKernel rightKernel,
    canonicalFixedNoisePair_selected_mass weight leftKernel rightKernel⟩

#print axioms tableEvaluationLaw_independentSource
#print axioms finite_conditional_table_realization
#print axioms selectedPairLaw_mass
#print axioms simultaneous_conditional_product_realization

end D5.S3.ConceptDynamics.PartialIdentification.FiniteConditionalResponseTable
