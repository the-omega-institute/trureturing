/- GID: D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Certified disjoint counterfactual dependency sets induce product response laws under independent source blocks, using the standard full-assignment partition equivalence and existing finite pushforward factorization. -/

import D5.S3.ConceptDynamics.PartialIdentification.InterventionExogenousLocality
import D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
import Mathlib.Logic.Equiv.Prod

/- Library audit (2026-09-05): reuse Mathlib DependsOn,
   dependsOn_iff_exists_comp, and Equiv.piEquivPiSubtypeProd. Reuse the
   repository productResponseLaw, pushforwardResponseLaw, and
   independent_exogenous_components_induce_markovian_response_law.
   Source blocks are independent by the supplied product law. The dependency
   compiler certifies that the queried maps are coordinatewise at this split.
   Distinct graph c-components alone are not a premise sufficient for this theorem.
   Dependence inside either source block is unrestricted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.SeparatedCounterfactualSourceFactorization

open D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics
open D5.S3.ConceptDynamics.PartialIdentification.InterventionExogenousLocality
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization

variable {Source Noise : Type*} [DecidableEq Source] [Fintype Source] [Fintype Noise]

/-- Evaluate the original full-assignment readouts under two independent source
blocks. The standard equivalence covers every assignment in Source → Noise;
unused coordinates remain in the complement block. -/
noncomputable def partitionedReadoutLaw
    {LeftResponse RightResponse : Type*}
    [Fintype LeftResponse] [Fintype RightResponse]
    [DecidableEq LeftResponse] [DecidableEq RightResponse]
    (support : Finset Source)
    (leftLaw : FiniteResponseLaw ({i : Source // i ∈ support} → Noise))
    (rightLaw : FiniteResponseLaw ({i : Source // i ∉ support} → Noise))
    (leftReadout : (Source → Noise) → LeftResponse)
    (rightReadout : (Source → Noise) → RightResponse) :
    FiniteResponseLaw (LeftResponse × RightResponse) :=
  pushforwardResponseLaw (productResponseLaw leftLaw rightLaw)
    (fun source =>
      (leftReadout ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ support) (fun _ => Noise)).symm source),
       rightReadout ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ support) (fun _ => Noise)).symm source)))

/-- Semantic locality supplies the two reduced response maps required by the
existing product-pushforward theorem. Disjoint support certificates suffice;
no converse from overlapping supports to dependence is asserted. -/
theorem separated_readouts_factorize
    {LeftResponse RightResponse : Type*}
    [Fintype LeftResponse] [Fintype RightResponse]
    [DecidableEq LeftResponse] [DecidableEq RightResponse]
    [Nonempty LeftResponse] [Nonempty RightResponse]
    (leftSupport rightSupport : Finset Source)
    (leftLaw : FiniteResponseLaw ({i : Source // i ∈ leftSupport} → Noise))
    (rightLaw : FiniteResponseLaw ({i : Source // i ∉ leftSupport} → Noise))
    (leftReadout : (Source → Noise) → LeftResponse)
    (rightReadout : (Source → Noise) → RightResponse)
    (left_local : DependsOn leftReadout (leftSupport : Set Source))
    (right_local : DependsOn rightReadout (rightSupport : Set Source))
    (separated : Disjoint leftSupport rightSupport) :
    IsMarkovianTwoComponentLaw
      (partitionedReadoutLaw leftSupport leftLaw rightLaw leftReadout rightReadout).mass := by
  have right_complement : DependsOn rightReadout ((leftSupport : Set Source)ᶜ) := by
    apply DependsOn.mono _ right_local
    intro i hi
    change i ∉ leftSupport
    intro hleft
    exact (Finset.disjoint_left.mp separated) hleft hi
  rcases dependsOn_iff_exists_comp.mp left_local with ⟨leftMap, left_eq⟩
  rcases dependsOn_iff_exists_comp.mp right_complement with ⟨rightMap, right_eq⟩
  let split := Equiv.piEquivPiSubtypeProd (fun i => i ∈ leftSupport) (fun _ => Noise)
  have response_maps :
      (fun source => (leftReadout (split.symm source), rightReadout (split.symm source))) =
        (fun source => (leftMap source.1, rightMap source.2)) := by
    funext source
    apply Prod.ext
    · rw [left_eq]
      change leftMap ((split (split.symm source)).1) = leftMap source.1
      rw [split.apply_symm_apply]
    · rw [right_eq]
      change rightMap ((split (split.symm source)).2) = rightMap source.2
      rw [split.apply_symm_apply]
  change IsMarkovianTwoComponentLaw
    (pushforwardResponseLaw (productResponseLaw leftLaw rightLaw)
      (fun source => (leftReadout (split.symm source), rightReadout (split.symm source)))).mass
  rw [response_maps]
  exact independent_exogenous_components_induce_markovian_response_law
    leftLaw rightLaw leftMap rightMap

/-- The separated response law assigns each joint cell the product of its
actual marginal masses. This specializes to simultaneous benefit at (true,true). -/
theorem separated_readouts_cell_eq_product
    {LeftResponse RightResponse : Type*}
    [Fintype LeftResponse] [Fintype RightResponse]
    [DecidableEq LeftResponse] [DecidableEq RightResponse]
    [Nonempty LeftResponse] [Nonempty RightResponse]
    (leftSupport rightSupport : Finset Source)
    (leftLaw : FiniteResponseLaw ({i : Source // i ∈ leftSupport} → Noise))
    (rightLaw : FiniteResponseLaw ({i : Source // i ∉ leftSupport} → Noise))
    (leftReadout : (Source → Noise) → LeftResponse)
    (rightReadout : (Source → Noise) → RightResponse)
    (left_local : DependsOn leftReadout (leftSupport : Set Source))
    (right_local : DependsOn rightReadout (rightSupport : Set Source))
    (separated : Disjoint leftSupport rightSupport)
    (left : LeftResponse) (right : RightResponse) :
    let joint := (partitionedReadoutLaw leftSupport leftLaw rightLaw leftReadout rightReadout).mass
    joint (left, right) = leftResponseMarginal joint left * rightResponseMarginal joint right := by
  rcases separated_readouts_factorize leftSupport rightSupport leftLaw rightLaw
    leftReadout rightReadout left_local right_local separated with ⟨l, r, factorized⟩
  dsimp only
  rw [factorized, leftResponseMarginal_productResponseMass,
    rightResponseMarginal_productResponseMass, r.total, l.total]
  simp only [productResponseMass, mul_one, one_mul]

/-- End-to-end bridge: parent-indexed SCM evaluation, local source contracts,
finite counterfactual supports, disjointness, and independent source-block laws
produce a factorized Boolean joint-event law on the original source carrier. -/
theorem compiled_counterfactual_events_factorize
    {n : Nat} {Value LeftQuery RightQuery : Type*}
    [Fintype LeftQuery] [Fintype RightQuery]
    (model : StructuralModel n Value (Source → Noise)) (topological : TopologicalOrder model)
    (direct : Fin n → Finset Source) (locality : ExogenousLocality model direct)
    (leftInterventions : LeftQuery → Finset (Fin n))
    (leftAssigned : LeftQuery → Fin n → Value) (leftObserved : LeftQuery → Fin n)
    (leftEvent : (LeftQuery → Value) → Bool)
    (rightInterventions : RightQuery → Finset (Fin n))
    (rightAssigned : RightQuery → Fin n → Value) (rightObserved : RightQuery → Fin n)
    (rightEvent : (RightQuery → Value) → Bool)
    (separated : Disjoint
      (counterfactualSupport model direct leftInterventions leftObserved)
      (counterfactualSupport model direct rightInterventions rightObserved))
    (leftLaw : FiniteResponseLaw
      ({i : Source // i ∈ counterfactualSupport model direct leftInterventions leftObserved} → Noise))
    (rightLaw : FiniteResponseLaw
      ({i : Source // i ∉ counterfactualSupport model direct leftInterventions leftObserved} → Noise)) :
    IsMarkovianTwoComponentLaw
      (partitionedReadoutLaw
        (counterfactualSupport model direct leftInterventions leftObserved) leftLaw rightLaw
        (fun u => leftEvent (counterfactualReadout model topological leftInterventions leftAssigned leftObserved u))
        (fun u => rightEvent (counterfactualReadout model topological rightInterventions rightAssigned rightObserved u))).mass := by
  apply separated_readouts_factorize
    (counterfactualSupport model direct leftInterventions leftObserved)
    (counterfactualSupport model direct rightInterventions rightObserved)
    leftLaw rightLaw
    (fun u => leftEvent (counterfactualReadout model topological leftInterventions leftAssigned leftObserved u))
    (fun u => rightEvent (counterfactualReadout model topological rightInterventions rightAssigned rightObserved u))
  · exact dependsOn_iff_factorsThrough.mpr
      (counterfactualEvent_factorsThrough model topological direct locality
        leftInterventions leftAssigned leftObserved leftEvent)
  · exact dependsOn_iff_factorsThrough.mpr
      (counterfactualEvent_factorsThrough model topological direct locality
        rightInterventions rightAssigned rightObserved rightEvent)
  · exact separated

#print axioms separated_readouts_factorize
#print axioms separated_readouts_cell_eq_product
#print axioms compiled_counterfactual_events_factorize

end D5.S3.ConceptDynamics.PartialIdentification.SeparatedCounterfactualSourceFactorization
