/- GID: D5/S3/ConceptDynamics/Contracts/ContractRefinement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Contracts/ContractRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strong contracts imply their weaker contract obligations. -/

import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-21).
   * `rg -n "contract|assume|guarantee|Subseteq|⊆" D5 --glob '*.lean'`
     found no theorem packaging contract refinement over an implementation
     function and two assumption/guarantee pairs.
   * Pinned Mathlib's set-subset membership lemmas were inspected; the direct
     subset applications below are the complete available support.
   * No existing family object is duplicated: the source primitives are sets
     of inputs and outputs plus an implementation map. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Contracts.ContractRefinement

/-- A module satisfying the stronger assumption/guarantee contract also
satisfies the weaker contract. -/
theorem strong_contract_refines_weak
    {I O : Type*} (A APrime : Set I) (G GPrime : Set O)
    (implementation : I → O)
    (h_assumptions : A ⊆ APrime)
    (h_guarantees : GPrime ⊆ G)
    (h_strong : ∀ i ∈ APrime, implementation i ∈ GPrime) :
    ∀ i ∈ A, implementation i ∈ G := by
  intro i hi
  exact h_guarantees (h_strong i (h_assumptions hi))

/-- A concrete Boolean implementation witnesses satisfiability of the strong
and weak contract hypotheses. -/
example :
    let A : Set Bool := ∅
    let APrime : Set Bool := Set.univ
    let G : Set Bool := Set.univ
    let GPrime : Set Bool := Set.univ
    let implementation : Bool → Bool := id
    A ⊆ APrime ∧
      GPrime ⊆ G ∧
      (∀ i ∈ APrime, implementation i ∈ GPrime) := by
  simp

example : Set Bool := Set.univ

#print axioms strong_contract_refines_weak

end D5.S3.ConceptDynamics.Contracts.ContractRefinement
