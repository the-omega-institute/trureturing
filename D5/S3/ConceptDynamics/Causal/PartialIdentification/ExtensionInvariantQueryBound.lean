/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/ExtensionInvariantQueryBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/ExtensionInvariantQueryBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equivariant relabelings of finite response-signature programs preserve feasibility, event values, and the complete identified set. -/

import D5.S3.ConceptDynamics.Causal.PartialIdentification.CausalOrderLinearProgram

/- Library-search audit trail (2026-09-03):
   * The 2026 causal-order framework claims that bounds do not depend on which
     total extension of the query-implied partial order is selected.
   * `CausalOrderLinearProgram` supplies the finite response-signature LP, but
     no repository theorem transports identified sets across two order-indexed
     signature carriers.
   * This module isolates the exact proof obligation: a signature equivalence
     must preserve every constraint row, right-hand side, and query evaluation.
     Under that payload, the full attainable query set is invariant. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.ExtensionInvariantQueryBound

open scoped BigOperators
open D5.S3.ConceptDynamics.Causal.FiniteLinearCausalIdentification
open D5.S3.ConceptDynamics.Causal.PartialIdentification.CanonicalResponseSignature

/-- Relabel a response-signature mass vector along a carrier equivalence. -/
def relabelMass
    {LeftSignature RightSignature : Type*}
    (equivalence : LeftSignature ≃ RightSignature)
    (mass : LeftSignature -> ℚ) : RightSignature -> ℚ :=
  fun right => mass (equivalence.symm right)

/-- Relabeling forward and then backward returns the original mass vector. -/
theorem relabelMass_symm
    {LeftSignature RightSignature : Type*}
    (equivalence : LeftSignature ≃ RightSignature)
    (mass : LeftSignature -> ℚ) :
    relabelMass equivalence.symm (relabelMass equivalence mass) = mass := by
  funext left
  simp [relabelMass]

/-- Event mass is invariant under a signature equivalence that preserves the
Boolean query evaluation. -/
theorem signatureEventMass_relabel
    {LeftSignature RightSignature : Type*}
    [Fintype LeftSignature] [Fintype RightSignature]
    (equivalence : LeftSignature ≃ RightSignature)
    (leftEvent : LeftSignature -> Bool)
    (rightEvent : RightSignature -> Bool)
    (event_preserved : forall left,
      rightEvent (equivalence left) = leftEvent left)
    (mass : LeftSignature -> ℚ) :
    signatureEventMass (relabelMass equivalence mass) rightEvent =
      signatureEventMass mass leftEvent := by
  unfold signatureEventMass
  calc
    (∑ right,
        if rightEvent right then
          relabelMass equivalence mass right else 0) =
      ∑ left,
        if rightEvent (equivalence left) then
          relabelMass equivalence mass (equivalence left) else 0 := by
        symm
        exact Equiv.sum_comp equivalence
          (fun right =>
            if rightEvent right then
              relabelMass equivalence mass right else 0)
    _ = ∑ left, if leftEvent left then mass left else 0 := by
      apply Finset.sum_congr rfl
      intro left _
      rw [event_preserved left]
      simp [relabelMass]

/-- One compiled constraint row has the same value after an equivariant
signature relabeling. -/
theorem constraintRow_relabel
    {LeftSignature RightSignature Constraint : Type*}
    [Fintype LeftSignature] [Fintype RightSignature]
    [Fintype Constraint]
    (leftProblem : FiniteLinearCausalProblem LeftSignature Constraint)
    (rightProblem : FiniteLinearCausalProblem RightSignature Constraint)
    (equivalence : LeftSignature ≃ RightSignature)
    (row_preserved : forall constraint left,
      rightProblem.row constraint (equivalence left) =
        leftProblem.row constraint left)
    (mass : LeftSignature -> ℚ)
    (constraint : Constraint) :
    (∑ right,
        rightProblem.row constraint right *
          relabelMass equivalence mass right) =
      ∑ left,
        leftProblem.row constraint left * mass left := by
  calc
    (∑ right,
        rightProblem.row constraint right *
          relabelMass equivalence mass right) =
      ∑ left,
        rightProblem.row constraint (equivalence left) *
          relabelMass equivalence mass (equivalence left) := by
        symm
        exact Equiv.sum_comp equivalence
          (fun right =>
            rightProblem.row constraint right *
              relabelMass equivalence mass right)
    _ = ∑ left,
        leftProblem.row constraint left * mass left := by
      apply Finset.sum_congr rfl
      intro left _
      rw [row_preserved constraint left]
      simp [relabelMass]

/-- Equivariant row relabeling preserves and reflects feasibility. -/
theorem feasible_relabel_iff
    {LeftSignature RightSignature Constraint : Type*}
    [Fintype LeftSignature] [Fintype RightSignature]
    [Fintype Constraint]
    (leftProblem : FiniteLinearCausalProblem LeftSignature Constraint)
    (rightProblem : FiniteLinearCausalProblem RightSignature Constraint)
    (equivalence : LeftSignature ≃ RightSignature)
    (row_preserved : forall constraint left,
      rightProblem.row constraint (equivalence left) =
        leftProblem.row constraint left)
    (rhs_preserved : forall constraint,
      rightProblem.rhs constraint = leftProblem.rhs constraint)
    (mass : LeftSignature -> ℚ) :
    Feasible leftProblem mass <->
      Feasible rightProblem (relabelMass equivalence mass) := by
  unfold Feasible D5.S0.Certificates.RationalFarkas.LinearFeasible
  constructor
  · intro feasible constraint
    rw [constraintRow_relabel
      leftProblem rightProblem equivalence row_preserved mass constraint]
    rw [rhs_preserved constraint]
    exact feasible constraint
  · intro feasible constraint
    rw [← constraintRow_relabel
      leftProblem rightProblem equivalence row_preserved mass constraint]
    rw [← rhs_preserved constraint]
    exact feasible constraint

/-- Two order-indexed response-signature programs have the same full identified
set whenever a carrier equivalence preserves all observational rows and the
counterfactual event evaluation. This is the reusable invariance theorem that a
concrete pair of compatible total orders must instantiate. -/
theorem identified_set_invariant_under_signature_equivalence
    {LeftSignature RightSignature Constraint : Type*}
    [Fintype LeftSignature] [Fintype RightSignature]
    [Fintype Constraint]
    (leftProblem : FiniteLinearCausalProblem LeftSignature Constraint)
    (rightProblem : FiniteLinearCausalProblem RightSignature Constraint)
    (leftEvent : LeftSignature -> Bool)
    (rightEvent : RightSignature -> Bool)
    (equivalence : LeftSignature ≃ RightSignature)
    (row_preserved : forall constraint left,
      rightProblem.row constraint (equivalence left) =
        leftProblem.row constraint left)
    (rhs_preserved : forall constraint,
      rightProblem.rhs constraint = leftProblem.rhs constraint)
    (event_preserved : forall left,
      rightEvent (equivalence left) = leftEvent left)
    (target : ℚ) :
    (exists mass : LeftSignature -> ℚ,
        Feasible leftProblem mass /\
          signatureEventMass mass leftEvent = target) <->
      exists mass : RightSignature -> ℚ,
        Feasible rightProblem mass /\
          signatureEventMass mass rightEvent = target := by
  constructor
  · rintro ⟨mass, feasible, query_eq⟩
    refine ⟨relabelMass equivalence mass, ?_, ?_⟩
    · exact (feasible_relabel_iff
        leftProblem rightProblem equivalence
        row_preserved rhs_preserved mass).mp feasible
    · rw [signatureEventMass_relabel
        equivalence leftEvent rightEvent event_preserved mass]
      exact query_eq
  · rintro ⟨mass, feasible, query_eq⟩
    have row_preserved_symm : forall constraint right,
        leftProblem.row constraint (equivalence.symm right) =
          rightProblem.row constraint right := by
      intro constraint right
      simpa using (row_preserved constraint (equivalence.symm right)).symm
    have rhs_preserved_symm : forall constraint,
        leftProblem.rhs constraint = rightProblem.rhs constraint := by
      intro constraint
      exact (rhs_preserved constraint).symm
    have event_preserved_symm : forall right,
        leftEvent (equivalence.symm right) = rightEvent right := by
      intro right
      simpa using (event_preserved (equivalence.symm right)).symm
    refine ⟨relabelMass equivalence.symm mass, ?_, ?_⟩
    · exact (feasible_relabel_iff
        rightProblem leftProblem equivalence.symm
        row_preserved_symm rhs_preserved_symm mass).mp feasible
    · rw [signatureEventMass_relabel
        equivalence.symm rightEvent leftEvent
        event_preserved_symm mass]
      exact query_eq

#print axioms signatureEventMass_relabel
#print axioms feasible_relabel_iff
#print axioms identified_set_invariant_under_signature_equivalence

end D5.S3.ConceptDynamics.Causal.PartialIdentification.ExtensionInvariantQueryBound
