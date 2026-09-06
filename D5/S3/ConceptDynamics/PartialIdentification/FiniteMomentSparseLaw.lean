/- GID: D5/S3/ConceptDynamics/PartialIdentification/FiniteMomentSparseLaw
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/FiniteMomentSparseLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/ConceptDynamics/PartialIdentification/FiniteMomentSupportReduction]
   digest: The small Caratheodory latent witness pushes forward to a normalized law on the original response carrier that preserves every finite LP constraint and the exact query value, closing identified-set preservation on the original causal semantics. -/

import D5.S3.ConceptDynamics.PartialIdentification.FiniteMomentSupportReduction

/- This module closes the semantic transport left implicit by a latent-only
   support statement. The pushed law lives on the original atom carrier, so its
   feasibility and objective are judged by the unchanged original LP. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.PartialIdentification.FiniteMomentSparseLaw

open scoped BigOperators
open D5.S0.Certificates.RationalFarkas
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.CanonicalResponseSignature
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.FiniteMomentSupportReduction

/-- Expectation of any finite rational coefficient is unchanged when a finite
law is pushed through a deterministic map, after pulling the coefficient back
along that map. -/
theorem pushforward_linearObjective
    {Source Response : Type*}
    [Fintype Source] [Fintype Response] [DecidableEq Response]
    (law : FiniteResponseLaw Source)
    (responseOf : Source → Response)
    (coefficient : Response → ℚ) :
    linearObjective coefficient (pushforwardResponseLaw law responseOf).mass =
      linearObjective (fun source => coefficient (responseOf source)) law.mass := by
  classical
  change
    (∑ response, coefficient response *
      pushforwardSignatureMass law.mass responseOf response) =
      ∑ source, coefficient (responseOf source) * law.mass source
  unfold pushforwardSignatureMass
  calc
    (∑ response, coefficient response *
        (∑ source,
          if responseOf source = response then law.mass source else 0)) =
      ∑ response, ∑ source,
        coefficient response *
          (if responseOf source = response then law.mass source else 0) := by
        apply Finset.sum_congr rfl
        intro response _
        rw [Finset.mul_sum]
    _ = ∑ source, ∑ response,
        coefficient response *
          (if responseOf source = response then law.mass source else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ source, coefficient (responseOf source) * law.mass source := by
      apply Finset.sum_congr rfl
      intro source _
      simp

/-- Push the sparse latent law back onto the unchanged original response
carrier. Its support is contained in the selected source atoms. -/
noncomputable def MomentCompression.sparseLaw
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature] [DecidableEq Atom]
    {law : FiniteResponseLaw Atom} {feature : Atom → Feature → ℚ}
    (compression : MomentCompression law feature) : FiniteResponseLaw Atom :=
  pushforwardResponseLaw compression.latentLaw compression.sourceAtom

/-- Any original-carrier linear objective of the sparse pushforward is exactly
the pulled-back latent objective. -/
theorem MomentCompression.sparseLaw_linearObjective_eq
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature] [DecidableEq Atom]
    {law : FiniteResponseLaw Atom} {feature : Atom → Feature → ℚ}
    (compression : MomentCompression law feature)
    (coefficient : Atom → ℚ) :
    linearObjective coefficient compression.sparseLaw.mass =
      linearObjective
        (fun state => coefficient (compression.sourceAtom state))
        compression.latentLaw.mass := by
  exact pushforward_linearObjective
    compression.latentLaw compression.sourceAtom coefficient

/-- For a row/query compression, pushing the latent witness back to the original
atom carrier preserves every original LP inequality. -/
theorem MomentCompression.sparseLawLinearFeasible
    {Constraint Atom : Type*}
    [Fintype Constraint] [Fintype Atom] [DecidableEq Atom]
    (A : Constraint → Atom → ℚ) (b : Constraint → ℚ)
    (objective : Atom → ℚ) (law : FiniteResponseLaw Atom)
    (compression : MomentCompression law (linearRowQueryFeature A objective))
    (feasible : LinearFeasible A b law.mass) :
    LinearFeasible A b compression.sparseLaw.mass := by
  have latent_feasible :=
    compression.latentLinearFeasible A b objective law feasible
  intro constraint
  change linearObjective (A constraint) compression.sparseLaw.mass ≤ b constraint
  rw [compression.sparseLaw_linearObjective_eq (A constraint)]
  change
    (∑ state,
      A constraint (compression.sourceAtom state) *
        compression.latentLaw.mass state) ≤ b constraint
  exact latent_feasible constraint

/-- The original-carrier sparse pushforward also preserves the exact nominated
query value. -/
theorem MomentCompression.sparseLawLinearObjective_eq
    {Constraint Atom : Type*}
    [Fintype Constraint] [Fintype Atom] [DecidableEq Atom]
    (A : Constraint → Atom → ℚ) (objective : Atom → ℚ)
    (law : FiniteResponseLaw Atom)
    (compression : MomentCompression law (linearRowQueryFeature A objective)) :
    linearObjective objective compression.sparseLaw.mass =
      linearObjective objective law.mass := by
  calc
    linearObjective objective compression.sparseLaw.mass =
        linearObjective
          (fun state => objective (compression.sourceAtom state))
          compression.latentLaw.mass :=
      compression.sparseLaw_linearObjective_eq objective
    _ = linearObjective objective law.mass :=
      compression.latentLinearObjective_eq A objective law

/-- Every feasible query value in the original finite causal LP has a feasible
law on the same original response carrier whose generating latent support is at
most one plus the joint row/query affine profile rank. -/
theorem finite_linear_problem_sparse_original_witness
    {Constraint Atom : Type*}
    [Fintype Constraint] [Fintype Atom] [DecidableEq Atom]
    (A : Constraint → Atom → ℚ) (b : Constraint → ℚ)
    (objective : Atom → ℚ) (law : FiniteResponseLaw Atom)
    (feasible : LinearFeasible A b law.mass) :
    ∃ compression : MomentCompression law (linearRowQueryFeature A objective),
      LinearFeasible A b compression.sparseLaw.mass ∧
      linearObjective objective compression.sparseLaw.mass =
        linearObjective objective law.mass ∧
      Fintype.card compression.profiles ≤
        linearProblemProfileRank A objective + 1 := by
  obtain ⟨compression⟩ :=
    exists_momentCompression law (linearRowQueryFeature A objective)
  exact ⟨compression,
    compression.sparseLawLinearFeasible A b objective law feasible,
    compression.sparseLawLinearObjective_eq A objective law,
    compression.linearRowQuery_profileRank_card_le A objective law⟩

/-- Coarser original-carrier endpoint using only the number of LP rows. -/
theorem finite_linear_problem_sparse_original_witness_card_le
    {Constraint Atom : Type*}
    [Fintype Constraint] [Fintype Atom] [DecidableEq Atom]
    (A : Constraint → Atom → ℚ) (b : Constraint → ℚ)
    (objective : Atom → ℚ) (law : FiniteResponseLaw Atom)
    (feasible : LinearFeasible A b law.mass) :
    ∃ compression : MomentCompression law (linearRowQueryFeature A objective),
      LinearFeasible A b compression.sparseLaw.mass ∧
      linearObjective objective compression.sparseLaw.mass =
        linearObjective objective law.mass ∧
      Fintype.card compression.profiles ≤ Fintype.card Constraint + 2 := by
  obtain ⟨compression⟩ :=
    exists_momentCompression law (linearRowQueryFeature A objective)
  exact ⟨compression,
    compression.sparseLawLinearFeasible A b objective law feasible,
    compression.sparseLawLinearObjective_eq A objective law,
    compression.linearRowQuery_card_le A objective law⟩

#print axioms pushforward_linearObjective
#print axioms finite_linear_problem_sparse_original_witness
#print axioms finite_linear_problem_sparse_original_witness_card_le

end D5.S3.ConceptDynamics.PartialIdentification.FiniteMomentSparseLaw
