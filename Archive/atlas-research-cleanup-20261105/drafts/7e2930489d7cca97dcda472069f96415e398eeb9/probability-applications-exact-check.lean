import D5.S3.Combinatorics.CircularWords.ThreeSpecifiedDeletions
import D5.S3.ConceptDynamics.Faithfulness.ModelRelativeCompletenessDifferenceCriterion
import Mathlib.Data.Finsupp.Basic

open D5.S3.Combinatorics.CircularWords
open CircularDeletionTransport DeletionReadoutReconstruction ThreeSpecifiedDeletions
open D5.S3.ConceptDynamics.Faithfulness.ModelRelativeCompletenessDifferenceCriterion

set_option autoImplicit false

theorem joint_pushforward_injective {α : Type*} [DecidableEq α] {A : Finset α} (hA : 4 ≤ A.card)
    {a b c : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective
      (Finsupp.mapDomain
        (fun C : SupportedCircle A => (delete a C.1, delete b C.1, delete c C.1)) :
          (SupportedCircle A →₀ ℚ) → (Cycle α × Cycle α × Cycle α) →₀ ℚ) := by
  apply Finsupp.mapDomain_injective
  intro C D he
  apply Subtype.ext
  exact reconstruct_three hA ha hb hc hab hac hbc C.2.1 D.2.1 C.2.2 D.2.2
    (congrArg (fun p => p.1) he)
    (congrArg (fun p => p.2.1) he)
    (congrArg (fun p => p.2.2) he)

-- The model parameter is a subset of the additive signed-mass space.
-- Instantiating it with nonnegative normalized masses gives the probability case.
theorem model_difference_application {X I Y : Type*} (d : I → X → Y)
    (M : Set (X →₀ ℚ)) (hne : M.Nonempty) :
    modelRelativeComplete
      (fun i v => Finsupp.mapDomain (d i) v) M ↔
    jointDifferenceResidual
      (fun i (v : X →₀ ℚ) => Finsupp.mapDomain (d i) v) ∩ modelDifference M = {0} := by
  exact model_relative_completeness_difference_criterion
    (fun i => Finsupp.mapDomain.addMonoidHom (d i)) M hne

#check @joint_pushforward_injective
#check @model_difference_application
#print axioms joint_pushforward_injective
#print axioms model_difference_application
