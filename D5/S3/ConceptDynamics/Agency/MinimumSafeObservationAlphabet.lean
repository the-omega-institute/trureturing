/- GID: D5/S3/ConceptDynamics/Agency/MinimumSafeObservationAlphabet
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/MinimumSafeObservationAlphabet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Safe-compatible partitions determine the exact minimum safe observation alphabet. -/

import D5.S3.ConceptDynamics.Agency.DeterministicSafePolicyExistence
import Mathlib.Order.Bounds.Basic

/- Library-search audit trail (2026-09-01):
   * The atom occurs only in its `residual-open` ledger entry, with no coverage
     GID or formalization receipt. Searches for safe observers, common safe
     actions, compatible fibers, alphabets, partitions, and minimum label
     counts found no D5 theorem with the requested cardinal minimum.
   * The exact repository primitive `deterministic_safe_policy_exists_iff`
     proves that common legal actions on every effective observation fiber are
     equivalent to a deterministic safe policy. It is imported and applied
     directly rather than reproved. Same-section atoms 71.1 and 73.1 are also
     residual-open and have no neighboring GID to import.
   * Pinned Mathlib searches for safe partitions and safe observers found no
     domain theorem. `IsLeast` from `Mathlib.Order.Bounds.Basic` supplies the
     standard minimum interface; no third-party dependency is needed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.MinimumSafeObservationAlphabet

open D5.S3.ConceptDynamics.Agency.DeterministicSafePolicyExistence

/-- A surjective finite readout is a safe-compatible partition when every
effective fiber admits one action legal at every state in that fiber. -/
def SafeCompatiblePartition {X A : Type*} (legal : X -> Set A)
    (alphabetSize : Nat) : Prop :=
  exists readout : X -> Fin alphabetSize,
    Function.Surjective readout /\
      forall z : Set.range readout,
        ({action | forall x, readout x = z.1 -> action ∈ legal x} : Set A).Nonempty

/-- A finite observation alphabet supports deterministic one-step safety when
all of its values are realized and a policy on the effective values chooses an
action legal at every compatible state. -/
def SupportsDeterministicSafePolicy {X A : Type*} (legal : X -> Set A)
    (alphabetSize : Nat) : Prop :=
  exists readout : X -> Fin alphabetSize,
    Function.Surjective readout /\
      exists policy : Set.range readout -> A,
        forall z x, readout x = z.1 -> policy z ∈ legal x

/-- For each exact alphabet size, safe-compatible fibers and deterministic
one-step safe policies are equivalent. -/
theorem supports_deterministic_safe_policy_iff_safe_compatible_partition
    {X A : Type*} (legal : X -> Set A) (alphabetSize : Nat) :
    SupportsDeterministicSafePolicy legal alphabetSize ↔
      SafeCompatiblePartition legal alphabetSize := by
  constructor
  · rintro ⟨readout, surjective, policy, safe⟩
    refine ⟨readout, surjective, ?_⟩
    exact (deterministic_safe_policy_exists_iff readout legal).mp ⟨policy, safe⟩
  · rintro ⟨readout, surjective, compatible⟩
    obtain ⟨policy, safe⟩ :=
      (deterministic_safe_policy_exists_iff readout legal).mpr compatible
    exact ⟨readout, surjective, policy, safe⟩

#print axioms supports_deterministic_safe_policy_iff_safe_compatible_partition

/-- A natural number is the minimum size of a deterministic safe observation
alphabet exactly when it is the minimum size of a safe-compatible partition.
The membership clause of `IsLeast` gives attainability, while its lower-bound
clause proves that every safe observer uses at least that many values. -/
theorem minimum_safe_observation_alphabet
    {X A : Type*} (legal : X -> Set A) (chiSafe : Nat) :
    IsLeast {alphabetSize | SafeCompatiblePartition legal alphabetSize} chiSafe ↔
      IsLeast {alphabetSize | SupportsDeterministicSafePolicy legal alphabetSize} chiSafe := by
  constructor
  · rintro ⟨compatible, minimum⟩
    refine ⟨?_, ?_⟩
    · exact
        (supports_deterministic_safe_policy_iff_safe_compatible_partition
          legal chiSafe).mpr compatible
    · intro alphabetSize supportsSafePolicy
      apply minimum
      exact
        (supports_deterministic_safe_policy_iff_safe_compatible_partition
          legal alphabetSize).mp supportsSafePolicy
  · rintro ⟨safePolicy, minimum⟩
    refine ⟨?_, ?_⟩
    · exact
        (supports_deterministic_safe_policy_iff_safe_compatible_partition
          legal chiSafe).mp safePolicy
    · intro alphabetSize compatible
      apply minimum
      exact
        (supports_deterministic_safe_policy_iff_safe_compatible_partition
          legal alphabetSize).mpr compatible

#print axioms minimum_safe_observation_alphabet

end D5.S3.ConceptDynamics.Agency.MinimumSafeObservationAlphabet
