/- GID: D5/S1/Digit/PublishedGoldenDFAStateLowerBound
   generality: I
   mirror-B: D5/B/S1/Digit/PublishedGoldenDFAStateLowerBound
   mirror-E: none(waiver:published-finite-to-infinite-bridge)
   anchors: [mathlib/module/Mathlib.Tactic.Sat.FromLRAT]
   digest: A one-way CNF encoding and kernel-checked refutation of one finite published prefix exclude every globally correct zero-invariant typed golden base-four DFAO in the same state budget. -/

import D5.S0.Certificates.RefutationEncoding
import D5.S1.Digit.PublishedGoldenBase4Problem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.PublishedGoldenDFAStateLowerBound

open D5.S0.Certificates.RefutationEncoding
open D5.S0.Certificates.LRATUnsatisfiable
open D5.S1.Digit.PublishedGoldenBase4Problem

noncomputable section

/-- A one-way CNF target containing every published finite-prefix model within
one state budget. Spurious satisfying assignments are permitted. -/
abbrev PrefixModelRefutationEncoding (extent bound : Nat) :=
  RefutationEncoding (HasPrefixModelAtMost extent bound)

/-- A kernel-checked refutation of a finite-prefix over-approximation excludes
all globally correct published machines in the same state budget. -/
theorem no_global_model_at_most_of_prefix_refutation
    (extent bound : Nat)
    (encoding : PrefixModelRefutationEncoding extent bound)
    (refutation : Refutation encoding.formula) :
    ¬HasGlobalModelAtMost bound := by
  intro globalModel
  apply RefutationEncoding.false_of_refutation encoding refutation
  exact global_model_at_most_implies_prefix_model_at_most globalModel

/-- Exact minimality inside the published machine class. -/
def IsMinimalPublishedStateCount (states : Nat) : Prop :=
  HasGlobalModel states ∧
    ∀ candidateStates,
      HasGlobalModel candidateStates → states ≤ candidateStates

/-- A verified `states`-state upper machine and a finite-prefix refutation for
all published machines with at most `states - 1` states prove exact minimality
in the published class. -/
theorem minimal_published_state_count_of_prefix_refutation
    (states extent : Nat)
    (upper : HasGlobalModel states)
    (encoding : PrefixModelRefutationEncoding extent (states - 1))
    (refutation : Refutation encoding.formula) :
    IsMinimalPublishedStateCount states := by
  constructor
  · exact upper
  · intro candidateStates candidate
    by_contra smaller
    have hlt : candidateStates < states := Nat.lt_of_not_ge smaller
    have hbudget : candidateStates ≤ states - 1 := by omega
    have bounded : HasGlobalModelAtMost (states - 1) :=
      ⟨candidateStates, hbudget, candidate⟩
    exact
      (no_global_model_at_most_of_prefix_refutation
        extent (states - 1) encoding refutation) bounded

/-- The corrected published M09 target. It is deliberately weaker than the
powers-only typed target because its formula may use the start-zero-loop and
zero-output-anchor conventions. -/
theorem published_base4_exclude_at_most_fourteen
    (extent : Nat)
    (encoding : PrefixModelRefutationEncoding extent 14)
    (refutation : Refutation encoding.formula) :
    ¬HasGlobalModelAtMost 14 :=
  no_global_model_at_most_of_prefix_refutation
    extent 14 encoding refutation

/-- The terminal published-class target. A verified 22-state upper machine and
a 21-state finite-prefix refutation prove exact published minimality. -/
theorem published_base4_twenty_two_state_minimality
    (upper : HasGlobalModel 22)
    (extent : Nat)
    (encoding : PrefixModelRefutationEncoding extent 21)
    (refutation : Refutation encoding.formula) :
    IsMinimalPublishedStateCount 22 :=
  minimal_published_state_count_of_prefix_refutation
    22 extent upper encoding refutation

#print axioms no_global_model_at_most_of_prefix_refutation
#print axioms published_base4_exclude_at_most_fourteen
#print axioms published_base4_twenty_two_state_minimality

end

end D5.S1.Digit.PublishedGoldenDFAStateLowerBound
