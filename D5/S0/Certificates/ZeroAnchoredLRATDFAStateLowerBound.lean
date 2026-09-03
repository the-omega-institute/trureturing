/- GID: D5/S0/Certificates/ZeroAnchoredLRATDFAStateLowerBound
   generality: G
   mirror-B: D5/B/S0/Certificates/ZeroAnchoredLRATDFAStateLowerBound
   mirror-E: none(waiver:zero-anchored-kernel-lower-bound)
   anchors: [mathlib/module/Mathlib.Tactic.Sat.FromLRAT]
   digest: Refuting a complete finite-prefix encoding for a zero-anchored sparse problem yields a global state lower bound in the exact leading-zero model class. -/

import D5.S0.Automata.ZeroAnchoredSparseDFAO
import D5.S0.Certificates.LRATDFAStateLowerBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.ZeroAnchoredLRATDFAStateLowerBound

open D5.S0.Automata.ZeroAnchoredSparseDFAO
open D5.S0.Certificates.DFAIdentificationCNF
open D5.S0.Certificates.LRATUnsatisfiable
open D5.S0.Certificates.LRATDFAStateLowerBound

universe u v w

/-- A complete CNF target for all zero-anchored models of one finite prefix
within a fixed state budget. -/
abbrev PrefixModelEncoding
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    (extent bound : Nat) :=
  RefutationEncoding (problem.HasPrefixModelAtMost extent bound)

/-- A finite-prefix refutation excludes every globally correct zero-anchored
machine in the same state budget. -/
theorem no_global_model_at_most_of_prefix_refutation
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    (extent bound : Nat)
    (encoding : PrefixModelEncoding problem extent bound)
    (refutation : Refutation encoding.formula) :
    ¬problem.HasGlobalModelAtMost bound :=
  no_global_of_finite_refutation
    problem.global_model_at_most_implies_prefix_model_at_most
    encoding refutation

/-- Exact minimality inside the zero-anchored model class. -/
def IsMinimalStateCount
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    (states : Nat) : Prop :=
  problem.HasGlobalModel states ∧
    ∀ candidateStates,
      problem.HasGlobalModel candidateStates →
        states ≤ candidateStates

/-- A verified upper machine and an LRAT exclusion of all smaller budgets prove
exact minimality in the zero-anchored class. -/
theorem minimal_state_count_of_prefix_refutation
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    (states extent : Nat)
    (upper : problem.HasGlobalModel states)
    (encoding : PrefixModelEncoding problem extent (states - 1))
    (refutation : Refutation encoding.formula) :
    IsMinimalStateCount problem states := by
  constructor
  · exact upper
  · intro candidateStates candidate
    by_contra smaller
    have hlt : candidateStates < states := Nat.lt_of_not_ge smaller
    have hbudget : candidateStates ≤ states - 1 := by omega
    have bounded : problem.HasGlobalModelAtMost (states - 1) :=
      ⟨candidateStates, hbudget, candidate⟩
    exact
      (no_global_model_at_most_of_prefix_refutation
        problem extent (states - 1) encoding refutation) bounded

#print axioms no_global_model_at_most_of_prefix_refutation
#print axioms minimal_state_count_of_prefix_refutation

end D5.S0.Certificates.ZeroAnchoredLRATDFAStateLowerBound
