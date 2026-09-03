/- GID: D5/S0/Certificates/LRATDFAStateLowerBound
   generality: G
   mirror-B: D5/B/S0/Certificates/LRATDFAStateLowerBound
   mirror-E: none(waiver:kernel-checked-state-lower-bound)
   anchors: [mathlib/module/Mathlib.Tactic.Sat.FromLRAT]
   digest: A kernel-checked LRAT refutation of any complete finite-prefix encoding rules out every globally correct DFAO within the same state budget. -/

import D5.S0.Certificates.DFAIdentificationCNF
import D5.S0.Certificates.LRATUnsatisfiable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.LRATDFAStateLowerBound

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Certificates.DFAIdentificationCNF
open D5.S0.Certificates.LRATUnsatisfiable

universe u v w

/-- A refutation-oriented CNF target for all models of one finite sparse prefix
within a fixed state budget. Positive decoding is deliberately absent. -/
abbrev PrefixModelEncoding
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : SparseProblem Alphabet Output BaseState)
    (extent bound : Nat) :=
  RefutationEncoding (problem.HasPrefixModelAtMost extent bound)

/-- The stronger exact interface remains available when satisfiable formulas
must reconstruct positive finite-prefix witnesses. -/
abbrev ExactPrefixModelEncoding
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : SparseProblem Alphabet Output BaseState)
    (extent bound : Nat) :=
  CertifiedEncoding (problem.HasPrefixModelAtMost extent bound)

/-- A kernel-checked LRAT refutation of a complete encoding excludes the
encoded mathematical problem. -/
theorem false_of_refutation
    {Problem : Prop}
    (encoding : RefutationEncoding Problem)
    (refutation : Refutation encoding.formula) :
    ¬Problem := by
  intro witness
  obtain ⟨valuation, satisfies⟩ := encoding.complete witness
  exact (refutation.sound valuation) satisfies

/-- Generic finite-witness bridge. Any global problem that maps to the encoded
finite problem is excluded by a refutation of the finite formula. -/
theorem no_global_of_finite_refutation
    {GlobalProblem FiniteProblem : Prop}
    (toFinite : GlobalProblem → FiniteProblem)
    (encoding : RefutationEncoding FiniteProblem)
    (refutation : Refutation encoding.formula) :
    ¬GlobalProblem := by
  intro globalWitness
  exact false_of_refutation encoding refutation (toFinite globalWitness)

/-- This is the finite-to-infinite bridge used by the sparse DFAO program.
Unsatisfiability on one genuine finite prefix rules out every globally correct
machine in the same state budget. -/
theorem no_global_model_at_most_of_prefix_refutation
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : SparseProblem Alphabet Output BaseState)
    (extent bound : Nat)
    (encoding : PrefixModelEncoding problem extent bound)
    (refutation : Refutation encoding.formula) :
    ¬problem.HasGlobalModelAtMost bound :=
  no_global_of_finite_refutation
    problem.global_model_at_most_implies_prefix_model_at_most
    encoding refutation

/-- A state count is minimal when a globally correct machine with that many
states exists and every globally correct machine uses at least that many. -/
def IsMinimalStateCount
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : SparseProblem Alphabet Output BaseState)
    (states : Nat) : Prop :=
  problem.HasGlobalModel states ∧
    ∀ candidateStates,
      problem.HasGlobalModel candidateStates →
        states ≤ candidateStates

/-- An upper witness at `states` together with a finite-prefix LRAT refutation
for all machines using at most `states - 1` proves exact minimality. -/
theorem minimal_state_count_of_prefix_refutation
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : SparseProblem Alphabet Output BaseState)
    (states extent : Nat)
    (upper : problem.HasGlobalModel states)
    (encoding :
      PrefixModelEncoding problem extent (states - 1))
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

#print axioms false_of_refutation
#print axioms no_global_of_finite_refutation
#print axioms no_global_model_at_most_of_prefix_refutation
#print axioms minimal_state_count_of_prefix_refutation

end D5.S0.Certificates.LRATDFAStateLowerBound
