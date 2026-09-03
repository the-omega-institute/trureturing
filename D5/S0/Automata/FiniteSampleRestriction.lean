/- GID: D5/S0/Automata/FiniteSampleRestriction
   generality: G
   mirror-B: D5/B/S0/Automata/FiniteSampleRestriction
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Unsatisfiability on any exact finite subsample implies nonexistence of a globally correct DFAO on the same state carrier. -/

import D5.S0.Automata.DFAOStateLowerBound

/- Library-search audit trail (2026-09-01):
   * The frozen DFAO node defines sparse-domain correctness, but the open-problem
     registry had not isolated the logical direction from finite sample UNSAT
     to an infinite sparse-language lower bound.
   * This node adds only the restriction lemma. It makes no compactness claim:
     finite SAT remains finite evidence, while finite UNSAT is already enough
     to exclude a global model on the same state carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.FiniteSampleRestriction

open D5.S0.Automata.DFAOStateLowerBound

universe u v w z

/-- Correctness of a DFAO on an indexed infinite or finite word family. -/
def CorrectOnFamily {Alphabet : Type u} {Output : Type v}
    {State : Type w} {Index : Type z}
    (machine : DFAO Alphabet Output State)
    (word : Index → List Alphabet) (target : Index → Output) : Prop :=
  ∀ index, machine.evalOutput (word index) = target index

/-- Correctness on a selected subsample of an indexed family. -/
def FitsSubsample {Alphabet : Type u} {Output : Type v}
    {State : Type w} {Index SampleIndex : Type z}
    (machine : DFAO Alphabet Output State)
    (word : Index → List Alphabet) (target : Index → Output)
    (select : SampleIndex → Index) : Prop :=
  ∀ sampleIndex,
    machine.evalOutput (word (select sampleIndex)) = target (select sampleIndex)

/-- Global correctness restricts to every selected sample. -/
theorem fitsSubsample_of_correctOnFamily
    {Alphabet : Type u} {Output : Type v}
    {State : Type w} {Index SampleIndex : Type z}
    (machine : DFAO Alphabet Output State)
    (word : Index → List Alphabet) (target : Index → Output)
    (select : SampleIndex → Index)
    (correct : CorrectOnFamily machine word target) :
    FitsSubsample machine word target select := by
  intro sampleIndex
  exact correct (select sampleIndex)

/-- If no DFAO on a fixed state carrier fits one selected finite sample, then
no DFAO on that carrier can be correct on the whole indexed family. -/
theorem no_global_model_of_no_subsample_model
    {Alphabet : Type u} {Output : Type v}
    {State : Type w} {Index SampleIndex : Type z}
    (word : Index → List Alphabet) (target : Index → Output)
    (select : SampleIndex → Index)
    (excluded : ¬ ∃ machine : DFAO Alphabet Output State,
      FitsSubsample machine word target select) :
    ¬ ∃ machine : DFAO Alphabet Output State,
      CorrectOnFamily machine word target := by
  rintro ⟨machine, correct⟩
  apply excluded
  exact ⟨machine,
    fitsSubsample_of_correctOnFamily machine word target select correct⟩

/-- The same implication specialized to a `k`-state carrier. This is the exact
logical bridge consumed by SAT or LRAT exclusion of `Fin k` models. -/
theorem no_global_fin_model_of_no_subsample_fin_model
    {Alphabet : Type u} {Output : Type v}
    {Index SampleIndex : Type z} (k : Nat)
    (word : Index → List Alphabet) (target : Index → Output)
    (select : SampleIndex → Index)
    (excluded : ¬ ∃ machine : DFAO Alphabet Output (Fin k),
      FitsSubsample machine word target select) :
    ¬ ∃ machine : DFAO Alphabet Output (Fin k),
      CorrectOnFamily machine word target :=
  no_global_model_of_no_subsample_model word target select excluded

#print axioms fitsSubsample_of_correctOnFamily
#print axioms no_global_model_of_no_subsample_model
#print axioms no_global_fin_model_of_no_subsample_fin_model

end D5.S0.Automata.FiniteSampleRestriction
