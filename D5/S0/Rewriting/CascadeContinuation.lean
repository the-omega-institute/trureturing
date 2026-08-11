/- GID: D5/S0/Rewriting/CascadeContinuation
   generality: G
   mirror-B: D5/B/S0/Rewriting/CascadeContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A relation extendable at every state admits a path through every finite stage. -/

import Mathlib.Logic.Function.Iterate

namespace D5.S0.Rewriting.CascadeContinuation

/-- If every state has a related successor, then every starting state lies at
the beginning of one coherent infinite sequence of related states. This is the
choice-and-iteration mechanism underlying the continuation claim in the source
atom. -/
theorem cascade_continues_to_all_stages
    {State : Type*} (step : State → State → Prop)
    (redeem : ∀ state, ∃ next, step state next) (start : State) :
    ∃ path : ℕ → State,
      path 0 = start ∧ ∀ n, step (path n) (path (n + 1)) := by
  let next : State → State := fun state => Classical.choose (redeem state)
  have next_step (state : State) : step state (next state) :=
    Classical.choose_spec (redeem state)
  refine ⟨fun n => (next^[n]) start, ?_, ?_⟩
  · rfl
  · intro n
    simpa [Function.iterate_succ_apply'] using next_step ((next^[n]) start)

end D5.S0.Rewriting.CascadeContinuation
