/- GID: D5/S0/Rewriting/Safety/SafePolicyInvariant
   generality: G
   mirror-B: D5/B/S0/Rewriting/Safety/SafePolicyInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Policies selecting controls whose responses remain in the safe kernel preserve safety. -/

import D5.S0.Rewriting.Safety.InvariantSafety

/- Library-search audit trail (2026-08-24):
   * Exact current-tree hit `InvariantSafety.invariant_safety` proves finite
     reachability stays inside a transition-closed invariant and is applied
     directly below.
   * Searches for `U_safe`, safe controls, safe policies, and controllable
     domains found no canonical policy/action/response primitive or complete
     theorem in the current tree or pinned Mathlib.
   * The safe-control set is therefore constructed publicly from the supplied
     available-control family, response relation, and safe kernel. `loogle` and
     `leansearch` were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Rewriting.Safety.SafePolicyInvariant

open D5.S0.Rewriting.Safety.InvariantSafety

/-- If every policy choice is available and every possible response stays in
the safe kernel, every finite policy execution remains in the kernel and safe set. -/
theorem safe_policy_preserves_kernel
    {X U : Type*} (available : X → Set U) (response : X → U → X → Prop)
    (kernel safe : Set X) (policy : X → U) (kernel_safe : kernel ⊆ safe) :
    let safeControls : X → Set U := fun state =>
      {control | control ∈ available state ∧
        ∀ next, response state control next → next ∈ kernel}
    (∀ state, policy state ∈ safeControls state) →
      ∀ {initial current}, initial ∈ kernel →
        Relation.ReflTransGen
          (fun state next => response state (policy state) next)
          initial current →
        current ∈ kernel ∧ current ∈ safe := by
  dsimp
  intro policy_safe initial current initial_mem path
  have current_kernel : current ∈ kernel := by
    exact invariant_safety
      (R := fun state next => response state (policy state) next)
      (initial := kernel) (invariant := kernel) (safe := kernel)
      (fun {_} membership => membership)
      (fun {_} membership => membership)
      (fun {state next} _ step => (policy_safe state).2 next step)
      initial_mem path
  exact ⟨current_kernel, kernel_safe current_kernel⟩

/- A one-state system witnesses simultaneous satisfiability of all hypotheses. -/
example :
    ∀ {initial current : Unit}, initial ∈ (Set.univ : Set Unit) →
      Relation.ReflTransGen
        (fun state next => (fun _ _ _ => True) state ((fun _ => ()) state) next)
        initial current →
      current ∈ (Set.univ : Set Unit) ∧ current ∈ (Set.univ : Set Unit) := by
  apply safe_policy_preserves_kernel
    (available := fun _ => Set.univ)
    (response := fun _ _ _ => True)
    (kernel := Set.univ) (safe := Set.univ) (policy := fun _ => ())
  · intro _ membership
    exact membership
  · intro state
    exact ⟨by trivial, fun _ _ => by trivial⟩

example : Unit := ()

#print axioms safe_policy_preserves_kernel

end D5.S0.Rewriting.Safety.SafePolicyInvariant
