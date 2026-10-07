/- GID: D5/S1/Phase/LonelyRunnerDeletion/OneDeletionDefs
   generality: G
   mirror-B: D5/B/S1/Phase/LonelyRunnerDeletion/OneDeletionDefs
   mirror-E: none(waiver:zhang-question-two-eleven-statement-definition)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Round, mathlib/module/Mathlib.Algebra.Order.Archimedean.Real.Basic, mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Zhang's Question 2.11 on the Lonely Runner value of the speed sets [N] minus one speed. -/

import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Phase.LonelyRunnerDeletion.OneDeletionDefs

/-! Fixed public statement: Yuhan Zhang, *Tight instances of the Lonely Runner Conjecture: complete
    classification of one-entry modifications, a new infinite family, and the growth bound*,
    arXiv:2608.13599v2, "Question 2.11. Is LR([n − 1] \ {r}) ≥ 1/(n−1) for all n and all
    r ∈ [n − 1]? … A stronger form: is LR([n − 1] \ {r}) = 1/(n−1) only for r = n − 1?" Here
    [m] = {1, …, m}, ‖x‖ is the distance from x to the nearest integer and
    LR(V) = max_t min_{v ∈ V} ‖v t‖. Writing N = n − 1, the speed set is nonempty exactly when
    N ≥ 2; the maximum over t is attained, so it equals the supremum used below. The distance
    to the nearest integer is taken over all real times t (the rational `torusDist` of
    `LonelyRunnerFourteenOfTwenty` covers rational times only). -/

/-- The Lonely Runner value `LR(V) = sup_t min_{v ∈ V} ‖v t‖` of a finite set of speeds. -/
noncomputable def lonelyValue (V : Finset ℕ) : ℝ :=
  ⨆ t : ℝ, ⨅ v : V, |(v : ℝ) * t - round ((v : ℝ) * t)|

/-- Question 2.11, both forms, with `N = n − 1`. -/
def claim : Prop :=
  ∀ N r : ℕ, 2 ≤ N → 1 ≤ r → r ≤ N →
    1 / (N : ℝ) ≤ lonelyValue ((Finset.Icc 1 N).erase r) ∧
      (lonelyValue ((Finset.Icc 1 N).erase r) = 1 / (N : ℝ) ↔ r = N ∨ N = 2)

end D5.S1.Phase.LonelyRunnerDeletion.OneDeletionDefs
