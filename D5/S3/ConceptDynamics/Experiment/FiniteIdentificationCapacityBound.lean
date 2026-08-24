/- GID: D5/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The capacity of a finite experiment family is the cardinality of its dependent joint-readout space; injective joint readout bounds the state count, and this cardinal bound is equivalent to its base-two logarithmic cost form when capacity is positive. -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.SetTheory.Cardinal.NatCard

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'finite_identification_capacity_bound' D5 Golden/Frozen/accepted`
     found no public or private declaration with the requested theorem name.
   * `rg -n 'Injective.*card|capacity|Cost' D5/S3/ D5/S0/ | head -20`
     found no identification-capacity theorem; the reported hits concern unrelated
     program-description costs.
   * Pinned Mathlib contains the exact pigeonhole lemma
     `Nat.card_le_card_of_injective` in `Mathlib.SetTheory.Cardinal.NatCard` and the
     exact positive-argument equivalence `Real.logb_le_logb` in
     `Mathlib.Analysis.SpecialFunctions.Log.Base`; both are reused below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.FiniteIdentificationCapacityBound

universe u v w

/-- The number of possible joint readouts of a finite dependent experiment family. -/
noncomputable def Cap
    {J : Type u} [Fintype J] (O : J -> Type v) [forall j, Fintype (O j)] : Nat :=
  Nat.card ((j : J) -> O j)

/-- Identification cost is the base-two logarithm of joint-readout capacity. -/
noncomputable def Cost
    {J : Type u} [Fintype J] (O : J -> Type v) [forall j, Fintype (O j)] : Real :=
  Real.logb 2 (Cap O)

/-- An injective joint readout embeds the finite state space in the readout space. -/
theorem finite_identification_capacity_bound
    {X : Type w} {J : Type u} [Finite X] [Fintype J]
    (O : J -> Type v) [forall j, Fintype (O j)]
    (q_J : X -> ((j : J) -> O j)) (hq_J : Function.Injective q_J) :
    Nat.card X <= Cap O := by
  unfold Cap
  exact Nat.card_le_card_of_injective q_J hq_J

/-- The cardinal capacity bound implies the corresponding base-two cost bound. -/
theorem cost_form
    {X : Type w} {J : Type u} [Finite X] [Fintype J]
    (O : J -> Type v) [forall j, Fintype (O j)]
    (q_J : X -> ((j : J) -> O j)) (hCap : 0 < Cap O)
    (hq_J : Function.Injective q_J) :
    Real.logb 2 (Nat.card X) <= Cost O := by
  rw [Cost]
  have hBound := finite_identification_capacity_bound O q_J hq_J
  by_cases hX : Nat.card X = 0
  · rw [hX]
    norm_num only [Nat.cast_zero, Real.logb_zero]
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hCap)
  · exact Real.logb_le_logb_of_le (by norm_num)
      (by exact_mod_cast Nat.pos_of_ne_zero hX) (by exact_mod_cast hBound)

/-- At positive capacity, the cardinal and base-two logarithmic bounds are equivalent. -/
theorem cardinal_bound_iff_cost_bound
    {X : Type w} {J : Type u} [Finite X] [Fintype J]
    (O : J -> Type v) [forall j, Fintype (O j)] (hCap : 0 < Cap O) :
    Nat.card X <= Cap O <-> Real.logb 2 (Nat.card X) <= Cost O := by
  rw [Cost]
  constructor
  · intro hBound
    by_cases hX : Nat.card X = 0
    · rw [hX]
      norm_num only [Nat.cast_zero, Real.logb_zero]
      exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hCap)
    · exact Real.logb_le_logb_of_le (by norm_num)
        (by exact_mod_cast Nat.pos_of_ne_zero hX) (by exact_mod_cast hBound)
  · intro hCost
    by_cases hX : Nat.card X = 0
    · simp [hX]
    · have hXReal : (0 : Real) < Nat.card X := by
        exact_mod_cast Nat.pos_of_ne_zero hX
      have hCapReal : (0 : Real) < Cap O := by
        exact_mod_cast hCap
      have hReal : (Nat.card X : Real) <= Cap O :=
        (Real.logb_le_logb (by norm_num) hXReal hCapReal).mp hCost
      exact_mod_cast hReal

example : Nat.card Bool <= Cap (fun _ : Fin 2 => Bool) := by
  let q : Bool -> ((j : Fin 2) -> Bool) := fun b _ => b
  apply finite_identification_capacity_bound (fun _ : Fin 2 => Bool) q
  intro x y hxy
  exact congrFun hxy 0

#print axioms finite_identification_capacity_bound

end D5.S3.ConceptDynamics.Experiment.FiniteIdentificationCapacityBound
