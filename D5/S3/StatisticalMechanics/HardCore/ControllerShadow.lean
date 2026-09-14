/- GID: D5/S3/StatisticalMechanics/HardCore/ControllerShadow
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/ControllerShadow
   mirror-E: none(waiver:history-controller-construction)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/StatisticalMechanics/HardCore/ControllerShadow.CoarseShadowIsCurrentProjection; result=D5/S3/StatisticalMechanics/HardCore/ControllerShadow.coarse_shadow_refutes_current_projection; claim=D5/S3/StatisticalMechanics/HardCore/ControllerShadow.CoarseShadowIsCurrentProjection
   digest: Replay coarse state policies as history controllers and certify a projection failure. -/

import D5.S3.StatisticalMechanics.HardCore.MemoryRefinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.ControllerShadow

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.BranchingPotential
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.MemoryRefinement

/-- Replay a coarse controller along an arbitrary newest-first history.
The trace is total even on illegal histories; only legal branches are counted. -/
def controllerTrace (r : ℕ) (choose : Finset Point → Fin 6) (F₀ : Finset Point) :
    List (Fin 3) → Finset Point
  | [] => F₀
  | d :: h =>
      memoryStep r (controllerTrace r choose F₀ h)
        (choose (controllerTrace r choose F₀ h)) d

/-- The lifted controller retains a coarse shadow instead of trying to recover
forgotten information by projecting the larger current mask. -/
def liftedPolicy (r : ℕ) (choose : Finset Point → Fin 6) (F₀ : Finset Point)
    (h : List (Fin 3)) (_G : Finset Point) : Fin 6 :=
  choose (controllerTrace r choose F₀ h)

private theorem shadow_count_eq (r : ℕ) (choose : Finset Point → Fin 6)
    (F₀ : Finset Point) (n : ℕ) (h : List (Fin 3)) :
    pathCount (geometricStep r) (liftedPolicy r choose F₀) n h
        (controllerTrace r choose F₀ h) =
      pathCount (geometricStep r) (fun _ F => choose F) n h
        (controllerTrace r choose F₀ h) := by
  induction n generalizing h with
  | zero => simp [pathCount]
  | succ n ih =>
      simp only [pathCount]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : direction d ∈ controllerTrace r choose F₀ h
      · simp [geometricStep, liftedPolicy, hd]
      · simp only [geometricStep, liftedPolicy, if_neg hd, Option.elim_some]
        simpa only [controllerTrace, liftedPolicy] using ih (d :: h)

/-- Constructed policy transport. Every coarse state-dependent policy has a
history-dependent refinement whose larger-memory tree has no more paths.
No supplied equality between the two independently chosen policies is needed. -/
theorem lifted_controller_refines (choose : Finset Point → Fin 6)
    {r R : ℕ} (hr : r ≤ R) (F₀ G₀ : Finset Point) (hFG : F₀ ⊆ G₀) (n : ℕ) :
    pathCount (geometricStep R) (liftedPolicy r choose F₀) n [] G₀ ≤
      pathCount (geometricStep r) (fun _ F => choose F) n [] F₀ := by
  calc
    _ ≤ pathCount (geometricStep r) (liftedPolicy r choose F₀) n [] F₀ :=
      history_count_antitone r R hr
        (fun h => choose (controllerTrace r choose F₀ h)) n [] F₀ G₀ hFG
    _ = _ := by simpa only [controllerTrace] using shadow_count_eq r choose F₀ n []

/-- A valid four-step SRL history disproves recovery of the coarse shadow by
projecting the current radius-four mask. At (2,-1), radius four remembers a
blocker that radius three has already forgotten. -/
theorem coarse_shadow_is_not_current_projection :
    (∀ q ∈ ([(0, []), (0, [0]), (1, [0, 0]), (1, [1, 0, 0])] :
        List (Fin 3 × List (Fin 3))),
      direction q.1 ∉ controllerTrace 3 (fun _ => 0) {(-1, 0)} q.2 ∧
      direction q.1 ∉ controllerTrace 4 (fun _ => 0) {(-1, 0)} q.2) ∧
    (2, -1) ∉ controllerTrace 3 (fun _ => 0) {(-1, 0)} [1, 1, 0, 0] ∧
    (2, -1) ∈ (controllerTrace 4 (fun _ => 0) {(-1, 0)} [1, 1, 0, 0]).filter
      (fun p => p.1.natAbs + p.2.natAbs ≤ 3) := by
  decide +kernel

/-- The coarse trace is always the radius-three Manhattan-ball projection of
the fine trace, for the same controller, initial set and history. -/
def CoarseShadowIsCurrentProjection : Prop :=
  ∀ (choose : Finset Point → Fin 6) (F₀ : Finset Point) (h : List (Fin 3)),
    controllerTrace 3 choose F₀ h =
      (controllerTrace 4 choose F₀ h).filter (fun p => p.1.natAbs + p.2.natAbs ≤ 3)

/-- The legal four-step witness refutes recovery by current-mask projection. -/
theorem coarse_shadow_refutes_current_projection :
    ¬ CoarseShadowIsCurrentProjection := by
  intro h
  have he := h (fun _ => 0) {(-1, 0)} [1, 1, 0, 0]
  have hw := coarse_shadow_is_not_current_projection
  exact hw.2.1 (he.symm ▸ hw.2.2)

#print axioms CoarseShadowIsCurrentProjection
#print axioms coarse_shadow_refutes_current_projection
#print axioms lifted_controller_refines
#print axioms coarse_shadow_is_not_current_projection

end D5.S3.StatisticalMechanics.HardCore.ControllerShadow
