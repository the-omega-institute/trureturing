/- GID: D5/S3/ObserverMemory/FiniteCountermodels/PathBranchNoncommutation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FiniteCountermodels/PathBranchNoncommutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Ordinary backward paths retain the periodic core but discard transient branches. -/

import D5.S3.ObserverMemory.InverseLimits.IdentityFuturePastGap
import Mathlib.Tactic.FinCases

/- Library-search audit trail (2026-08-23):
   * Exact repository hits `pastCoreEquiv` and `backward_orbit_eval_zero_bijective`
     canonically identify backward paths with the positive-periodic core and are
     imported and applied below.
   * Repository searches for branch completion, transient incoming trees, and
     predecessor-tree codes found no implementation of the source child relation.
     The relation below is therefore constructed directly as a nonperiodic child
     whose source update lands at the specified parent.
   * Pinned Mathlib found `Function.mem_periodicPts`, `Function.mk_mem_periodicPts`,
     and `Function.IsFixedPt.isPeriodicPt`, but no constant-map periodic-core theorem.
     Repository and Mathlib searches found no theorem packaging the canonical path
     equivalence together with a branch-sensitive countermodel. -/

namespace D5.S3.ObserverMemory.FiniteCountermodels.PathBranchNoncommutation

open D5.S3.ObserverMemory.InverseLimits.BackwardOrbitCore
open D5.S3.ObserverMemory.InverseLimits.IdentityFuturePastGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The source child relation: all nonperiodic predecessors of a parent. -/
def TransientChild {Y : Type*} (tau : Y -> Y) (parent : Y) :=
  {child : Y // child ∉ Function.periodicPts tau ∧ tau child = parent}

/-- Transport backward paths canonically through their coordinate-zero periodic cores. -/
noncomputable def backwardOrbitEquivOfPeriodicCoreEquiv
    {Y Z : Type*} [Finite Y] [Finite Z]
    (tau : Y -> Y) (sigma : Z -> Z)
    (coreEquiv : PeriodicCore tau ≃ PeriodicCore sigma) :
    BackwardOrbit tau ≃ BackwardOrbit sigma :=
  (pastCoreEquiv tau).trans (coreEquiv.trans (pastCoreEquiv sigma).symm)

/-- A two-state constant map with one transient child at its periodic root. -/
def oneBranchMap : Fin 2 -> Fin 2 := fun _ => 0

/-- A three-state constant map with two transient children at its periodic root. -/
def twoBranchMap : Fin 3 -> Fin 3 := fun _ => 0

private theorem constant_zero_periodic_iff {n : Nat} (x : Fin (n + 1)) :
    x ∈ Function.periodicPts (fun _ : Fin (n + 1) => 0) ↔ x = 0 := by
  constructor
  · rw [Function.mem_periodicPts]
    rintro ⟨k, hk, hperiod⟩
    have hiterate : ((fun _ : Fin (n + 1) => 0)^[k]) x = 0 := by
      cases k with
      | zero => omega
      | succ k => simp [Function.iterate_succ_apply']
    exact hperiod.symm.trans hiterate
  · rintro rfl
    exact Function.mk_mem_periodicPts (n := 1) (by norm_num) (by
      change ((fun _ : Fin (n + 1) => 0)^[1]) 0 = 0
      simp)

/-- The unique periodic roots of the two countermodel maps correspond directly. -/
def countermodelCoreEquiv : PeriodicCore oneBranchMap ≃ PeriodicCore twoBranchMap where
  toFun _ := ⟨0, (constant_zero_periodic_iff (0 : Fin 3)).2 rfl⟩
  invFun _ := ⟨0, (constant_zero_periodic_iff (0 : Fin 2)).2 rfl⟩
  left_inv point :=
    Subtype.ext ((constant_zero_periodic_iff point.1).1 point.2).symm
  right_inv point :=
    Subtype.ext ((constant_zero_periodic_iff point.1).1 point.2).symm

private def oneTransientChildEquiv : TransientChild oneBranchMap 0 ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨1, by
    constructor
    · change 1 ∉ Function.periodicPts (fun _ : Fin 2 => 0)
      exact (constant_zero_periodic_iff (1 : Fin 2)).not.mpr (by decide)
    · rfl⟩
  left_inv child := by
    apply Subtype.ext
    have hne : child.1 ≠ 0 := by
      intro hzero
      apply child.2.1
      rw [hzero]
      exact (constant_zero_periodic_iff (0 : Fin 2)).2 rfl
    have hone : child.1 = (1 : Fin 2) := by
      apply Fin.ext
      omega
    exact hone.symm
  right_inv child := by
    fin_cases child
    rfl

private def twoTransientChildEquiv : TransientChild twoBranchMap 0 ≃ Fin 2 where
  toFun child := if child.1 = 1 then 0 else 1
  invFun index := if index = 0 then
      ⟨1, by
        constructor
        · change 1 ∉ Function.periodicPts (fun _ : Fin 3 => 0)
          exact (constant_zero_periodic_iff (1 : Fin 3)).not.mpr (by decide)
        · rfl⟩
    else
      ⟨2, by
        constructor
        · change 2 ∉ Function.periodicPts (fun _ : Fin 3 => 0)
          exact (constant_zero_periodic_iff (2 : Fin 3)).not.mpr (by decide)
        · rfl⟩
  left_inv child := by
    apply Subtype.ext
    have hne : child.1 ≠ 0 := by
      intro hzero
      apply child.2.1
      rw [hzero]
      exact (constant_zero_periodic_iff (0 : Fin 3)).2 rfl
    by_cases hone : child.1 = (1 : Fin 3)
    · simp [hone]
    · have htwo : child.1 = (2 : Fin 3) := by
        apply Fin.ext
        omega
      simp [htwo]
  right_inv index := by
    fin_cases index <;> rfl

/-- The path limit is canonically determined by the periodic core, while two
constant maps with the same one-point periodic permutation have different
complete height-one transient incoming trees and are not conjugate. -/
theorem path_limit_branch_noncommutation :
    (∀ {Y Z : Type*} [Finite Y] [Finite Z]
      (tau : Y -> Y) (sigma : Z -> Z)
      (coreEquiv : PeriodicCore tau ≃ PeriodicCore sigma)
      (orbit : BackwardOrbit tau),
      (backwardOrbitEquivOfPeriodicCoreEquiv tau sigma coreEquiv orbit).1 0 =
        (coreEquiv (pastCoreEquiv tau orbit)).1) ∧
    (∃ child : Fin 2, child ∉ Function.periodicPts oneBranchMap) ∧
    (∃ child : Fin 3, child ∉ Function.periodicPts twoBranchMap) ∧
    (∀ point : PeriodicCore oneBranchMap,
      countermodelCoreEquiv
          ⟨oneBranchMap point.1,
            (Function.bijOn_periodicPts oneBranchMap).mapsTo point.2⟩ =
        ⟨twoBranchMap (countermodelCoreEquiv point).1,
          (Function.bijOn_periodicPts twoBranchMap).mapsTo
            (countermodelCoreEquiv point).2⟩) ∧
    (∀ orbit : BackwardOrbit oneBranchMap,
      (backwardOrbitEquivOfPeriodicCoreEquiv oneBranchMap twoBranchMap
          countermodelCoreEquiv orbit).1 0 =
        (countermodelCoreEquiv (pastCoreEquiv oneBranchMap orbit)).1) ∧
    (∀ child : Fin 2, child ∉ Function.periodicPts oneBranchMap ->
      IsEmpty (TransientChild oneBranchMap child)) ∧
    (∀ child : Fin 3, child ∉ Function.periodicPts twoBranchMap ->
      IsEmpty (TransientChild twoBranchMap child)) ∧
    Nat.card (TransientChild oneBranchMap 0) = 1 ∧
    Nat.card (TransientChild twoBranchMap 0) = 2 ∧
    Nat.card (TransientChild oneBranchMap 0) ≠
      Nat.card (TransientChild twoBranchMap 0) ∧
    ¬ (∃ relabel : Fin 2 ≃ Fin 3,
      Function.Semiconj relabel oneBranchMap twoBranchMap) := by
  refine ⟨?_,
    ⟨1, by
      change 1 ∉ Function.periodicPts (fun _ : Fin 2 => 0)
      exact (constant_zero_periodic_iff (1 : Fin 2)).not.mpr (by decide)⟩,
    ⟨1, by
      change 1 ∉ Function.periodicPts (fun _ : Fin 3 => 0)
      exact (constant_zero_periodic_iff (1 : Fin 3)).not.mpr (by decide)⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y Z _ _ tau sigma coreEquiv orbit
    have happly := (pastCoreEquiv sigma).apply_symm_apply
      (coreEquiv (pastCoreEquiv tau orbit))
    exact congrArg Subtype.val happly
  · intro point
    apply Subtype.ext
    rfl
  · intro orbit
    have happly := (pastCoreEquiv twoBranchMap).apply_symm_apply
      (countermodelCoreEquiv (pastCoreEquiv oneBranchMap orbit))
    exact congrArg Subtype.val happly
  · intro child htransient
    constructor
    rintro ⟨predecessor, _, hmaps⟩
    have hchild : child = 0 := by simpa [oneBranchMap] using hmaps.symm
    exact htransient (hchild ▸ (constant_zero_periodic_iff (0 : Fin 2)).2 rfl)
  · intro child htransient
    constructor
    rintro ⟨predecessor, _, hmaps⟩
    have hchild : child = 0 := by simpa [twoBranchMap] using hmaps.symm
    exact htransient (hchild ▸ (constant_zero_periodic_iff (0 : Fin 3)).2 rfl)
  · simpa using Nat.card_congr oneTransientChildEquiv
  · simpa using Nat.card_congr twoTransientChildEquiv
  · intro hequal
    have himpossible : Nat.card (Fin 1) = Nat.card (Fin 2) :=
      (Nat.card_congr oneTransientChildEquiv).symm.trans
        (hequal.trans (Nat.card_congr twoTransientChildEquiv))
    norm_num at himpossible
  · rintro ⟨relabel, _⟩
    have hcard := Nat.card_congr relabel
    norm_num at hcard

#print axioms path_limit_branch_noncommutation

end D5.S3.ObserverMemory.FiniteCountermodels.PathBranchNoncommutation
