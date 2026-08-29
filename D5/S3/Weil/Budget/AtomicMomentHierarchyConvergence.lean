/- GID: D5/S3/Weil/Budget/AtomicMomentHierarchyConvergence
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/AtomicMomentHierarchyConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nested finite-moment frontiers decrease to the determining-family completion frontier. -/

import D5.S3.Weil.Budget.ResolventFrontierGeometry
import Mathlib.Topology.Order.MonotoneConvergence

/- Library-search audit trail (2026-08-29):
   * D5 searches for measure-valued moment hierarchies, determining-family
     closure, and optimizer subsequences found no exact theorem or definition.
   * Pinned Mathlib exact hits `antitone_nat_of_succ_le`,
     `StrictMono.tendsto_atTop`, `tendsto_iff_tendsto_subseq_of_antitone`,
     `le_of_tendsto`, and conditional `sSup` bounds.
   * No packaged result identifies a nested finite-moment frontier with the
     full determining-family frontier on `Measure Real`.
   * Body-shape searches for both extremal value sets found no D5 primitive. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.AtomicMomentHierarchyConvergence

open Filter MeasureTheory Set Topology

/-- Nested finite-moment optimizer values decrease to the full completion
frontier when a weighted compactness subsequence closes every determining
constraint and preserves the optimizer white floor. -/
theorem atomic_moment_hierarchy_converges
    (C cap : Real)
    (levelMatch : Nat -> Measure Real -> Prop)
    (fullMatch : Measure Real -> Prop)
    (resolventBudget whiteFloor : Measure Real -> Real)
    (floorBound : forall nu, whiteFloor nu <= cap)
    (levelNested : forall N nu, levelMatch (N + 1) nu -> levelMatch N nu)
    (fullImpliesLevel : forall nu, fullMatch nu -> forall N, levelMatch N nu)
    (determiningFamily : forall nu,
      (forall N, levelMatch N nu) -> fullMatch nu)
    (optimizer : Nat -> Measure Real)
    (optimizerLevel : forall N, levelMatch N (optimizer N))
    (optimizerBudget : forall N, resolventBudget (optimizer N) <= C)
    (optimizerOptimal : forall N,
      whiteFloor (optimizer N) = sSup
        {r : Real | exists nu : Measure Real,
          levelMatch N nu /\ resolventBudget nu <= C /\ r = whiteFloor nu})
    (cluster : Measure Real)
    (clusterLevels : forall N, levelMatch N cluster)
    (clusterBudget : resolventBudget cluster <= C)
    (selection : Nat -> Nat) (selectionStrict : StrictMono selection)
    (selectedFloorLimit : Tendsto
      (fun k => whiteFloor (optimizer (selection k))) atTop
      (nhds (whiteFloor cluster))) :
    let levelValues := fun N : Nat =>
      {r : Real | exists nu : Measure Real,
        levelMatch N nu /\ resolventBudget nu <= C /\ r = whiteFloor nu}
    let fullValues :=
      {r : Real | exists nu : Measure Real,
        fullMatch nu /\ resolventBudget nu <= C /\ r = whiteFloor nu}
    let hierarchy := fun N : Nat => sSup (levelValues N)
    let fullFrontier := sSup fullValues
    Antitone hierarchy /\ Tendsto hierarchy atTop (nhds fullFrontier) := by
  let levelValues := fun N : Nat =>
    {r : Real | exists nu : Measure Real,
      levelMatch N nu /\ resolventBudget nu <= C /\ r = whiteFloor nu}
  let fullValues :=
    {r : Real | exists nu : Measure Real,
      fullMatch nu /\ resolventBudget nu <= C /\ r = whiteFloor nu}
  let hierarchy := fun N : Nat => sSup (levelValues N)
  let fullFrontier := sSup fullValues
  have levelBounded (N : Nat) : BddAbove (levelValues N) := by
    refine ⟨cap, ?_⟩
    rintro r ⟨nu, _, _, rfl⟩
    exact floorBound nu
  have fullBounded : BddAbove fullValues := by
    refine ⟨cap, ?_⟩
    rintro r ⟨nu, _, _, rfl⟩
    exact floorBound nu
  have levelNonempty (N : Nat) : (levelValues N).Nonempty :=
    ⟨whiteFloor (optimizer N), optimizer N, optimizerLevel N,
      optimizerBudget N, rfl⟩
  have clusterFull : fullMatch cluster := determiningFamily cluster clusterLevels
  have clusterMem : whiteFloor cluster ∈ fullValues :=
    ⟨cluster, clusterFull, clusterBudget, rfl⟩
  have fullNonempty : fullValues.Nonempty := ⟨whiteFloor cluster, clusterMem⟩
  have hierarchyStep (N : Nat) : hierarchy (N + 1) <= hierarchy N := by
    apply csSup_le (levelNonempty (N + 1))
    intro r hr
    apply le_csSup (levelBounded N)
    rcases hr with ⟨nu, hLevel, hBudget, rfl⟩
    exact ⟨nu, levelNested N nu hLevel, hBudget, rfl⟩
  have hierarchyAntitone : Antitone hierarchy :=
    antitone_nat_of_succ_le hierarchyStep
  have fullLeLevel (N : Nat) : fullFrontier <= hierarchy N := by
    apply csSup_le fullNonempty
    intro r hr
    apply le_csSup (levelBounded N)
    rcases hr with ⟨nu, hFull, hBudget, rfl⟩
    exact ⟨nu, fullImpliesLevel nu hFull N, hBudget, rfl⟩
  have selectedHierarchyLimit : Tendsto
      (fun k => hierarchy (selection k)) atTop (nhds (whiteFloor cluster)) := by
    simpa only [hierarchy, levelValues, optimizerOptimal] using selectedFloorLimit
  have fullLeCluster : fullFrontier <= whiteFloor cluster := by
    exact ge_of_tendsto' selectedHierarchyLimit
      (fun k => fullLeLevel (selection k))
  have clusterLeFull : whiteFloor cluster <= fullFrontier :=
    le_csSup fullBounded clusterMem
  have clusterFloorEq : whiteFloor cluster = fullFrontier :=
    le_antisymm clusterLeFull fullLeCluster
  have hierarchyLimit : Tendsto hierarchy atTop (nhds fullFrontier) := by
    apply (tendsto_iff_tendsto_subseq_of_antitone hierarchyAntitone
      selectionStrict.tendsto_atTop).2
    change Tendsto (fun k => hierarchy (selection k)) atTop (nhds fullFrontier)
    simpa only [clusterFloorEq] using selectedHierarchyLimit
  simpa only [levelValues, fullValues, hierarchy, fullFrontier] using
    And.intro hierarchyAntitone hierarchyLimit

#print axioms atomic_moment_hierarchy_converges

end D5.S3.Weil.Budget.AtomicMomentHierarchyConvergence
