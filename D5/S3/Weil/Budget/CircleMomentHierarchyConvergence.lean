/- GID: D5/S3/Weil/Budget/CircleMomentHierarchyConvergence
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/CircleMomentHierarchyConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nested circle-moment frontiers decrease to the determining-family completion frontier. -/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Order.MonotoneConvergence

/- Library-search audit trail (2026-09-01):
   * `D5/S3/Weil/Budget/FullCirclePrimalAttainment.lean` is the canonical
     sibling carrier: its feasible objects are `FiniteMeasure Circle`, used
     as `Measure Circle`, with the local Borel instances repeated below.
   * D5 searches for `moment_hierarchy`, `levelMatch`, `determiningFamily`,
     and `Antitone ... Tendsto` found only the frozen Real-carrier theorem
     `AtomicMomentHierarchyConvergence.atomic_moment_hierarchy_converges`.
   * Pinned Mathlib supplies `antitone_nat_of_succ_le`,
     `StrictMono.tendsto_atTop`, `tendsto_iff_tendsto_subseq_of_antitone`,
     and conditional `sSup` bounds, but no circle-moment hierarchy theorem.
   * No transport or Circle specialization of the Real-carrier owner exists;
     the proof below applies the order/limit argument directly on Circle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.CircleMomentHierarchyConvergence

open Filter MeasureTheory Set Topology

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- Nested finite circle-moment optimizer values decrease to the full completion
frontier when a weighted compactness subsequence closes every determining
constraint and preserves the optimizer white floor. -/
theorem circle_moment_hierarchy_converges
    (C cap : Real)
    (levelMatch : Nat -> Measure Circle -> Prop)
    (fullMatch : Measure Circle -> Prop)
    (resolventBudget whiteFloor : Measure Circle -> Real)
    (floorBound : forall nu, whiteFloor nu <= cap)
    (levelNested : forall N nu, levelMatch (N + 1) nu -> levelMatch N nu)
    (fullImpliesLevel : forall nu, fullMatch nu -> forall N, levelMatch N nu)
    (determiningFamily : forall nu,
      (forall N, levelMatch N nu) -> fullMatch nu)
    (optimizer : Nat -> Measure Circle)
    (optimizerLevel : forall N, levelMatch N (optimizer N))
    (optimizerBudget : forall N, resolventBudget (optimizer N) <= C)
    (optimizerOptimal : forall N,
      whiteFloor (optimizer N) = sSup
        {r : Real | exists nu : Measure Circle,
          levelMatch N nu /\ resolventBudget nu <= C /\ r = whiteFloor nu})
    (cluster : Measure Circle)
    (clusterLevels : forall N, levelMatch N cluster)
    (clusterBudget : resolventBudget cluster <= C)
    (selection : Nat -> Nat) (selectionStrict : StrictMono selection)
    (selectedFloorLimit : Tendsto
      (fun k => whiteFloor (optimizer (selection k))) atTop
      (nhds (whiteFloor cluster))) :
    let levelValues := fun N : Nat =>
      {r : Real | exists nu : Measure Circle,
        levelMatch N nu /\ resolventBudget nu <= C /\ r = whiteFloor nu}
    let fullValues :=
      {r : Real | exists nu : Measure Circle,
        fullMatch nu /\ resolventBudget nu <= C /\ r = whiteFloor nu}
    let hierarchy := fun N : Nat => sSup (levelValues N)
    let fullFrontier := sSup fullValues
    Antitone hierarchy /\ Tendsto hierarchy atTop (nhds fullFrontier) := by
  let levelValues := fun N : Nat =>
    {r : Real | exists nu : Measure Circle,
      levelMatch N nu /\ resolventBudget nu <= C /\ r = whiteFloor nu}
  let fullValues :=
    {r : Real | exists nu : Measure Circle,
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

-- The canonical Circle measure domain is inhabited.
example : Nonempty (Measure Circle) := ⟨0⟩

-- All hypotheses in the theorem signature are jointly satisfiable.
example :
    ∃ (C cap : Real)
      (levelMatch : Nat -> Measure Circle -> Prop)
      (fullMatch : Measure Circle -> Prop)
      (resolventBudget whiteFloor : Measure Circle -> Real)
      (optimizer : Nat -> Measure Circle) (cluster : Measure Circle)
      (selection : Nat -> Nat),
      (forall nu, whiteFloor nu <= cap) /\
      (forall N nu, levelMatch (N + 1) nu -> levelMatch N nu) /\
      (forall nu, fullMatch nu -> forall N, levelMatch N nu) /\
      (forall nu, (forall N, levelMatch N nu) -> fullMatch nu) /\
      (forall N, levelMatch N (optimizer N)) /\
      (forall N, resolventBudget (optimizer N) <= C) /\
      (forall N, whiteFloor (optimizer N) = sSup
        {r : Real | exists nu : Measure Circle,
          levelMatch N nu /\ resolventBudget nu <= C /\ r = whiteFloor nu}) /\
      (forall N, levelMatch N cluster) /\
      resolventBudget cluster <= C /\ StrictMono selection /\
      Tendsto (fun k => whiteFloor (optimizer (selection k))) atTop
        (nhds (whiteFloor cluster)) := by
  refine ⟨0, 0, (fun _ _ => True), (fun _ => True),
    (fun _ => 0), (fun _ => 0), (fun _ => 0), 0, id, ?_⟩
  simp only [le_refl, implies_true, forall_const, true_and]
  refine ⟨?_, strictMono_id, tendsto_const_nhds⟩
  have hset : {r : Real | ∃ _nu : Measure Circle, r = 0} = {0} := by
    ext r
    constructor
    · rintro ⟨_, rfl⟩
      exact Set.mem_singleton 0
    · intro hr
      have hr0 : r = 0 := Set.mem_singleton_iff.mp hr
      exact ⟨0, hr0⟩
  rw [hset, csSup_singleton]

#print axioms circle_moment_hierarchy_converges

end D5.S3.Weil.Budget.CircleMomentHierarchyConvergence
