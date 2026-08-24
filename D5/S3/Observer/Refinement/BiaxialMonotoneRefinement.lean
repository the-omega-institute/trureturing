/- GID: D5/S3/Observer/Refinement/BiaxialMonotoneRefinement
   generality: G
   mirror-B: D5/B/S3/Observer/Refinement/BiaxialMonotoneRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Both observation axes independently and jointly shrink indistinguishability. -/

import D5.S3.ConceptDynamics.Experiment.ExperimentExpansionMonotonicity
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Iterate

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'biaxial_monotone' D5 Golden/Frozen/accepted` found no pre-existing match.
   * The requested `rg -inE 'Indist|refine.*monotone|观察' D5/S3/` search
     found `ExperimentExpansionMonotonicity.expansion_shrinks_indistinguishability`,
     which proves the general experiment-set axis and is reused below.
   * `FiniteFutureCongruence.finiteFutureRelation` gives a one-readout finite-horizon
     relation but no horizon-monotonicity theorem or independent prime-set axis.
   * Pinned Mathlib supplies `Function.iterate` and basic set inclusion; repository and
     Mathlib searches found no public or private theorem combining both axes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Refinement.BiaxialMonotoneRefinement

open D5.S3.ConceptDynamics.Experiment.ExperimentExpansionMonotonicity

/-- The prime-time observation experiments enabled by a finite prime set and time window. -/
def observationSchedule (J : Finset Nat) (m : Nat) : Set (Nat × Nat) :=
  {index | index.1 ∈ J ∧ index.2 < m}

/-- Run the experiment indexed by prime `p` and time `k` on a dynamical state. -/
def orbitExperiment {X O : Type*} (readout : Nat -> X -> O) (T : X -> X) :
    Nat × Nat -> X -> O :=
  fun index x => readout index.1 ((T^[index.2]) x)

/-- Two states are indistinguishable when every scheduled prime-time readout agrees. -/
def Indist {X O : Type*} (J : Finset Nat) (m : Nat)
    (readout : Nat -> X -> O) (T : X -> X) : Set (X × X) :=
  experimentIndistinguishability (observationSchedule J m) (orbitExperiment readout T)

/-- At fixed time depth, observing more primes can only shrink indistinguishability. -/
theorem prime_axis_monotone {X O : Type*} (J K : Finset Nat) (m : Nat)
    (readout : Nat -> X -> O) (T : X -> X) (hJK : J ⊆ K) :
    Indist K m readout T ⊆ Indist J m readout T := by
  unfold Indist
  apply expansion_shrinks_indistinguishability
  intro index hindex
  exact ⟨hJK hindex.1, hindex.2⟩

/-- At a fixed prime set, observing for longer can only shrink indistinguishability. -/
theorem time_axis_monotone {X O : Type*} (J : Finset Nat) (m n : Nat)
    (readout : Nat -> X -> O) (T : X -> X) (hmn : m ≤ n) :
    Indist J n readout T ⊆ Indist J m readout T := by
  unfold Indist
  apply expansion_shrinks_indistinguishability
  intro index hindex
  exact ⟨hindex.1, Nat.lt_of_lt_of_le hindex.2 hmn⟩

/-- Enlarging both the prime set and time window jointly refines indistinguishability. -/
theorem biaxial_monotone {X O : Type*} (J K : Finset Nat) (m n : Nat)
    (readout : Nat -> X -> O) (T : X -> X) (hJK : J ⊆ K) (hmn : m ≤ n) :
    Indist K n readout T ⊆ Indist J m readout T := by
  exact (prime_axis_monotone J K n readout T hJK).trans
    (time_axis_monotone J m n readout T hmn)

example :
    Indist ({2, 3} : Finset Nat) 3 (fun p x : Nat => x + p) Nat.succ ⊆
      Indist ({2} : Finset Nat) 1 (fun p x : Nat => x + p) Nat.succ := by
  exact biaxial_monotone {2} {2, 3} 1 3 _ _ (by simp) (by decide)

#print axioms biaxial_monotone

end D5.S3.Observer.Refinement.BiaxialMonotoneRefinement
