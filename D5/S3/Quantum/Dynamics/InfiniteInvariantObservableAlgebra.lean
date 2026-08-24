/- GID: D5/S3/Quantum/Dynamics/InfiniteInvariantObservableAlgebra
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/InfiniteInvariantObservableAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The supremum of finite pullback algebras is the canonical least stable observable algebra. -/

import D5.S3.Quantum.Dynamics.LeastInvariantObservableAlgebra

/- Library-search audit trail (2026-08-25):
   * The frozen `finiteKoopmanClosure`, `invariantObservableExtensions`,
     `PullbackInvariant`, and `stableObservableAlgebraEquiv` are the canonical
     observable-algebra primitives and are imported directly.
   * The frozen `least_invariant_observable_algebra` theorem gives stabilization,
     invariance, leastness, and the canonical completed-state equivalence at the
     least finite depth; no accepted theorem exposes the source's infinite-chain
     supremum object, so this module adds only that residual wrapper.
   * Pinned Mathlib supplies complete-lattice `sSup`, `sSup_le`, and `le_sSup`.
 -/

noncomputable section

namespace D5.S3.Quantum.Dynamics.InfiniteInvariantObservableAlgebra

open D5.S3.ObserverMemory.Refinement.PredictionCompletion
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.Quantum.Dynamics.LeastInvariantObservableAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The least upper bound of all finite pullback-generated observable algebras. -/
def infiniteKoopmanClosure {Y O : Type*} (update : Y -> Y)
    (readout : Y -> O) : StarSubalgebra ℂ (Y -> ℂ) :=
  sSup (Set.range (finiteKoopmanClosure update readout))

private theorem finite_closure_le_least_extension
    {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) (depth : Nat)
    (algebra : StarSubalgebra ℂ (Y -> ℂ))
    (hExtension : algebra ∈ invariantObservableExtensions update readout) :
    finiteKoopmanClosure update readout depth <= algebra := by
  apply StarAlgebra.adjoin_le
  rintro generator ⟨n, hn, g, hg, rfl⟩
  have hiterate : forall k, g ∘ (update^[k]) ∈ algebra := by
    intro k
    induction k with
    | zero =>
        simpa using hExtension.1 hg
    | succ k ih =>
        simpa only [Function.comp_def, Function.iterate_succ_apply] using
          hExtension.2 _ ih
  exact hiterate n

private theorem infinite_closure_eq_stable
    {Y O : Type*} [Fintype Y] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    infiniteKoopmanClosure update readout =
      finiteKoopmanClosure update readout
        (predictionStabilityDepth update readout) := by
  let depth := predictionStabilityDepth update readout
  have hbase := least_invariant_observable_algebra update readout hreadout
  dsimp only at hbase
  have hleast :
      finiteKoopmanClosure update readout depth =
        sInf (invariantObservableExtensions update readout) :=
    hbase.2.2.2.1
  have hupper : forall n,
      finiteKoopmanClosure update readout n <=
        finiteKoopmanClosure update readout depth := by
    intro n
    calc
      finiteKoopmanClosure update readout n <=
          sInf (invariantObservableExtensions update readout) := by
        apply le_sInf
        intro algebra hExtension
        exact finite_closure_le_least_extension
          update readout n algebra hExtension
      _ = finiteKoopmanClosure update readout depth := hleast.symm
  apply le_antisymm
  · apply sSup_le
    intro algebra halgebra
    rcases halgebra with ⟨n, rfl⟩
    exact hupper n
  · apply le_sSup
    exact ⟨depth, rfl⟩

theorem infinite_invariant_observable_algebra
    {Y O : Type*} [Fintype Y] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O)
    (hreadout : Function.Surjective readout) :
    let depth := predictionStabilityDepth update readout
    infiniteKoopmanClosure update readout =
        finiteKoopmanClosure update readout depth ∧
      initialObservableAlgebra readout <=
        infiniteKoopmanClosure update readout ∧
      PullbackInvariant update (infiniteKoopmanClosure update readout) ∧
      (infiniteKoopmanClosure update readout =
        sInf (invariantObservableExtensions update readout)) ∧
      (forall
          (f : finiteKoopmanClosure update readout
            (predictionStabilityDepth update readout)) (state : Y),
        stableObservableAlgebraEquiv update readout hreadout
          f (completionProjection update readout state) = f.1 state) := by
  dsimp only
  let depth := predictionStabilityDepth update readout
  have hbase := least_invariant_observable_algebra update readout hreadout
  dsimp only at hbase
  have hleast :
      finiteKoopmanClosure update readout depth =
        sInf (invariantObservableExtensions update readout) :=
    hbase.2.2.2.1
  have hupper : forall n,
      finiteKoopmanClosure update readout n <=
        finiteKoopmanClosure update readout depth := by
    intro n
    calc
      finiteKoopmanClosure update readout n <=
          sInf (invariantObservableExtensions update readout) := by
        apply le_sInf
        intro algebra hExtension
        exact finite_closure_le_least_extension
          update readout n algebra hExtension
      _ = finiteKoopmanClosure update readout depth := hleast.symm
  have hsSup_le :
      sSup (Set.range (finiteKoopmanClosure update readout)) <=
        finiteKoopmanClosure update readout depth := by
    apply sSup_le
    intro algebra halgebra
    rcases halgebra with ⟨n, rfl⟩
    exact hupper n
  have hdepth_le_sSup :
      finiteKoopmanClosure update readout depth <=
        sSup (Set.range (finiteKoopmanClosure update readout)) := by
    apply le_sSup
    exact ⟨depth, rfl⟩
  have hchain :
      infiniteKoopmanClosure update readout =
        finiteKoopmanClosure update readout depth :=
    le_antisymm hsSup_le hdepth_le_sSup
  refine ⟨hchain, ?_, ?_, ?_, ?_⟩
  · rw [hchain]
    intro f hf
    apply StarAlgebra.subset_adjoin
    exact ⟨0, Nat.zero_le _, f, hf, by simp⟩
  · rw [hchain]
    exact hbase.2.2.1
  · rw [hchain]
    exact hleast
  · intro f state
    exact hbase.2.2.2.2 f state

#print axioms infinite_invariant_observable_algebra

end D5.S3.Quantum.Dynamics.InfiniteInvariantObservableAlgebra
