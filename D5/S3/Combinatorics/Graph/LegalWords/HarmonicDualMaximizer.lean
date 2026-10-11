/- GID: D5/S3/Combinatorics/Graph/LegalWords/HarmonicDualMaximizer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/HarmonicDualMaximizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Parallel independent-set flips constrain positive stationary harmonic-dual masses. -/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators symmDiff
open Finset
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

namespace D5.S3.Combinatorics.Graph.LegalWords.HarmonicDualMaximizer

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The derivative load, indexed by all legal single-coordinate flips. -/
noncomputable def coordinateLoad (ν : Finset V → ℝ) (S : Finset V) : ℝ :=
  ∑ j : V, if H.IsIndepSet (↑(S ∆ {j}) : Set V) then
    (ν (S ∆ {j}) / (ν S + ν (S ∆ {j}))) ^ 2 else 0

/-- Each independent-set edge is counted once, from its endpoint lacking the added vertex. -/
noncomputable def harmonicDual (ν : Finset V → ℝ) : ℝ :=
  ∑ S ∈ configurations H univ, ∑ i : V,
    if i ∉ S ∧ H.IsIndepSet (↑(insert i S) : Set V) then
      ν S * ν (insert i S) / (ν S + ν (insert i S)) else 0

/-- Square-root regularization on the actual independent configurations. -/
noncomputable def regularizedDual (ε : ℝ) (ν : Finset V → ℝ) : ℝ :=
  harmonicDual H ν + ε * ∑ S ∈ configurations H univ, Real.sqrt (ν S)

end D5.S3.Combinatorics.Graph.LegalWords.HarmonicDualMaximizer
