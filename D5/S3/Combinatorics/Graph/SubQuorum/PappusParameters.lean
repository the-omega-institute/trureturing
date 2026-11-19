/- GID: D5/S3/Combinatorics/Graph/SubQuorum/PappusParameters
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/PappusParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=certified-instance
   digest: Exact Pappus representative and sub-quorum maxima. -/

import D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
import D5.S3.Combinatorics.Graph.SubQuorum.C4RepresentativeBounds

/-! The representative maximum and sub-quorum parameter of the fixed Pappus
graph both equal ten. These positive certificates have no qualifying refutation
basis under CLAUDE.md §3.3.
Source PR #28593, Sahbi revision 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0. -/

namespace D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
open StarFormingDissociationRefutation
open StarForming
open DoubleStarGrafting

section
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem omega_upper_of_objective_bound (n : ℕ)
    (h : ∀ T M, Feasible G T M → T.card + M.card ≤ n) : Omega G ≤ n := by
  classical
  apply Finset.sup_le
  intro p hp
  exact h p.1 p.2 (Finset.mem_filter.mp hp).2

end

set_option maxRecDepth 8192 in
/-- The Pappus representative upper bound is a consequence of the pair-packing bound. -/
theorem omega_pappus : Omega pappusGraph = 10 := by
  classical
  have regular : ∀ v, pappusGraph.degree v = 3 := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, DegreeCapacity.degree]
      using pappus_class.2.1
  have hu : Omega pappusGraph ≤ 10 := by
    apply omega_upper_of_objective_bound
    intro T M hf
    simpa using objective_general_bound pappusGraph pappusColor pappusColor_valid
      pappus_class.2.2 3 9 (by decide) regular (paritySide_card 9) T M hf
  have hh := parameter_comparison pappusGraph
  rw [beta_pappus] at hh
  omega

/-- Pappus attains ten in all three distinct parameters. -/
theorem pappus_parameters : beta pappusGraph 2 = 10 ∧
    psiSq pappusGraph = 10 ∧ Omega pappusGraph = 10 := by
  have hh := parameter_comparison pappusGraph
  rw [beta_pappus,omega_pappus] at hh
  exact ⟨beta_pappus,by omega,omega_pappus⟩

end D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
