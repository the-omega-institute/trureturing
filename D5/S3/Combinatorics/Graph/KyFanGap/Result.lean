/- GID: D5/S3/Combinatorics/Graph/KyFanGap/Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Prime.Infinite]
   utility: none
   digest: Infinitely many graph Ky Fan prefixes have a strict asymptotic gap. -/

import D5.S3.Combinatorics.Graph.KyFanGap.NearExtremal
import D5.S3.Combinatorics.Graph.KyFanGap.BlowUp
import Mathlib.Data.Nat.Prime.Infinite

/-! A uniform nonsquare gap and the blow-up limit settle the graph conjecture. -/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace D5.S3.Combinatorics.Graph.KyFanGap

/-- Infinitely many normalized graph Ky Fan maxima converge strictly below
Nikiforov's universal upper bound. -/
theorem result : conjecture := by
  classical
  apply (Set.infinite_of_not_bddAbove Nat.not_bddAbove_setOfPred_prime).mono
  intro k hk
  have hk1 : 1 ≤ k := le_trans (by omega) hk.two_le
  obtain ⟨δ, hδ, hgap⟩ := uniform_gap hk1 hk.not_isSquare
  refine ⟨normalizedSupremum k, tendsto_xi_div hk1, ?_⟩
  have hbound : normalizedSupremum k ≤ (1 + Real.sqrt k) / 2 - δ := by
    apply le_of_tendsto (tendsto_xi_div hk1)
    filter_upwards [eventually_ge_atTop k] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    apply (div_le_iff₀ hnpos).mpr
    apply Finset.sup'_le
    intro G _
    have h := hgap n hn (G.adjMatrix ℝ) (G.isSymm_adjMatrix (α := ℝ))
      (G.isAdjMatrix_adjMatrix ℝ).zero_or_one
    exact (div_le_iff₀ hnpos).mp h
  exact hbound.trans_lt (sub_lt_self _ hδ)

end D5.S3.Combinatorics.Graph.KyFanGap
