/- GID: D5/S3/RenyiDivergence/OrderSpectrum
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pin cross-unit Renyi monotonicity and identify the above-one order supremum. -/

import Mathlib
import D5.S3.RenyiDivergence.OrderLimits
import D5.S3.RenyiDivergence.OrderInfinityLimit

/- Provenance: Native proof over pinned mathlib. -/

/- SEARCH RECEIPT (2026-08-15, pinned repository and pinned mathlib):
   * A pinned-mathlib search for `Renyi`, `Rényi`, `renyiDivergence`, `max divergence`,
     and `Hellinger divergence` found no probability-theory Renyi divergence, max-divergence,
     or reusable order-monotonicity theorem. The Renyi hits are the random-graph discussion in
     `Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean:24`, while the Hellinger
     hits are Hellinger--Toeplitz results rather than probability divergences.
   * `D5/S3/RenyiDivergence/Monotone.lean:35` records the crossing-one gap; lines 48 and 166
     provide the frozen same-side monotonicity theorems reused below.
   * `D5/S3/RenyiDivergence/OrderLimits.lean:34`, line 180, and line 195 provide respectively
     the frozen max-ratio ceiling and the two frozen KL comparisons reused below.
   * `D5/S3/RenyiDivergence/OrderInfinityLimit.lean:35` provides the frozen convergence to the
     log maximum likelihood ratio; line 122 also demonstrates `eventually_gt_atTop` on reals.
   * `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean:139` provides `ciSup_le`, and
     line 143 provides `le_ciSup` under the required bounded-range hypothesis.
   * `Mathlib/Topology/Order/OrderClosed.lean:131` provides `le_of_tendsto`, and
     `Mathlib/Order/Filter/AtTopBot/Basic.lean:66` supplies the `NeBot atTop` instance.
   * `Mathlib/Order/Filter/AtTopBot/Defs.lean:61` provides `eventually_gt_atTop`, used to turn
     sufficiently large real orders into elements of the subtype `Set.Ioi 1`.
-/

namespace D5.S3.RenyiDivergence.OrderSpectrum

open D5.S3.Divergence.ClassicalDPI

/-- Under discrete absolute continuity, Renyi divergence is monotone across order one. -/
theorem renyi_divergence_monotone_crossing_one {ι : Type*} [Fintype ι]
    (alpha beta : ℝ) (p q : ι → ℝ)
    (horder : 0 < alpha ∧ alpha < 1 ∧ 1 < beta)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : ∀ i, 0 < p i → 0 < q i) :
    renyiDivergence alpha p q ≤ renyiDivergence beta p q :=
  (renyi_divergence_le_kl_of_lt_one alpha p q ⟨horder.1, horder.2.1⟩ hp hq).trans
    (kl_le_renyi_divergence_of_one_lt beta p q horder.2.2 hp hq)

/-- Finite Renyi divergence is nondecreasing at positive orders away from order one, combining
the frozen same-side comparisons with the absolute-continuity crossing comparison. -/
theorem renyi_divergence_monotone_of_ne_one {ι : Type*} [Fintype ι]
    (alpha beta : ℝ) (p q : ι → ℝ)
    (horder : 0 < alpha ∧ alpha ≤ beta) (ha1 : alpha ≠ 1) (hb1 : beta ≠ 1)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq : ∀ i, 0 < p i → 0 < q i) :
    renyiDivergence alpha p q ≤ renyiDivergence beta p q := by
  rcases lt_or_gt_of_ne ha1 with ha_lt | ha_gt
  · rcases lt_or_gt_of_ne hb1 with hb_lt | hb_gt
    · exact renyi_divergence_monotone_of_lt_one alpha beta p q
        ⟨horder.1, horder.2, hb_lt⟩ hp hq_nonneg
    · exact renyi_divergence_monotone_crossing_one alpha beta p q
        ⟨horder.1, ha_lt, hb_gt⟩ hp hq
  · rcases lt_or_gt_of_ne hb1 with hb_lt | hb_gt
    · exfalso
      exact (not_lt_of_ge horder.2) (hb_lt.trans ha_gt)
    · exact renyi_divergence_monotone_of_one_lt alpha beta p q
        ⟨ha_gt, horder.2⟩ hp hq_nonneg

/-- The supremum of finite Renyi divergences over all orders strictly above one is exactly the
logarithm of the largest likelihood ratio. -/
theorem renyi_divergence_iSup_eq_log_sup_ratio {ι : Type*} [Fintype ι] [Nonempty ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : ∀ i, 0 < p i → 0 < q i) :
    ⨆ a : ↥(Set.Ioi (1 : ℝ)), renyiDivergence (a : ℝ) p q =
      Real.log (Finset.univ.sup' Finset.univ_nonempty (fun i => p i / q i)) := by
  let L : ℝ := Real.log (Finset.univ.sup' Finset.univ_nonempty (fun i => p i / q i))
  have hupper (a : ↥(Set.Ioi (1 : ℝ))) : renyiDivergence (a : ℝ) p q ≤ L := by
    simpa [L] using renyi_divergence_le_log_sup_ratio (a : ℝ) p q a.property hp hq
  have hbdd :
      BddAbove (Set.range (fun a : ↥(Set.Ioi (1 : ℝ)) => renyiDivergence (a : ℝ) p q)) := by
    refine ⟨L, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hupper a
  apply le_antisymm
  · exact ciSup_le hupper
  · refine le_of_tendsto
      (D5.S3.RenyiDivergence.OrderInfinityLimit.renyi_divergence_tendsto_log_sup_ratio
        p q hp hq) ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with a ha
    exact le_ciSup hbdd (⟨a, ha⟩ : ↥(Set.Ioi (1 : ℝ)))

#print axioms renyi_divergence_monotone_crossing_one
#print axioms renyi_divergence_monotone_of_ne_one
#print axioms renyi_divergence_iSup_eq_log_sup_ratio

end D5.S3.RenyiDivergence.OrderSpectrum
