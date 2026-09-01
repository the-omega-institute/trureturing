/- GID: D5/S3/Weil/TestFunctions/PaleyWienerGauge
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/PaleyWienerGauge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equality on window-supported tests defines the Paley-Wiener gauge setoid. -/

import Mathlib.Analysis.Distribution.Support
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-09-01):
   * Repository searches for `Paley-Wiener`, `tempered distribution`, window
     restriction, and equality kernels found no existing gauge definition.
     The adjacent `ExternalSupportInvisibility` and `FiniteMomentElimination`
     modules use the same tempered-distribution carrier, but prove later
     invisibility and moment-correction statements rather than this definition.
   * Pinned Mathlib's exact general construction is `Setoid.ker`: equality
     after any readout is an equivalence relation. `TemperedDistribution.delta_apply`
     and `Distribution.dsupport_delta` supply the nontrivial endpoint
     Dirac witness below. Mathlib has no packaged restriction of a tempered
     distribution to an open set.
   * Searches of the other pinned Lean packages found no Paley-Wiener gauge or
     tempered-distribution restriction API. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.TestFunctions.PaleyWienerGauge

open Function Set
open scoped SchwartzMap

noncomputable section

/-- Schwartz tests whose topological support lies in the Paley-Wiener window
`(-2L, 2L)`. -/
def PaleyWienerWindow (L : ℝ) :=
  {test : 𝓢(ℝ, ℂ) // tsupport test ⊆ Ioo (-(2 * L)) (2 * L)}

/-- The restriction of a tempered distribution to the Paley-Wiener window,
represented by its action on every Schwartz test supported in that window. -/
def paleyWienerRestriction (L : ℝ) :
    𝓢'(ℝ, ℂ) → PaleyWienerWindow L → ℂ :=
  fun distribution test => distribution test.1

/-- Definition 428.1: two tempered distributions are Paley-Wiener
`L`-gauge equivalent when their restrictions to `(-2L, 2L)` agree. -/
def paleyWienerGauge (L : ℝ) : Setoid 𝓢'(ℝ, ℂ) :=
  Setoid.ker (paleyWienerRestriction L)

/-- The gauge relation is exactly equality on all tests supported in the
open Paley-Wiener window. -/
theorem paley_wiener_gauge_iff (L : ℝ) (left right : 𝓢'(ℝ, ℂ)) :
    paleyWienerGauge L left right ↔
      ∀ test : PaleyWienerWindow L, left test.1 = right test.1 := by
  constructor
  · intro h test
    exact congrFun h test
  · intro h
    funext test
    exact h test

private theorem delta_ne_zero (x : ℝ) :
    TemperedDistribution.delta x ≠ (0 : 𝓢'(ℝ, ℂ)) := by
  intro hzero
  have hx : x ∈ Distribution.dsupport (TemperedDistribution.delta x) := by
    rw [Distribution.dsupport_delta]
    exact Set.mem_singleton x
  rw [hzero, Distribution.mem_dsupport_iff_forall_exists_ne] at hx
  obtain ⟨test, _, htest⟩ := hx Set.univ (Set.mem_univ x) isOpen_univ
  exact htest (by simp)

/-- The gauge is genuinely coarser than equality: the zero distribution and
the Dirac distribution at the excluded endpoint `2L` are distinct but have
the same restriction to the open window. -/
theorem exists_distinct_paley_wiener_gauge_pair (L : ℝ) :
    ∃ left right : 𝓢'(ℝ, ℂ),
      left ≠ right ∧ paleyWienerGauge L left right := by
  refine ⟨0, TemperedDistribution.delta (2 * L), ?_, ?_⟩
  · exact Ne.symm (delta_ne_zero (2 * L))
  · rw [paley_wiener_gauge_iff]
    intro test
    rw [TemperedDistribution.delta_apply]
    by_contra htest
    have hnonzero : test.1 (2 * L) ≠ 0 := Ne.symm htest
    have hmem : 2 * L ∈ tsupport test.1 := subset_tsupport test.1 hnonzero
    exact (test.2 hmem).2.false

#print axioms paleyWienerGauge
#print axioms paley_wiener_gauge_iff
#print axioms exists_distinct_paley_wiener_gauge_pair

end

end D5.S3.Weil.TestFunctions.PaleyWienerGauge
