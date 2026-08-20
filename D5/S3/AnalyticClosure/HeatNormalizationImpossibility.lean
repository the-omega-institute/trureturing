/- GID: D5/S3/AnalyticClosure/HeatNormalizationImpossibility
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boundary-divergent heat abscissae forbid normalization on their closed left side. -/

/- Library-search audit trail (2026-08-21):

   Pinned-library search.
   * `Summable` and `HasSum` are absent from pinned Batteries and pinned Lean
     core: zero files in either tree mention `Summable`.
   * Searched the whole of `Mathlib/Topology/Algebra/InfiniteSum/` (Basic,
     ConditionalInt, Constructions, Defs, DiscreteConvolution, ENNReal, Field,
     Group, GroupCompletion, Module, NatInt, Nonarchimedean, Order, Real, Ring,
     SummationFilter, TsumUniformlyOn, UniformOn) for a statement packaging
     "a non-summable family admits no positive-constant rescaling with unit
     sum". No such statement exists in the pinned library.
   * Inspected candidates: `summable_mul_left_iff`, `summable_mul_right_iff`,
     `Summable.mul_left`, `summable_norm_iff`, `HasSum.summable`,
     `Summable.hasSum`, `tsum_mul_left`, `not_summable_iff_tendsto_nat_atTop`.
   * Of those, exactly one is load-bearing below: `summable_mul_left_iff`
     (`Mathlib/Topology/Algebra/InfiniteSum/Ring.lean:106`), used with
     `HasSum.summable` to strip the positive scalar.

   Repository search.
   * The nearest recorded result is `heat_coefficient_summable_iff_of_boundary_divergent`
     (`D5/S3/Midline/HeatTraceConvergence.lean:22`), which proves
     `Summable (heatCoefficient M s) ↔ α < s.re` under the same
     `BoundaryDivergentAbscissa` hypothesis and resolves the same
     boundary/strict asymmetry. It is a different proposition: it characterises
     summability of the complex heat coefficients, whereas the statement below
     denies existence of a positive normalizing constant. It is deliberately
     not imported here. That module carries `generality: I` and imports the
     golden instance chain (`GoldenHeatBoundary`, `ZetaHeatTraceBridge`);
     importing it would, by rule H10 (specification line 219, enforced by
     SL-010), force this file to `I` and make a statement holding for an
     arbitrary index type and an arbitrary `M` depend on one instance family.
     The two-branch derivation from the definitions is preferred for that
     reason, at the cost of restating a case analysis that module also performs.
   * `BoundaryDivergentAbscissa` has eight occurrences in the repository: its
     definition site plus consumers in `HeatTraceConvergence`,
     `GoldenHeatBoundary`, `ZetaHeatTraceBridge`, and
     `HeatLayers/GoldenHeatLayers`. None states this file's conclusion.
   * No repository statement, formal or narrative, asserts a window-scoped or
     half-line normalization impossibility. This file therefore strengthens and
     restates nothing on record; it stands on its own.
   * SL-028 self-check: searched `D5/S3/` for `HasSum … 1` conclusions and for
     the name fragments `HeatNormalization`, `heat_normalization`,
     `NormalizationImpossibility`. No public declaration in the repository
     states this proposition up to renaming. This is a text-level search; the
     admit path does not render `Observe` diagnostics, so it is not certified
     exhaustive by the gate.

   Generality and address.
   * `G` is recorded. The imported `D5/S3/Midline/UniversalHeatTrace` is itself
     `generality: G`, so rule H10's prohibition on a `G` artifact importing an
     instance fact is satisfied. The statement carries no fixed index type, no
     fixed `M`, and no golden-specific hypothesis.
   * The address is `D5/S3/AnalyticClosure`. `D5/S3/Midline` holds every
     definition consumed here and would otherwise be the natural bucket, but it
     stands at twelve files, so adding one would cross the strictly-greater-
     than-twelve split threshold. `AnalyticClosure` holds four files, among them
     `PositiveSeriesTail` (`generality: G`, pinned-Mathlib-only, positive-series
     summability against a partial sum), which shares this file's subject.
   * The name records what is proved: a normalization impossibility on the
     closed left side of the abscissa. The conclusion has no upper cutoff, so
     no "window" appears in the address or the declaration name.

   Thin-wrapper check.
   * Substantive steps after bookkeeping: a two-way split on `s.re ≤ α`; the
     boundary branch discharged by the conjunct that `BoundaryDivergentAbscissa`
     adds over `IsHeatAbscissa`; the strict branch discharged by
     `IsHeatAbscissa`'s unrestricted-below conjunct; one library application to
     strip the positive scalar. Four steps, not a one-application consequence of
     any single pinned declaration.

   Openness provenance.
   * The target is entry L2 of the formalization queue in the HALF-DENSITY
     skeleton, a stated derivation gap rather than a restatement of a settled
     result. The skeleton states the conclusion over a half-open window; the
     lower bound is not used by the argument below and is therefore absent from
     the hypotheses.

   The inspected-candidate lists above are not claimed to be exhaustive.
-/

import Mathlib
import D5.S3.Midline.UniversalHeatTrace

/- Provenance: Native proof over pinned mathlib, unfolding the heat-abscissa
   definitions of the imported frozen module. -/

namespace D5.S3.AnalyticClosure.HeatNormalizationImpossibility

open D5.S3.Midline.UniversalHeatTrace

/-- At or below a boundary-divergent heat abscissa, no positive constant can
normalize the heat coefficients to a series with sum one: non-summability of
`exp (-s.re * M ·)` at or left of `α` (from `BoundaryDivergentAbscissa`)
propagates to any positive rescaling of it via `summable_mul_left_iff`, so no
such rescaling can have `HasSum … 1`. -/
theorem heat_normalization_impossibility {A : Type*}
    (M : A → ℝ) (α : ℝ) (hAbscissa : BoundaryDivergentAbscissa M α)
    (s : ℂ) (hs : s.re ≤ α) :
    ¬ ∃ c : ℝ, 0 < c ∧ HasSum (fun a ↦ c * Real.exp (-s.re * M a)) 1 := by
  have hnot : ¬Summable (fun a ↦ Real.exp (-s.re * M a)) := by
    rcases hs.eq_or_lt with heq | hlt
    · simpa [heq] using hAbscissa.2
    · exact hAbscissa.1.2 s.re hlt
  rintro ⟨c, hc, hsum⟩
  exact hnot ((summable_mul_left_iff hc.ne').mp hsum.summable)

#print axioms heat_normalization_impossibility

end D5.S3.AnalyticClosure.HeatNormalizationImpossibility
