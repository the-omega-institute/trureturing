/- GID: D5/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A zero-sum gauge preserves the global sum of adelic local contributions. -/

import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/- Library-search audit trail (2026-08-28):
   * Repository searches found no adelic completion declaration or prior coverage of this atom.
   * Pinned Mathlib and Loogle both return the exact algebraic theorem
     `Summable.tsum_add`; it is applied directly below.
   * GitHub Lean-code searches found no `AdelicPlace` or `ZeroSumGauge` declaration.
   * The source defines all places as `V_f \sqcup V_infty`, each local contribution
     `L_v`, and their global additive sum. It does not define a bridge from that sum
     to the earlier quotient-valued structural completion signature `K(C)/G`.
   * Summability is bundled into the semantic types so the source's infinite sums
     have their ordinary additive meaning; no finiteness of the place types is assumed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.Adelic.ZeroSumGaugeGlobalCompletion

universe u_f u_i

/-- The source's full set of local places, split into finite and infinite places. -/
abbrev AdelicPlace (FinitePlace : Type u_f) (InfinitePlace : Type u_i) :=
  FinitePlace ⊕ InfinitePlace

/-- A summable family of real local contributions `L_v` over every adelic place. -/
structure AdelicLocalLedger (FinitePlace : Type u_f) (InfinitePlace : Type u_i) where
  localContribution : AdelicPlace FinitePlace InfinitePlace → Real
  summable_localContribution : Summable localContribution

/-- A local gauge shift `b_v` whose global additive contribution is zero. -/
structure ZeroSumGauge (FinitePlace : Type u_f) (InfinitePlace : Type u_i) where
  shift : AdelicPlace FinitePlace InfinitePlace → Real
  hasSum_zero : HasSum shift 0

/-- Apply the source's local gauge change `L_v ↦ L_v + b_v`. -/
def gaugeTransform {FinitePlace : Type u_f} {InfinitePlace : Type u_i}
    (ledger : AdelicLocalLedger FinitePlace InfinitePlace)
    (gauge : ZeroSumGauge FinitePlace InfinitePlace) :
    AdelicLocalLedger FinitePlace InfinitePlace where
  localContribution place := ledger.localContribution place + gauge.shift place
  summable_localContribution :=
    ledger.summable_localContribution.add gauge.hasSum_zero.summable

/-- The section-15 global additive completion reading `Δ_glob = Σ_v L_v`. -/
def globalAdditiveCompletion {FinitePlace : Type u_f} {InfinitePlace : Type u_i}
    (ledger : AdelicLocalLedger FinitePlace InfinitePlace) : Real :=
  ∑' place, ledger.localContribution place

/-- A zero-sum change of local gauges preserves the global additive completion. -/
theorem zero_sum_gauge_preserves_global_completion
    {FinitePlace : Type u_f} {InfinitePlace : Type u_i}
    (ledger : AdelicLocalLedger FinitePlace InfinitePlace)
    (gauge : ZeroSumGauge FinitePlace InfinitePlace) :
    globalAdditiveCompletion (gaugeTransform ledger gauge) =
      globalAdditiveCompletion ledger := by
  change (∑' place : AdelicPlace FinitePlace InfinitePlace,
      (ledger.localContribution place + gauge.shift place)) =
    ∑' place : AdelicPlace FinitePlace InfinitePlace,
      ledger.localContribution place
  rw [ledger.summable_localContribution.tsum_add gauge.hasSum_zero.summable,
    gauge.hasSum_zero.tsum_eq, add_zero]

private def pairedGauge (r : Real) : ZeroSumGauge Unit Unit where
  shift place :=
    (if place = Sum.inl () then r else 0) +
      if place = Sum.inr () then -r else 0
  hasSum_zero := by
    simpa using
      (hasSum_ite_eq (Sum.inl () : AdelicPlace Unit Unit) r).add
        (hasSum_ite_eq (Sum.inr () : AdelicPlace Unit Unit) (-r))

/- Reverse fidelity probe: a nonzero two-place gauge changes a local contribution,
between a finite and an infinite place, while the public theorem still forces the
global completion reading to agree. -/
example (ledger : AdelicLocalLedger Unit Unit) (r : Real) (hr : r ≠ 0) :
    (gaugeTransform ledger (pairedGauge r)).localContribution (Sum.inl ()) ≠
        ledger.localContribution (Sum.inl ()) ∧
      globalAdditiveCompletion (gaugeTransform ledger (pairedGauge r)) =
        globalAdditiveCompletion ledger := by
  constructor
  · intro hlocal
    have hlocal' : ledger.localContribution (Sum.inl ()) + r =
        ledger.localContribution (Sum.inl ()) := by
      simpa [gaugeTransform, pairedGauge] using hlocal
    apply hr
    apply add_left_cancel (a := ledger.localContribution (Sum.inl ()))
    simpa using hlocal'
  · exact zero_sum_gauge_preserves_global_completion ledger (pairedGauge r)

#print axioms zero_sum_gauge_preserves_global_completion

end D5.S3.Analytic.Adelic.ZeroSumGaugeGlobalCompletion
