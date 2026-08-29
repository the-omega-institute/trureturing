/- GID: D5/S3/Weil/ZetaAnalytic/FiniteWindowGlobalBoundary
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaAnalytic/FiniteWindowGlobalBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local frame bounds stay positive while gap probes force the global floor to zero. -/

import D5.S3.Weil.ZetaAnalytic.WhiteFloorSamplingDuality

/- Library-search audit trail (2026-08-29):
   * D5 searches for finite-window white-floor positivity, global-boundary
     limits, and pure-point sampling gaps found no exact theorem.
   * `SupportRayleighMonotonicity.support_rayleigh_monotonicity` has the
     adjacent reversed-infimum argument, but not the real-window limit.
   * Pinned Mathlib exact hits `le_csInf`, `csInf_le`, `tendsto_order`, and
     `eventually_ge_atTop` supply only the order/filter primitives used below.
   * Body-shape searches for a window-indexed unit sampling infimum and its
     vanishing limit found no canonical D5 definition to import. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaAnalytic.FiniteWindowGlobalBoundary

open Filter Set Topology

/-- Positive sampling bounds on every finite window put each local floor in
the strict interior, while unit gap probes with vanishing sampling energy put
the increasing-window limit on the boundary. -/
theorem finite_window_positive_global_boundary
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace Real H]
    [NormedAddCommGroup K] [NormedSpace Real K]
    (sampling : H →L[Real] K)
    (windowAdmissible : Real -> H -> Prop)
    (windowMonotone : forall {L1 L2 : Real}, L1 <= L2 -> forall f,
      windowAdmissible L1 f -> windowAdmissible L2 f)
    (unitWindowNonempty : forall L : Real, 0 < L ->
      exists f : H, windowAdmissible L f /\ ‖f‖ = 1)
    (finiteFrameBound : forall L : Real, 0 < L ->
      exists c : Real, 0 < c /\ forall f : H, windowAdmissible L f ->
        c * ‖f‖ ^ 2 <= ‖sampling f‖ ^ 2)
    (probe : Nat -> H) (probeWindow : Nat -> Real)
    (probeUnit : forall n, ‖probe n‖ = 1)
    (probeAdmissible : forall n, windowAdmissible (probeWindow n) (probe n))
    (probeEnergyVanishes :
      Tendsto (fun n => ‖sampling (probe n)‖ ^ 2) atTop (nhds 0)) :
    let floor := fun L : Real => sInf
      {r : Real | exists f : H,
        windowAdmissible L f /\ ‖f‖ = 1 /\ r = ‖sampling f‖ ^ 2}
    (forall L : Real, 0 < L -> 0 < floor L) /\
      Tendsto floor atTop (nhds 0) := by
  let values : Real -> Set Real := fun L =>
    {r | exists f : H,
      windowAdmissible L f /\ ‖f‖ = 1 /\ r = ‖sampling f‖ ^ 2}
  have valuesBddBelow (L : Real) : BddBelow (values L) := by
    refine ⟨0, ?_⟩
    rintro r ⟨f, _, _, rfl⟩
    positivity
  have valuesNonempty (L : Real) (hL : 0 < L) : (values L).Nonempty := by
    rcases unitWindowNonempty L hL with ⟨f, hf, hUnit⟩
    exact ⟨‖sampling f‖ ^ 2, ⟨f, hf, hUnit, rfl⟩⟩
  have floorPositive (L : Real) (hL : 0 < L) :
      0 < sInf (values L) := by
    rcases finiteFrameBound L hL with ⟨c, hc, hFrame⟩
    refine hc.trans_le (le_csInf (valuesNonempty L hL) ?_)
    rintro r ⟨f, hf, hUnit, rfl⟩
    calc
      c = c * ‖f‖ ^ 2 := by rw [hUnit]; norm_num
      _ <= ‖sampling f‖ ^ 2 := hFrame f hf
  have floorTendsToZero :
      Tendsto (fun L : Real => sInf (values L)) atTop (nhds 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro lower hLower
      filter_upwards [eventually_gt_atTop (0 : Real)] with L hL
      exact hLower.trans (floorPositive L hL)
    · intro upper hUpper
      have probeEventuallyBelow : Filter.Eventually
          (fun n => ‖sampling (probe n)‖ ^ 2 < upper) atTop :=
        (tendsto_order.1 probeEnergyVanishes).2 upper hUpper
      rcases probeEventuallyBelow.exists with ⟨n, hn⟩
      filter_upwards [eventually_ge_atTop (probeWindow n)] with L hL
      apply (csInf_le (valuesBddBelow L) ?_).trans_lt hn
      exact ⟨probe n, windowMonotone hL (probe n) (probeAdmissible n),
        probeUnit n, rfl⟩
  simpa only [values] using And.intro floorPositive floorTendsToZero

#print axioms finite_window_positive_global_boundary

end D5.S3.Weil.ZetaAnalytic.FiniteWindowGlobalBoundary
