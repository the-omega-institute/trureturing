/- GID: D5/S3/Analytic/Adelic/ToroidalJetDepth
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/ToroidalJetDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The first toroidally visible derivative layer equals the xi vanishing multiplicity. -/

import D5.S3.Zeros.Endpoints.XiEndpointValues
import Mathlib.Analysis.Analytic.Order

/- Library-search audit trail (2026-08-29):
   * Repository searches for toroidal jet depth, derivative towers, first
     nonzero period derivatives, and iterated-derivative minima found no exact
     frozen theorem or canonical depth definition.
   * The frozen endpoint theorem supplies the independent nonzero value needed
     to show that the entire canonical `xiReading` has finite analytic order at
     every point; it does not state a jet-depth result.
   * Pinned Mathlib has no toroidal theorem. Its exact analytic constituent
     `analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero` characterizes a finite
     vanishing order by the first nonzero iterated derivative. The companion
     lower-order characterization and `Nat.sInf_mem`/`Nat.sInf_le` are applied
     directly.
   * Body-shape searches found no D5 infimum of derivative visibility. The
     source test is inlined in the public statement, so no `def` or `abbrev` is
     introduced and the least index is not defined from the target equality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.ToroidalJetDepth

open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.XiEndpointValues

/--
For analytic twists with at least one nonzero value at the observation point,
the least derivative layer at which some normalized toroidal period is visible
is exactly the natural vanishing multiplicity of the canonical xi reading.
-/
theorem toroidal_jet_depth_eq_vanishing_order {Index : Type*} (s : ℂ)
    (twist : Index -> ℂ -> ℂ)
    (twistDifferentiable : ∀ index, Differentiable ℂ (twist index))
    (pointwiseNonvanishing : ∃ index, twist index s ≠ 0) :
    sInf {j : Nat |
        ∃ index,
          iteratedDeriv j
            (fun point => xiReading point * twist index point) s ≠ 0} =
      analyticOrderNatAt xiReading s := by
  have xiAnalytic : AnalyticAt ℂ xiReading s :=
    xi_reading_differentiable.analyticAt s
  have xiAnalyticOn : AnalyticOnNhd ℂ xiReading Set.univ :=
    xi_reading_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have xiAtZeroNonzero : xiReading 0 ≠ 0 := by
    rw [xi_reading_endpoint_values.1]
    norm_num
  have xiOrderAtZero : analyticOrderAt xiReading 0 = 0 :=
    (xi_reading_differentiable.analyticAt 0).analyticOrderAt_eq_zero.mpr
      xiAtZeroNonzero
  have xiOrderFinite : analyticOrderAt xiReading s ≠ ⊤ := by
    refine xiAnalyticOn.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ s) ?_
    rw [xiOrderAtZero]
    exact ENat.zero_ne_top
  let multiplicity := analyticOrderNatAt xiReading s
  have multiplicityCast :
      (multiplicity : ENat) = analyticOrderAt xiReading s :=
    Nat.cast_analyticOrderNatAt xiOrderFinite
  obtain ⟨chosen, chosenNonzero⟩ := pointwiseNonvanishing
  have twistAnalytic : ∀ index, AnalyticAt ℂ (twist index) s :=
    fun index => (twistDifferentiable index).analyticAt s
  have periodAnalytic : ∀ index,
      AnalyticAt ℂ (fun point => xiReading point * twist index point) s :=
    fun index => xiAnalytic.mul (twistAnalytic index)
  have chosenOrder :
      analyticOrderAt
          (fun point => xiReading point * twist chosen point) s =
        (multiplicity : ENat) := by
    calc
      analyticOrderAt
          (fun point => xiReading point * twist chosen point) s =
          analyticOrderAt xiReading s +
            analyticOrderAt (twist chosen) s := by
        change analyticOrderAt (xiReading * twist chosen) s = _
        exact analyticOrderAt_mul xiAnalytic (twistAnalytic chosen)
      _ = analyticOrderAt xiReading s + 0 := by
        rw [(twistAnalytic chosen).analyticOrderAt_eq_zero.mpr chosenNonzero]
      _ = analyticOrderAt xiReading s := add_zero _
      _ = (multiplicity : ENat) := multiplicityCast.symm
  have chosenDerivativeNonzero :
      iteratedDeriv multiplicity
          (fun point => xiReading point * twist chosen point) s ≠ 0 :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
      (periodAnalytic chosen)).mp chosenOrder |>.2
  have visibleDepthsNonempty :
      {j : Nat |
        ∃ index,
          iteratedDeriv j
            (fun point => xiReading point * twist index point) s ≠ 0}.Nonempty :=
    ⟨multiplicity, chosen, chosenDerivativeNonzero⟩
  have earlierDerivativesVanish : ∀ index,
      ∀ j < multiplicity,
        iteratedDeriv j
          (fun point => xiReading point * twist index point) s = 0 := by
    intro index
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (periodAnalytic index)).mp
    calc
      (multiplicity : ENat) = analyticOrderAt xiReading s :=
        multiplicityCast
      _ ≤ analyticOrderAt xiReading s +
          analyticOrderAt (twist index) s := le_add_right le_rfl
      _ = analyticOrderAt
          (fun point => xiReading point * twist index point) s := by
        change _ = analyticOrderAt (xiReading * twist index) s
        exact (analyticOrderAt_mul xiAnalytic (twistAnalytic index)).symm
  change sInf {j : Nat |
      ∃ index,
        iteratedDeriv j
          (fun point => xiReading point * twist index point) s ≠ 0} =
    multiplicity
  apply le_antisymm
  · exact Nat.sInf_le ⟨chosen, chosenDerivativeNonzero⟩
  · apply le_of_not_gt
    intro depthLess
    obtain ⟨index, derivativeNonzero⟩ :=
      Nat.sInf_mem visibleDepthsNonempty
    exact derivativeNonzero
      (earlierDerivativesVanish index _ depthLess)

example (s : ℂ) :
    ∃ (twist : Unit -> ℂ -> ℂ),
      (∀ index, Differentiable ℂ (twist index)) ∧
        ∃ index, twist index s ≠ 0 := by
  refine ⟨fun _ _ => 1, ?_, (), one_ne_zero⟩
  intro index
  fun_prop

example : Nonempty ℂ := ⟨0⟩

#print axioms toroidal_jet_depth_eq_vanishing_order

end D5.S3.Analytic.Adelic.ToroidalJetDepth
