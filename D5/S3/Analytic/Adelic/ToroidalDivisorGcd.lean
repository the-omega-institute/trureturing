/- GID: D5/S3/Analytic/Adelic/ToroidalDivisorGcd
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/ToroidalDivisorGcd
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pointwise nonvanishing twists make xi the divisor-gcd of normalized toroidal periods. -/

import D5.S3.Zeros.CompletedZeta
import Mathlib.Analysis.Analytic.Order

/- Library-search audit trail (2026-08-29):
   * Repository searches for toroidal-period vanishing orders, pointwise
     divisor minima, and the `xiReading * twist` body found no exact frozen
     theorem owner. The canonical entire `xiReading` and its differentiability
     are imported from `CompletedZeta` rather than redeclared.
   * The related frozen Adelic modules construct period/twist charts and finite
     compact-window frames, but neither states the order-infimum or divisor
     identity below.
   * Pinned Mathlib has no toroidal divisor-gcd theorem. Its exact analytic
     constituents `analyticOrderAt_mul` and
     `AnalyticAt.analyticOrderAt_eq_zero`, together with complete-lattice
     infimum laws, are applied directly.
   * Body-shape searches found no D5 definition of the normalized product
     family. It is constructed inline, so this module introduces no new
     `def` or `abbrev`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.ToroidalDivisorGcd

open D5.S3.Zeros.CompletedZeta

/--
For an analytic family of quadratic twists that is pointwise nonvanishing in
at least one index, the vanishing order of the canonical xi reading is the
indexed infimum of the orders of its normalized toroidal periods. Consequently
the entire zero-divisor function is the pointwise infimum of the period
zero-divisor functions.
-/
theorem toroidal_divisor_gcd {Index : Type*} (rho : ℂ)
    (twist : Index -> ℂ -> ℂ)
    (twistDifferentiable : ∀ index, Differentiable ℂ (twist index))
    (pointwiseNonvanishing : ∀ point, ∃ index, twist index point ≠ 0) :
    analyticOrderAt xiReading rho =
        ⨅ index, analyticOrderAt
          (fun point => xiReading point * twist index point) rho ∧
      (fun point => analyticOrderAt xiReading point) =
        fun point => ⨅ index, analyticOrderAt
          (fun input => xiReading input * twist index input) point := by
  have orderInfimum : ∀ point : ℂ,
      analyticOrderAt xiReading point =
        ⨅ index, analyticOrderAt
          (fun input => xiReading input * twist index input) point := by
    intro point
    have xiAnalytic : AnalyticAt ℂ xiReading point :=
      xi_reading_differentiable.analyticAt point
    have twistAnalytic : ∀ index, AnalyticAt ℂ (twist index) point :=
      fun index => (twistDifferentiable index).analyticAt point
    have productOrder : ∀ index,
        analyticOrderAt
            (fun input => xiReading input * twist index input) point =
          analyticOrderAt xiReading point +
            analyticOrderAt (twist index) point := by
      intro index
      change analyticOrderAt (xiReading * twist index) point = _
      exact analyticOrderAt_mul xiAnalytic (twistAnalytic index)
    apply le_antisymm
    · apply le_iInf
      intro index
      rw [productOrder index]
      exact le_add_right le_rfl
    · obtain ⟨index, twistNonzero⟩ := pointwiseNonvanishing point
      calc
        (⨅ candidate, analyticOrderAt
            (fun input => xiReading input * twist candidate input) point) ≤
            analyticOrderAt
              (fun input => xiReading input * twist index input) point :=
          iInf_le _ index
        _ = analyticOrderAt xiReading point +
              analyticOrderAt (twist index) point := productOrder index
        _ = analyticOrderAt xiReading point + 0 := by
          rw [(twistAnalytic index).analyticOrderAt_eq_zero.mpr twistNonzero]
        _ = analyticOrderAt xiReading point := add_zero _
  exact ⟨orderInfimum rho, funext orderInfimum⟩

example :
    ∃ (twist : Unit -> ℂ -> ℂ),
      (∀ index, Differentiable ℂ (twist index)) ∧
        ∀ point, ∃ index, twist index point ≠ 0 := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro index
    fun_prop
  · intro point
    exact ⟨(), one_ne_zero⟩

example : Nonempty ℂ := ⟨0⟩

#print axioms toroidal_divisor_gcd

end D5.S3.Analytic.Adelic.ToroidalDivisorGcd
