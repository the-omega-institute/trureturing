/- GID: D5/S3/Analytic/Dilation/GoldenUnitZetaRegulatorCircle
   generality: I
   mirror-B: D5/B/S3/Analytic/Dilation/GoldenUnitZetaRegulatorCircle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden-unit zeta descends through its regulator-period quotient. -/

import D5.S3.Analytic.Dilation.GoldenUnitZetaPeriodicity
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Topology.Instances.AddCircle.Defs

namespace D5.S3.Analytic.Dilation.GoldenUnitZetaRegulatorCircle

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped goldenRatio

noncomputable section

-- The coefficient model `a + b * phi` of the exact ring `Z[phi]`.
abbrev GoldenInteger := Int × Int

-- The expanding real embedding of `Z[phi]`.
def sigmaPlus (alpha : GoldenInteger) : Real :=
  (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenRatio

-- The conjugate real embedding of `Z[phi]`.
def sigmaMinus (alpha : GoldenInteger) : Real :=
  (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenConj

-- The anisotropic quadratic form along the logarithmic unit flow.
def anisotropicForm (eta : Real) (alpha : GoldenInteger) : Real :=
  Real.exp eta * sigmaPlus alpha ^ 2 +
    Real.exp (-eta) * sigmaMinus alpha ^ 2

-- The exact nonzero coefficient lattice of `Z[phi]`.
abbrev NonzeroGoldenInteger := {alpha : GoldenInteger // alpha ≠ 0}

-- The golden-unit lattice zeta from the source definition.
def goldenUnitZeta (s : Complex) (eta : Real) : Complex :=
  ∑' alpha : NonzeroGoldenInteger,
    (anisotropicForm eta alpha : Complex) ^ (-s)

-- Twice the logarithmic regulator of the fundamental golden unit.
def regulatorPeriod : Real := 2 * Real.log Real.goldenRatio

-- The source quotient `R / (2 log(phi)) Z`.
abbrev GoldenRegulatorCircle := AddCircle regulatorPeriod

-- The already-frozen lattice reindexing theorem, exposed as periodicity.
theorem goldenUnitZeta_periodic (s : Complex) :
    Function.Periodic (goldenUnitZeta s) regulatorPeriod := by
  intro eta
  simpa [goldenUnitZeta, anisotropicForm, sigmaPlus, sigmaMinus,
    regulatorPeriod, GoldenInteger, NonzeroGoldenInteger] using
    (D5.S3.Analytic.Dilation.GoldenUnitZetaPeriodicity.golden_unit_zeta_periodicity
      s eta)

-- The literal regulator period is nonzero, so its quotient is not the
-- zero-period collapse.
theorem regulatorPeriod_pos : 0 < regulatorPeriod := by
  simp only [regulatorPeriod]
  exact mul_pos (by norm_num) (Real.log_pos Real.one_lt_goldenRatio)

-- The zeta observable on the regulator circle, obtained by Mathlib's
-- quotient lift of a periodic function.
def goldenUnitZetaOnRegulatorCircle (s : Complex) :
    GoldenRegulatorCircle → Complex :=
  (goldenUnitZeta_periodic s).lift

-- The regulator-period equality and the resulting quotient-circle carrier.
-- The first conjunct is the source theorem's first boxed assertion. The second
-- states that the circle observable pulls back to the source real-line formula,
-- so the parameter is genuinely carried by `R / (2 log(phi)) Z`.
theorem golden_unit_zeta_regulator_circle :
    (∀ (s : Complex) (eta : Real),
      goldenUnitZeta s (eta + 2 * Real.log Real.goldenRatio) =
        goldenUnitZeta s eta) ∧
    (∀ (s : Complex) (eta : Real),
      goldenUnitZetaOnRegulatorCircle s (eta : GoldenRegulatorCircle) =
        goldenUnitZeta s eta) := by
  constructor
  · intro s eta
    simpa only [regulatorPeriod] using goldenUnitZeta_periodic s eta
  · intro s eta
    exact Function.Periodic.lift_coe (goldenUnitZeta_periodic s) eta

-- Reverse probe for CAS assertion A1: the public theorem recovers the
-- literal regulator-period equality.
example (s : Complex) (eta : Real) :
    goldenUnitZeta s (eta + 2 * Real.log Real.goldenRatio) =
      goldenUnitZeta s eta :=
  golden_unit_zeta_regulator_circle.1 s eta

-- Reverse probe for CAS assertion A2: the public theorem recovers the
-- pullback identity from the regulator-circle carrier.
example (s : Complex) (eta : Real) :
    goldenUnitZetaOnRegulatorCircle s (eta : GoldenRegulatorCircle) =
      goldenUnitZeta s eta :=
  golden_unit_zeta_regulator_circle.2 s eta

-- Collapse probe for CAS assertion A2: the literal regulator circle has two
-- distinguishable points and therefore cannot be replaced by `Unit`.
example :
    (0 : GoldenRegulatorCircle) ≠
      ((regulatorPeriod / 2 : Real) : GoldenRegulatorCircle) := by
  intro h
  have hhalf :
      ((regulatorPeriod / 2 : Real) : GoldenRegulatorCircle) = 0 := h.symm
  obtain ⟨n, hn⟩ :=
    (AddCircle.coe_eq_zero_iff regulatorPeriod).mp hhalf
  have hn' :
      (n : Real) * regulatorPeriod = regulatorPeriod / 2 := by
    simpa [zsmul_eq_mul] using hn
  have hcast : (n : Real) * 2 = 1 := by
    nlinarith [regulatorPeriod_pos]
  have hint : n * 2 = 1 := by
    exact_mod_cast hcast
  omega

#print axioms golden_unit_zeta_regulator_circle

end

end D5.S3.Analytic.Dilation.GoldenUnitZetaRegulatorCircle
