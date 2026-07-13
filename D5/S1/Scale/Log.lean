/- GID: D5/S1/Scale/Log
   generality: I
   mirror-B: D5/B/S1/Scale/Log
   mirror-E: none(waiver:algebraically-proved)
   anchors: [gict/v3.6/I.2/definition/1.4]
   digest: Nonzero golden integers have an integer logarithmic scale with exact unit shifts. -/

import D5.S0.Carrier.Units
import D5.S1.Scale.Embedding
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace D5.S1.Scale

open D5.S0.Carrier

/-- The integral logarithmic scale; zero has no scale. -/
noncomputable def logScale (x : GoldenInt) : Option ℤ :=
  if x = 0 then none else some ⌊Real.logb Real.goldenRatio |embedding x|⌋

@[simp] theorem logScale_zero : logScale 0 = none := by simp [logScale]

theorem logScale_ne_zero {x : GoldenInt} (hx : x ≠ 0) :
    logScale x = some ⌊Real.logb Real.goldenRatio |embedding x|⌋ := by
  simp [logScale, hx]

theorem logScale_eq_none_iff (x : GoldenInt) : logScale x = none ↔ x = 0 := by
  simp [logScale]

/-- Multiplication by an integral power of the fundamental unit. -/
def phiUnitZPowMul (n : ℤ) (x : GoldenInt) : GoldenInt :=
  ((phiUnit ^ n : GoldenIntˣ) : GoldenInt) * x

@[simp] theorem embedding_phiUnitZPowMul (n : ℤ) (x : GoldenInt) :
    embedding (phiUnitZPowMul n x) = Real.goldenRatio ^ n * embedding x := by
  have hunit : embedding ((phiUnit ^ n : GoldenIntˣ) : GoldenInt) =
      Real.goldenRatio ^ n := by
    calc
      embedding ((phiUnit ^ n : GoldenIntˣ) : GoldenInt) =
          ((Units.map embedding.toMonoidHom) (phiUnit ^ n) : ℝ) :=
        (Units.coe_map embedding.toMonoidHom (phiUnit ^ n)).symm
      _ = (((Units.map embedding.toMonoidHom phiUnit) ^ n : ℝˣ) : ℝ) := by
        rw [(Units.map embedding.toMonoidHom).map_zpow]
      _ = ((Units.map embedding.toMonoidHom phiUnit : ℝˣ) : ℝ) ^ n :=
        Units.val_zpow_eq_zpow_val _ _
      _ = Real.goldenRatio ^ n := by
        rw [Units.coe_map]
        simp
  rw [phiUnitZPowMul, map_mul, hunit]

theorem phiUnitZPowMul_ne_zero (n : ℤ) {x : GoldenInt} (hx : x ≠ 0) :
    phiUnitZPowMul n x ≠ 0 := by
  intro hzero
  have himage := congr_arg embedding hzero
  rw [embedding_phiUnitZPowMul, map_zero] at himage
  rcases mul_eq_zero.mp himage with hpow | hxemb
  · exact (zpow_ne_zero n Real.goldenRatio_ne_zero) hpow
  · exact hx ((embedding_eq_zero_iff x).mp hxemb)

private theorem logb_goldenRatio_zpow (n : ℤ) :
    Real.logb Real.goldenRatio (Real.goldenRatio ^ n) = n := by
  simp [Real.logb, Real.log_zpow,
    (Real.log_pos Real.one_lt_goldenRatio).ne']

/-- Scaling by `phi^n` translates logarithmic scale by exactly `n`. -/
theorem logScale_phiUnit_zpow_mul (n : ℤ) {x : GoldenInt} (hx : x ≠ 0) :
    logScale (phiUnitZPowMul n x) = (logScale x).map (n + ·) := by
  rw [logScale_ne_zero (phiUnitZPowMul_ne_zero n hx), logScale_ne_zero hx]
  simp only [Option.map_some, embedding_phiUnitZPowMul, abs_mul, abs_zpow,
    abs_of_pos Real.goldenRatio_pos]
  rw [Real.logb_mul (zpow_ne_zero n Real.goldenRatio_ne_zero)
      (abs_ne_zero.mpr ((embedding_eq_zero_iff x).not.mpr hx)),
    logb_goldenRatio_zpow, Int.floor_intCast_add]

end D5.S1.Scale
