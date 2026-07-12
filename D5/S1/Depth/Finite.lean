/- GID: D5/S1/Depth/Finite
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:definition-and-structural-properties-only)
   anchors: [GICT-v3.6-I.2-definition-1.4]
   digest: Depth combines logarithmic scale, Zeckendorf support, and finite phase resolution. -/

import D5.S1.Digit.Addition
import D5.S1.Phase.Basic
import D5.S1.Scale.Log
import Mathlib.Data.PNat.Basic

namespace D5.S1.Depth

open D5.S0.Carrier D5.S0.Conventions
open D5.S1.Digit D5.S1.Phase D5.S1.Scale

/-- The A-axis coordinate on positive natural points. -/
noncomputable def scaleCoordinate (n : ℕ+) : ℤ :=
  ⌊Real.logb Real.goldenRatio |embedding ((n : ℕ) : GoldenInt)|⌋

/-- Positive natural points remain nonzero in the golden-integer carrier. -/
theorem goldenInt_natCast_ne_zero (n : ℕ+) : ((n : ℕ) : GoldenInt) ≠ 0 := by
  intro h
  have ha : ((n : ℕ) : ℤ) = 0 := by
    simpa using congrArg GoldenInt.a h
  exact (Int.ofNat_ne_zero.mpr n.ne_zero) ha

/-- The A-axis component is exactly the value carried by `logScale`. -/
@[simp] theorem logScale_natCast (n : ℕ+) :
    logScale ((n : ℕ) : GoldenInt) = some (scaleCoordinate n) := by
  simpa [scaleCoordinate] using logScale_ne_zero (goldenInt_natCast_ne_zero n)

/-- The canonical raw Zeckendorf coordinate of a natural point. -/
noncomputable def digitCoordinate (n : ℕ) : CanonicalRawDigits :=
  ⟨toRaw (Z n), canonicalRaw_toRaw (Z n)⟩

@[simp] theorem digitCoordinate_val (n : ℕ) :
    (digitCoordinate n).1 = toRaw (Z n) := rfl

/-- `|Z n|`: the number of occupied positions in the canonical raw support. -/
noncomputable def digitLength (n : ℕ) : ℕ :=
  (digitCoordinate n).1.support.card

/-- The G-axis coordinate inherited from `Phase.Basic`. -/
noncomputable def phaseCoordinate (n : ℕ) : AddCircle (1 : ℝ) :=
  goldenPhase (n : ℤ)

@[simp] theorem phaseCoordinate_eq_goldenPhase (n : ℕ) :
    phaseCoordinate n = goldenPhase (n : ℤ) := rfl

/-- The `[0, 1)` representative of a unit-circle phase. -/
noncomputable def phaseRepresentative (g : AddCircle (1 : ℝ)) : ℝ :=
  AddCircle.equivIco (1 : ℝ) 0 g

theorem phaseRepresentative_nonneg (g : AddCircle (1 : ℝ)) :
    0 ≤ phaseRepresentative g := by
  simpa [phaseRepresentative] using
    (AddCircle.equivIco (1 : ℝ) 0 g).property.1

theorem phaseRepresentative_lt_one (g : AddCircle (1 : ℝ)) :
    phaseRepresentative g < 1 := by
  simpa [phaseRepresentative] using
    (AddCircle.equivIco (1 : ℝ) 0 g).property.2

/-- `H_Q`: quantize a circle phase into one of `Q` half-open buckets. -/
noncomputable def finitePhase (Q : ℕ) (hQ : 0 < Q)
    (g : AddCircle (1 : ℝ)) : Fin Q :=
  ⟨⌊(Q : ℝ) * phaseRepresentative g⌋₊, by
    apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg Q)
      (phaseRepresentative_nonneg g))).2
    simpa using mul_lt_mul_of_pos_left (phaseRepresentative_lt_one g)
      (Nat.cast_pos.2 hQ)⟩

@[simp] theorem finitePhase_val (Q : ℕ) (hQ : 0 < Q)
    (g : AddCircle (1 : ℝ)) :
    (finitePhase Q hQ g : ℕ) = ⌊(Q : ℝ) * phaseRepresentative g⌋₊ := rfl

/-- The offset is admissible when the theoretical W index `A(n) + q0` is nonnegative. -/
def ResolutionAdmissible (q0 : ℤ) (n : ℕ+) : Prop :=
  0 ≤ scaleCoordinate n + q0

/-- The natural W index used by `Q(n) = W_(A(n)+q0)`. -/
noncomputable def resolutionIndex (q0 : ℤ) (n : ℕ+) : ℕ :=
  (scaleCoordinate n + q0).toNat

/-- Under the explicit admissibility premise, no information is lost by `Int.toNat`. -/
theorem resolution_index_spec {q0 : ℤ} {n : ℕ+}
    (h : ResolutionAdmissible q0 n) :
    (resolutionIndex q0 n : ℤ) = scaleCoordinate n + q0 := by
  exact Int.toNat_of_nonneg h

/-- The finite phase resolution `Q(n) = W_(A(n)+q0)`. -/
noncomputable def phaseResolution (q0 : ℤ) (n : ℕ+) : ℕ :=
  wValue (resolutionIndex q0 n)

theorem phaseResolution_pos (q0 : ℤ) (n : ℕ+) :
    0 < phaseResolution q0 n := by
  rw [phaseResolution, wValue]
  exact Nat.fib_pos.2 (by omega)

/-- The dependent triple `(A n, |Z n|, H_Q (G n))`; its third type has exactly `Q(n)` values. -/
abbrev DepthValue (q0 : ℤ) (n : ℕ+) :=
  ℤ × ℕ × Fin (phaseResolution q0 n)

/-- GICT Definition 1.4, restricted to positive natural points and finite W resolution. -/
noncomputable def depth (q0 : ℤ) (n : ℕ+) : DepthValue q0 n :=
  (scaleCoordinate n, digitLength n,
    finitePhase (phaseResolution q0 n) (phaseResolution_pos q0 n)
      (phaseCoordinate n))

@[simp] theorem depth_scale (q0 : ℤ) (n : ℕ+) :
    (depth q0 n).1 = scaleCoordinate n := rfl

@[simp] theorem depth_digit_length (q0 : ℤ) (n : ℕ+) :
    (depth q0 n).2.1 = (toRaw (Z n)).support.card := rfl

@[simp] theorem depth_phase (q0 : ℤ) (n : ℕ+) :
    (depth q0 n).2.2 =
      finitePhase (phaseResolution q0 n) (phaseResolution_pos q0 n)
        (goldenPhase (n : ℤ)) := rfl

/-- The phase component is structurally confined to the declared finite resolution. -/
theorem depth_phase_lt_resolution (q0 : ℤ) (n : ℕ+) :
    (depth q0 n).2.2.val < phaseResolution q0 n :=
  (depth q0 n).2.2.isLt

/-- TASK D5-T0020 | 难度:4 | 依赖:欠(GICT-depth-metric-structure) | 尝试:0
    提示:Choose a fiber distance, then prove separation and a triangle variant at Lean L2.
    尸检:none; GICT v3.6 line 234 explicitly lists separation and triangle variants as open. -/
def depthMetricL2Open : Unit := ()

end D5.S1.Depth
