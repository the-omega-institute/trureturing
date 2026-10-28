/- GID: D5/S3/Observer/MetricGeometry/PermanentFinitePredictionObstruction
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/PermanentFinitePredictionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: No finite autonomous orbit maintains a fixed subunit error forever on an irrational rotation. -/

import D5.S3.Observer.MetricGeometry.ArithmeticHorizon
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-! A finite autonomous predictor cannot maintain a fixed subunit error forever on an irrational rotation. -/

namespace D5.S3.Observer.MetricGeometry.PermanentFinitePredictionObstruction

open D5.S3.Observer.MetricGeometry.ArithmeticHorizon

/-- A finite autonomous predictor cannot satisfy a uniform subunit error bound at
all times along an irrational circle rotation. -/
theorem no_permanent_finite_prediction
    {S : Type*} [Fintype S]
    (G : S → S) (h : S → ℂ) (initial : S)
    (x : AddCircle (1 : ℝ)) (α ε : ℝ)
    (hα : Irrational α) (hε : 0 < ε) (hεh : ε < 1 / 2)
    (accuracy : ∀ n : ℕ,
      ‖h ((G^[n]) initial) - ((x + n • (α : AddCircle (1 : ℝ))).toCircle : ℂ)‖ ≤ ε) :
    False := by
  let B : ℝ := Fintype.card S +
    (Real.arcsin ε / Real.pi) * Psi α (Fintype.card S)
  obtain ⟨H, hH⟩ := exists_nat_gt B
  have hbound := finite_predictor_horizon G h initial x α ε hα hε hεh H (fun n _ => accuracy n)
  have hHB : (B : ℝ) < H := by
    simpa [Nat.cast_add, B] using hH
  exact (not_lt_of_ge (le_of_lt hHB)) hbound

end D5.S3.Observer.MetricGeometry.PermanentFinitePredictionObstruction
