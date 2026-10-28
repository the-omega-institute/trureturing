/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiTransfer
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: The four-state Andrasfai transfer traces satisfy the full corrected rational series identity. -/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiTransfer

open Matrix PowerSeries
open scoped Matrix

/-- Labelled-edge multiplicities of the partial four-state automaton. -/
def transfer : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1,1,0,0; 1,0,1,0; 0,0,0,1; 0,2,0,0]

private def block : Matrix (Fin 4) (Fin 4) ℚ :=
  !![3,2,1,1; 2,3,1,0; 2,0,2,0; 2,2,0,2]

private theorem block_eq : block = transfer^3 := by
  decide +kernel

private theorem block_annihilator :
    block^4 = (10 : ℚ) • block^3 - (29 : ℚ) • block^2 +
      (32 : ℚ) • block - (8 : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
  decide +kernel

private def b (j : ℕ) : ℚ := Matrix.trace (transfer^2 * block^j)

private theorem b_eq_trace (j : ℕ) : b j = Matrix.trace (transfer^(3*j+2)) := by
  unfold b
  rw [block_eq, ← pow_mul, ← pow_add]
  congr 2
  omega

private theorem b_initial : b 0 = 3 ∧ b 1 = 21 ∧ b 2 = 127 ∧ b 3 = 749 := by
  decide +kernel

private theorem b_recurrence (j : ℕ) :
    b (j+4) = 10*b (j+3) - 29*b (j+2) + 32*b (j+1) - 8*b j := by
  have h := congrArg (fun A => Matrix.trace ((transfer^2 * block^j) * A))
    block_annihilator
  simpa [b, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    Matrix.mul_assoc, ← pow_add, mul_one, pow_one, pow_succ] using h

/-- Coefficient j+1 is the trace for the original graph index j+1, before
its exceptional first coefficient is corrected. Constant coefficient is zero. -/
noncomputable def traceSeries : PowerSeries ℚ := X * PowerSeries.mk (fun j => Matrix.trace (transfer^(3*j+2)))

/-- The full denominator has constant coefficient one. -/
noncomputable def denominator : PowerSeries ℚ := 1-10*X+29*X^2-32*X^3+8*X^4

private theorem series_equation :
    denominator * PowerSeries.mk b = 3-9*X+4*X^2-8*X^3 := by
  ext n
  rw [show denominator * PowerSeries.mk b =
    PowerSeries.mk b - 10*(X*PowerSeries.mk b) +
      29*(X^2*PowerSeries.mk b) - 32*(X^3*PowerSeries.mk b) +
      8*(X^4*PowerSeries.mk b) by unfold denominator; ring]
  have hc (i : ℕ) : coeff i (3 : PowerSeries ℚ) = if i=0 then 3 else 0 := by
    have he : (3 : PowerSeries ℚ) = C 3 := (map_ofNat C 3).symm
    rw [he, coeff_C]
  rcases n with _ | _ | _ | _ | n
  · simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mk, hc,
      coeff_zero_X_mul, coeff_X_pow_mul', coeff_X, coeff_X_pow]
    norm_num [b_initial.1]
  · norm_num [hc, coeff_X, coeff_X_pow_mul', coeff_succ_X_mul,
      b_initial.1, b_initial.2.1]
  · norm_num [hc, coeff_X, coeff_X_pow_mul', coeff_succ_X_mul,
      b_initial.1, b_initial.2.1, b_initial.2.2.1]
  · norm_num [hc, coeff_X, coeff_X_pow_mul', coeff_succ_X_mul,
      b_initial.1, b_initial.2.1, b_initial.2.2.1, b_initial.2.2.2]
  · have h2 : 2 ≤ n+4 := by omega
    have h3 : 3 ≤ n+4 := by omega
    have h4 : 4 ≤ n+4 := by omega
    simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mk,
      coeff_succ_X_mul, coeff_X_pow_mul', ite_eq_left h2, ite_eq_left h3, ite_eq_left h4,
      hc, coeff_X, coeff_X_pow,
      show n+4 ≠ 0 by omega, show n+4 ≠ 1 by omega,
      show n+4 ≠ 2 by omega, show n+4 ≠ 3 by omega,
      ite_false, mul_zero, sub_zero, add_zero,
      show n+4-2 = n+2 by omega, show n+4-3 = n+1 by omega,
      show n+4-4 = n by omega]
    rw [b_recurrence]
    ring

/-- The complete trace generating series, including its index-one correction.
This theorem makes no identification of a graph subset count with a trace. -/
theorem corrected_trace_series :
    traceSeries + X =
      (X*(4-19*X+33*X^2-40*X^3+8*X^4)) * denominator⁻¹ := by
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp [denominator])).mpr
  dsimp [traceSeries]
  have he : PowerSeries.mk (fun j => Matrix.trace (transfer^(3*j+2))) =
      PowerSeries.mk b := by
    ext j
    simp only [coeff_mk, b_eq_trace]
  rw [he]
  calc
    (X * PowerSeries.mk b + X) * denominator =
      X*(denominator*PowerSeries.mk b)+X*denominator := by ring
    _ = X*(3-9*X+4*X^2-8*X^3)+X*denominator := by rw [series_equation]
    _ = X*(4-19*X+33*X^2-40*X^3+8*X^4) := by unfold denominator; ring

end D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiTransfer
