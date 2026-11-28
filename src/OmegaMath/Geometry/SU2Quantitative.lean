import OmegaMath.Geometry.UnitQuaternionSpeed
import Mathlib.Analysis.Normed.Algebra.QuaternionExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Omega original.

Global quadratic product estimates for the round unit-quaternion metric.
-/

noncomputable section
open scoped Quaternion InnerProductSpace Topology
open Set NormedSpace

namespace Omega.Geometry.UnitQuaternion

local notation "U" => unitary ℍ[ℝ]

/-- The actual quaternion exponential, as a unit quaternion. -/
def expUnit (X : ℍ[ℝ]) (hX : X.re = 0) : U :=
  ofUnit (exp X) (by rw [Quaternion.norm_exp, hX]; simp)

@[simp] theorem coe_expUnit (X : ℍ[ℝ]) (hX : X.re = 0) :
    ((expUnit X hX : U) : ℍ[ℝ]) = exp X := rfl

@[simp] theorem expUnit_zero : expUnit 0 rfl = 1 := by
  apply Subtype.ext
  simp

/-- A one-parameter unit-quaternion exponential. -/
def expPath (X : ℍ[ℝ]) (hX : X.re = 0) (t : ℝ) : U :=
  expUnit (t • X) (by simp [hX])

@[simp] theorem coe_expPath (X : ℍ[ℝ]) (hX : X.re = 0) (t : ℝ) :
    ((expPath X hX t : U) : ℍ[ℝ]) = exp (t • X) := rfl

@[simp] theorem expPath_zero (X : ℍ[ℝ]) (hX : X.re = 0) : expPath X hX 0 = 1 := by
  apply Subtype.ext
  simp

@[simp] theorem expPath_one (X : ℍ[ℝ]) (hX : X.re = 0) :
    expPath X hX 1 = expUnit X hX := by
  apply Subtype.ext
  simp

theorem norm_exp_smul (X : ℍ[ℝ]) (hX : X.re = 0) (t : ℝ) :
    ‖exp (t • X)‖ = 1 := by
  rw [Quaternion.norm_exp]
  simp [hX]

theorem exp_smul_mul_neg (X : ℍ[ℝ]) (t : ℝ) :
    exp (t • X) * exp (t • (-X)) = 1 := by
  let : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  rw [smul_neg, ← exp_add_of_commute (Commute.refl (t • X)).neg_right]
  simp

/-- Conjugation by a unit-quaternion exponential moves a quaternion by at most
time times the norm of its commutator with the generator. -/
theorem conjugation_displacement (Y X : ℍ[ℝ]) (hY : Y.re = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • Y) * X * exp (t • (-Y)) - X‖ ≤ t * ‖Y * X - X * Y‖ := by
  let f (s : ℝ) := exp (s • Y) * X * exp (s • (-Y))
  let v (s : ℝ) := exp (s • Y) * (Y * X - X * Y) * exp (s • (-Y))
  have hd (s : ℝ) : HasDerivAt f (v s) s := by
    convert ((hasDerivAt_exp_smul_const Y s).mul_const X).mul
      (hasDerivAt_exp_smul_const' (-Y) s) using 1
    dsimp [v]
    noncomm_ring
  have hv (s : ℝ) : ‖v s‖ ≤ ‖Y * X - X * Y‖ := by
    dsimp [v]
    rw [norm_mul, norm_mul, norm_exp_smul Y hY,
      norm_exp_smul (-Y) (by simp [hY])]
    simp
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment
    (a := 0) (b := t)
    (continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn
    (fun s _ => (hd s).hasDerivWithinAt) (fun s _ => hv s) t ⟨ht, le_rfl⟩
  simpa [f, mul_comm] using h

/-- Global round product estimate with the sharper half-commutator constant. -/
theorem round_exp_mul_le_half_commutator (X Y : ℍ[ℝ])
    (hX : X.re = 0) (hY : Y.re = 0) :
    roundDist (expUnit X hX * expUnit Y hY)
      (expUnit (X + Y) (by simp [hX, hY])) ≤ ‖X * Y - Y * X‖ / 2 := by
  let p (t : ℝ) : U := expPath X hX t * expPath Y hY t *
    expPath (-(X + Y)) (by simp [hX, hY]) t
  let v (t : ℝ) : ℍ[ℝ] := exp (t • X) *
    (X * exp (t • Y) - exp (t • Y) * X) * exp (t • (-(X + Y)))
  have hp (t : ℝ) : HasDerivAt (fun s => (p s : ℍ[ℝ])) (v t) t := by
    convert ((hasDerivAt_exp_smul_const X t).mul
      (hasDerivAt_exp_smul_const Y t)).mul
      (hasDerivAt_exp_smul_const' (-(X + Y)) t) using 1 <;>
      first | rfl | (dsimp [v]; noncomm_ring)
  have hv (t : ℝ) (ht : 0 ≤ t) : ‖v t‖ ≤ t * ‖X * Y - Y * X‖ := by
    dsimp [v]
    rw [norm_mul, norm_mul, norm_exp_smul X hX,
      norm_exp_smul (-(X + Y)) (by simp [hX, hY]), one_mul, mul_one]
    have he : ‖X * exp (t • Y) - exp (t • Y) * X‖ =
        ‖exp (t • Y) * X * exp (t • (-Y)) - X‖ := by
      calc
        _ = ‖(X * exp (t • Y) - exp (t • Y) * X) * exp (t • (-Y))‖ := by
          rw [norm_mul, norm_exp_smul (-Y) (by simp [hY]), mul_one]
        _ = ‖X - exp (t • Y) * X * exp (t • (-Y))‖ := by
          rw [sub_mul, mul_assoc X, exp_smul_mul_neg, mul_one]
        _ = _ := norm_sub_rev _ _
    rw [he]
    simpa only [norm_sub_rev] using conjugation_displacement Y X hY ht
  have hb (t : ℝ) : HasDerivAt (fun s : ℝ => ‖X * Y - Y * X‖ / 2 * s ^ 2)
      (t * ‖X * Y - Y * X‖) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul (‖X * Y - Y * X‖ / 2) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have h := round_le_of_speed_le hp hb (by simp)
    (fun t ht => hv t ht.1) (by norm_num : (0 : ℝ) ≤ 1)
  have hprod : expPath (-(X + Y)) (by simp [hX, hY]) 1 *
      expUnit (X + Y) (by simp [hX, hY]) = 1 := by
    apply Subtype.ext
    change exp (1 • (-(X + Y))) * exp (X + Y) = 1
    simpa using exp_smul_mul_neg (-(X + Y)) 1
  rw [show p 0 = 1 by simp [p], round_comm] at h
  have he := round_mul_right (expUnit (X + Y) (by simp [hX, hY])) (p 1) 1
  rw [one_mul, show p 1 * expUnit (X + Y) (by simp [hX, hY]) =
      expUnit X hX * expUnit Y hY by
        dsimp [p]; rw [mul_assoc, hprod]; simp] at he
  rw [he]
  simpa using h

/-- Global quadratic product estimate, with no smallness hypothesis. -/
theorem round_exp_mul_le (X Y : ℍ[ℝ]) (hX : X.re = 0) (hY : Y.re = 0) :
    roundDist (expUnit X hX * expUnit Y hY)
      (expUnit (X + Y) (by simp [hX, hY])) ≤ ‖X‖ * ‖Y‖ := by
  have hc : ‖X * Y - Y * X‖ ≤ 2 * (‖X‖ * ‖Y‖) := by
    calc
      _ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
      _ = _ := by simp only [norm_mul]; ring
  exact (round_exp_mul_le_half_commutator X Y hX hY).trans (by linarith)

end Omega.Geometry.UnitQuaternion
