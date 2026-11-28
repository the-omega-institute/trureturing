/- GID: D5/S3/Analysis/InverseTimeRescaling
   generality: G
   mirror-B: none(waiver:covered-by-conformal-maxwell-selection4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Removing the first derivative from a weighted mode equation in inverse-time coordinates. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Omega original.

Removing the first derivative from a weighted mode equation in inverse-time coordinates.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology

namespace Omega

/-- The positive inverse-time scale on the negative half-line when `H > 0`. -/
noncomputable def inverseTimeScale (H t : ℝ) : ℝ := -1 / (H * t)

theorem inverseTimeScale_pos {H t : ℝ} (hH : 0 < H) (ht : t < 0) :
    0 < inverseTimeScale H t :=
  div_pos_of_neg_of_neg (by norm_num) (mul_neg_of_pos_of_neg hH ht)

private theorem scalePower_derivative {H b t : ℝ} (hH : 0 < H) (ht : t < 0) :
    HasDerivAt (fun s => inverseTimeScale H s ^ b)
      (-b / t * inverseTimeScale H t ^ b) t := by
  have hden : H * t ≠ 0 := mul_ne_zero hH.ne' ht.ne
  have hscale : HasDerivAt (inverseTimeScale H) (-inverseTimeScale H t / t) t := by
    have hd := (hasDerivAt_const t (-1 : ℝ)).div
      ((hasDerivAt_id t).const_mul H) hden
    convert hd using 1 <;> try rfl
    simp only [inverseTimeScale, id_eq]
    field_simp [hH.ne', ht.ne]
    ring
  have hd := hscale.rpow_const (p := b) (Or.inl (inverseTimeScale_pos hH ht).ne')
  have hp : inverseTimeScale H t * inverseTimeScale H t ^ (b - 1) =
      inverseTimeScale H t ^ b := by
    have he := Real.rpow_add (inverseTimeScale_pos hH ht) 1 (b - 1)
    rw [show 1 + (b - 1) = b by ring, Real.rpow_one] at he
    exact he.symm
  convert hd using 1
  calc
    _ = -(b / t) * (inverseTimeScale H t * inverseTimeScale H t ^ (b - 1)) := by rw [hp]; ring
    _ = _ := by ring

/-- The exact weighted differential identity for an arbitrary real exponent and potential.
The mode is differentiable at negative times and its derivative is differentiable at `t`. -/
theorem inverseTime_rescaled_ode {H t : ℝ} (hH : 0 < H) (ht : t < 0)
    (b : ℝ) (A Q : ℝ → ℝ)
    (hA : ∀ s < 0, DifferentiableAt ℝ A s)
    (hA' : DifferentiableAt ℝ (deriv A) t) :
    let w := fun s => inverseTimeScale H s ^ b
    let v := fun s => w s * A s
    deriv (fun s => w s ^ 2 * deriv A s) t + w t ^ 2 * Q t * A t =
      w t * (deriv (deriv v) t + (Q t - b * (b + 1) / t ^ 2) * v t) := by
  dsimp only
  let w : ℝ → ℝ := fun s => inverseTimeScale H s ^ b
  let r : ℝ → ℝ := fun s => -b / s
  have hw {s : ℝ} (hs : s < 0) : HasDerivAt w (r s * w s) s :=
    scalePower_derivative hH hs
  have hr : HasDerivAt r (b / t ^ 2) t := by
    have hfun : ((fun _ : ℝ => -b) / id) = r := rfl
    rw [← hfun]
    simpa only [id_eq, mul_one, zero_mul, zero_sub, neg_neg] using
      (hasDerivAt_const t (-b)).div (hasDerivAt_id t) ht.ne
  have hv' : deriv (fun s => w s * A s) =ᶠ[𝓝 t]
      (fun s => (r s * w s) * A s + w s * deriv A s) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact ((hw hs).mul (hA s hs).hasDerivAt).deriv
  have hsecond := (((hr.mul (hw ht)).mul (hA t ht).hasDerivAt).add
    ((hw ht).mul hA'.hasDerivAt)).congr_of_eventuallyEq hv'
  have hflux := (((hw ht).pow 2).mul hA'.hasDerivAt).deriv
  change deriv (fun s => w s ^ 2 * deriv A s) t + w t ^ 2 * Q t * A t =
      w t * (deriv (deriv (fun s => w s * A s)) t +
        (Q t - b * (b + 1) / t ^ 2) * (w t * A t))
  change deriv (fun s => w s ^ 2 * deriv A s) t = _ at hflux
  rw [hflux, hsecond.deriv]
  simp only [r, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, show 2 - 1 = 1 by decide, pow_one]
  field_simp [ht.ne]
  ring

end Omega
