/- GID: D5/S3/Fourier/CyclicFluxChargeExchange
   generality: G
   mirror-B: D5/B/S3/Fourier/CyclicFluxChargeExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Fourier.ZMod]
   utility: none
   digest: The phase-free cyclic modular S kernel exchanges flux and charge. -/

import Mathlib.Analysis.Fourier.ZMod
import OmegaBuild.Commands

/-! # Phase-free cyclic modular S exchange

The positive transform in the second index converts the normalized cyclic
orbifold S kernel into the signed exchange of the two indices.
-/

compile_only_with_mathlib

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Fourier.CyclicFluxChargeExchange

variable {N : ℕ} [NeZero N]

/-- The unnormalized positive Fourier transform in the second index. -/
noncomputable def chargeTransform (C : ZMod N → ZMod N → ℂ) (r h : ZMod N) : ℂ :=
  ∑ s : ZMod N, ZMod.stdAddChar (s * h) * C r s

/-- The phase-free modular S kernel with normalization `N⁻¹`. -/
noncomputable def modularS (C : ZMod N → ZMod N → ℂ) (r s : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ a : ZMod N, ∑ b : ZMod N, ZMod.stdAddChar (-(r * b + s * a)) * C a b

private theorem modularS_eq_dft (C : ZMod N → ZMod N → ℂ) (r : ZMod N) :
    modularS C r = (N : ℂ)⁻¹ • ZMod.dft (fun a => chargeTransform C a (-r)) := by
  funext s
  simp only [modularS, Pi.smul_apply, ZMod.dft_apply, chargeTransform, smul_eq_mul]
  apply congrArg (fun z : ℂ => (N : ℂ)⁻¹ * z)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hexponent : -(r * b + s * a) = -(a * s) + b * (-r) := by
    calc
      -(r * b + s * a) = -(s * a) + -(r * b) := by rw [neg_add, add_comm]
      _ = -(a * s) + b * (-r) := by rw [mul_comm s a, mul_neg, mul_comm r b]
  rw [hexponent, AddChar.map_add_eq_mul, mul_assoc]

/-- In charge coordinates the explicit modular S kernel sends `(r, h)` to `(h, -r)`. -/
theorem chargeTransform_modularS (C : ZMod N → ZMod N → ℂ) (r h : ZMod N) :
    chargeTransform (modularS C) r h = chargeTransform C h (-r) := by
  calc
    chargeTransform (modularS C) r h = ZMod.dft (modularS C r) (-h) := by
      simp only [chargeTransform, ZMod.dft_apply, mul_neg, neg_neg, smul_eq_mul]
    _ = chargeTransform C h (-r) := by
      rw [modularS_eq_dft, ZMod.dft_const_smul, ZMod.dft_dft]
      simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ (NeZero.ne (N : ℂ)), one_smul, neg_neg]

end D5.S3.Fourier.CyclicFluxChargeExchange
