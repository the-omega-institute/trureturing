/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite source translation for the native corrected-field detector. -/

import D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import Mathlib.RingTheory.Binomial

/-! Source translation for a signed mode of the original corrected field. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeDetectorTranslation

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField ActualChargedAdjoint
open LatticeHalfFockOriginalTranslation (correctedField_translation_physical)
open LatticeSugawaraConformal (translation)
open Polynomial

/-- The detector at one signed doubled Hahn exponent, linear in its source state. -/
def detector (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (R S : ActualTensor D hu) : Carrier D →ₗ[ℂ] ℂ :=
  ((actualForm D hu).flip S).comp
    ((LinearMap.applyₗ R).comp
      ((LinearMap.proj e).comp (HVertexOperator.coeff.comp (correctedField D hu))))

@[simp] theorem detector_apply (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (R S : ActualTensor D hu) (a : Carrier D) :
    detector D hu e R S a = actualForm D hu ((correctedField D hu a).coeff e R) S := rfl

private theorem detector_step (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (R S : ActualTensor D hu) (a : Carrier D) :
    detector D hu e R S (translation D a) =
      (((e + 2 : ℤ) : ℂ) / 2) * detector D hu (e + 2) R S a := by
  simp only [detector_apply, correctedField_translation_physical, map_smul,
    LinearMap.smul_apply, smul_eq_mul]

private theorem falling_product (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (R S : ActualTensor D hu) (a : Carrier D) (h : ℕ) :
    detector D hu (e - 2 * (h : ℤ)) R S ((translation D ^ h) a) =
      (∏ k ∈ Finset.range h, ((e : ℂ) / 2 - (k : ℂ))) * detector D hu e R S a := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ' (translation D), Module.End.mul_apply, detector_step,
      show e - 2 * ((h + 1 : ℕ) : ℤ) + 2 = e - 2 * (h : ℤ) by omega,
      ih, Finset.prod_range_succ]
    push_cast
    ring

private theorem choose_eq_divided_product (x : ℂ) (h : ℕ) :
    Ring.choose x h = (h.factorial : ℂ)⁻¹ *
      ∏ k ∈ Finset.range h, (x - (k : ℂ)) := by
  rw [Ring.choose_eq_smul, smul_eq_mul]
  congr 1
  calc
    (descPochhammer ℤ h).smeval x = (descPochhammer ℂ h).eval x := by
      rw [descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval,
        descPochhammer_eval_eq_ascPochhammer]
    _ = _ := descPochhammer_eval_eq_prod_range h x

/-- Divided source translation at arbitrary signed modes of the original field. -/
theorem detector_divided_translation (D : LatticeData) (hu : IsUnit D.G.det) (e : ℤ)
    (R S : ActualTensor D hu) (a : Carrier D) (h : ℕ) :
    (h.factorial : ℂ)⁻¹ *
      detector D hu (e - 2 * (h : ℤ)) R S ((translation D ^ h) a) =
        Ring.choose ((e : ℂ) / 2) h * detector D hu e R S a := by
  rw [falling_product, choose_eq_divided_product, mul_assoc]

/-- Divided translation when the two detector weights select the signed mode. -/
theorem selected_detector_divided_translation (D : LatticeData) (hu : IsUnit D.G.det)
    (mR mS F : ℤ) (R S : ActualTensor D hu) (a : Carrier D) (h : ℕ) :
    (h.factorial : ℂ)⁻¹ * detector D hu (mS - mR - 2 * (F + (h : ℤ))) R S
      ((translation D ^ h) a) =
      Ring.choose (((mS : ℂ) - (mR : ℂ)) / 2 - (F : ℂ)) h *
        detector D hu (mS - mR - 2 * F) R S a := by
  rw [show mS - mR - 2 * (F + (h : ℤ)) = (mS - mR - 2 * F) - 2 * (h : ℤ) by omega,
    detector_divided_translation]
  have hx : (((mS - mR - 2 * F : ℤ) : ℂ) / 2) =
      ((mS : ℂ) - (mR : ℂ)) / 2 - (F : ℂ) := by
    push_cast
    ring
  rw [hx]

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeDetectorTranslation
