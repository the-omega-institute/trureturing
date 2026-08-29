/- GID: D5/S3/Weil/Budget/PositiveCayleyScaleTransport
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/PositiveCayleyScaleTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Resolvent-weighted Cayley spectral measures transport positively across scales. -/

import D5.S3.Weil.Budget.CayleyScaleChange
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

/- Library-search audit trail (2026-08-29):
   * D5 and current-origin searches found no positive Cayley scale-transport law.
   * Body-shape searches for resolvent `withDensity`, Cayley `Measure.map`, and
     the explicit norm-square transport weight found no reusable D5 primitive.
   * Pinned Mathlib supplies `Measure.map_map`, `Measure.withDensity_mul`, and
     `MeasureTheory.setLIntegral_map`, but no exact scale-transport identity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace D5.S3.Weil.Budget.PositiveCayleyScaleTransport

open CayleyScaleChange

/-- The source measure weighted by the resolvent at a real scale. -/
noncomputable def resolventWeightedMeasure
    (source : Measure Real) (scale : Real) : Measure Real :=
  source.withDensity fun spectral =>
    ENNReal.ofReal ((spectral ^ 2 + scale ^ 2)⁻¹)

/-- The resolvent-weighted source measure in its scale-dependent Cayley coordinate. -/
noncomputable def cayleySpectralMeasure
    (source : Measure Real) (scale : Real) : Measure Complex :=
  Measure.map (cayleyCoordinate scale) (resolventWeightedMeasure source scale)

/-- The positive Radon--Nikodym weight induced by changing Cayley scale. -/
noncomputable def scaleTransportWeight
    (a b : Real) (z : Complex) : Real :=
  let r := scaleChangeParameter a b
  (1 + r) ^ 2 / Complex.normSq (1 + (r : Complex) * z)

private theorem measurable_cayleyCoordinate (scale : Real) :
    Measurable (cayleyCoordinate scale) := by
  unfold cayleyCoordinate
  fun_prop

private theorem measurable_realDiskAutomorphism (r : Real) :
    Measurable (realDiskAutomorphism r) := by
  unfold realDiskAutomorphism
  fun_prop

private theorem measurable_resolvent_density (scale : Real) :
    Measurable fun spectral : Real =>
      ENNReal.ofReal ((spectral ^ 2 + scale ^ 2)⁻¹) := by
  fun_prop

private theorem measurable_scaleTransport_density (a b : Real) :
    Measurable fun z : Complex => ENNReal.ofReal (scaleTransportWeight a b z) := by
  unfold scaleTransportWeight
  fun_prop

private theorem map_withDensity_eq
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (mu : Measure alpha) (f : alpha -> beta) (g : beta -> ENNReal)
    (hf : Measurable f) (hg : Measurable g) :
    (Measure.map f mu).withDensity g =
      Measure.map f (mu.withDensity (g ∘ f)) := by
  ext s hs
  rw [withDensity_apply _ hs, MeasureTheory.setLIntegral_map hs hg hf]
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs)]
  rfl

private theorem transport_weight_at_cayley
    (a b spectral : Real) (ha : 0 < a) (hb : 0 < b) :
    scaleTransportWeight a b (cayleyCoordinate a spectral) =
      (spectral ^ 2 + a ^ 2) / (spectral ^ 2 + b ^ 2) := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hsa : spectral ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hsb : spectral ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hcomplex :
      1 + ((scaleChangeParameter a b : Real) : Complex) *
          cayleyCoordinate a spectral =
        (((2 * a / (a + b) : Real) : Complex)) *
          (((spectral : Complex) - Complex.I * (b : Complex)) /
            ((spectral : Complex) - Complex.I * (a : Complex))) := by
    apply Complex.ext <;>
      simp [scaleChangeParameter, cayleyCoordinate, Complex.div_re,
        Complex.div_im, Complex.normSq_apply] <;>
      field_simp [hab, hsa] <;> ring
  unfold scaleTransportWeight
  dsimp only
  rw [hcomplex, Complex.normSq_mul, Complex.normSq_div]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  norm_num
  unfold scaleChangeParameter
  field_simp [hab, hsa, hsb, ne_of_gt ha]
  ring

private theorem transport_density_identity
    (a b spectral : Real) (ha : 0 < a) (hb : 0 < b) :
    ENNReal.ofReal (scaleTransportWeight a b (cayleyCoordinate a spectral)) *
        ENNReal.ofReal ((spectral ^ 2 + a ^ 2)⁻¹) =
      ENNReal.ofReal ((spectral ^ 2 + b ^ 2)⁻¹) := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hsa : spectral ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hsb : spectral ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hq : 0 ≤ scaleTransportWeight a b (cayleyCoordinate a spectral) := by
    unfold scaleTransportWeight
    exact div_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  have hda : 0 ≤ (spectral ^ 2 + a ^ 2)⁻¹ := by positivity
  have hdb : 0 ≤ (spectral ^ 2 + b ^ 2)⁻¹ := by positivity
  rw [← ENNReal.ofReal_mul hq]
  apply (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg hq hda) hdb).2
  rw [transport_weight_at_cayley a b spectral ha hb]
  field_simp [hab, hsa, hsb]

/-- Positive Cayley scale transport: the scale-`b` spectral measure is the
pushforward of the scale-`a` measure after multiplication by the explicit
positive transport density. -/
theorem positive_cayley_scale_transport
    (source : Measure Real) (a b : Real) (ha : 0 < a) (hb : 0 < b) :
    cayleySpectralMeasure source b =
      Measure.map
        (realDiskAutomorphism (scaleChangeParameter a b))
        ((cayleySpectralMeasure source a).withDensity fun z =>
          ENNReal.ofReal (scaleTransportWeight a b z)) := by
  let densityA : Real -> ENNReal := fun spectral =>
    ENNReal.ofReal ((spectral ^ 2 + a ^ 2)⁻¹)
  let densityB : Real -> ENNReal := fun spectral =>
    ENNReal.ofReal ((spectral ^ 2 + b ^ 2)⁻¹)
  let transportDensity : Complex -> ENNReal := fun z =>
    ENNReal.ofReal (scaleTransportWeight a b z)
  have hcA := measurable_cayleyCoordinate a
  have hPhi := measurable_realDiskAutomorphism (scaleChangeParameter a b)
  have hdA : Measurable densityA := measurable_resolvent_density a
  have hq : Measurable transportDensity := measurable_scaleTransport_density a b
  have hdensity : densityA * (transportDensity ∘ cayleyCoordinate a) = densityB := by
    funext spectral
    simpa only [Pi.mul_apply, Function.comp_apply, mul_comm] using
      transport_density_identity a b spectral ha hb
  unfold cayleySpectralMeasure resolventWeightedMeasure
  change Measure.map (cayleyCoordinate b) (source.withDensity densityB) =
    Measure.map (realDiskAutomorphism (scaleChangeParameter a b))
      ((Measure.map (cayleyCoordinate a) (source.withDensity densityA)).withDensity
        transportDensity)
  rw [map_withDensity_eq (source.withDensity densityA) _ _ hcA hq]
  rw [← withDensity_mul source hdA (hq.comp hcA), hdensity]
  rw [Measure.map_map hPhi hcA]
  apply congrArg (fun f => Measure.map f (source.withDensity densityB))
  funext spectral
  simpa only [Function.comp_apply] using cayley_scale_change a b spectral ha hb

#print axioms positive_cayley_scale_transport

end D5.S3.Weil.Budget.PositiveCayleyScaleTransport
