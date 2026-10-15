/- Uncompiled exact application for the original EJM delivery.
The full original root is a proof dependency, never a premise. This file
cannot establish an unconditional noise region until every original cut
receipt and the root have passed the kernel. The box is a sufficient region;
no optimal noise threshold is asserted. Keep this bind-only check transient.
-/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierRoot
import D5.S3.Quantum.Entanglement.EJM.EJMAmplitudeProbe

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalPhysicalDelivery

open EJMInflationScore (score)
open EJMCertificateData (F1 F2)
open ElegantJointMeasurementInflation (Node)
open ElegantJointMeasurementSourceNoise
open ElegantJointMeasurementNoiseRobustness
open TriangleIndependentSourceNoise
open scoped BigOperators

-- Original twenty-coordinate score -> actual independent-source Born law ->
-- a positive explicit box. No score-margin or root-acceptance hypothesis.
example :
    0 < (2329145 / 438110171750596608 : ℝ) ∧
      ∀ x y z : ℝ,
        x ∈ Set.Ioc (1 - (2329145 / 438110171750596608 : ℝ)) 1 →
        y ∈ Set.Ioc (1 - (2329145 / 438110171750596608 : ℝ)) 1 →
        z ∈ Set.Ioc (1 - (2329145 / 438110171750596608 : ℝ)) 1 →
        (∀ a b c : Fin 4, 0 ≤ ejmProbability x y z a b c) ∧
        (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          ejmProbability x y z a b c) = 1 ∧
        ¬ TriangleSymmetricLocalRefutation.IsTriangleLocal (ejmProbability x y z) := by
  have margin : ∀ e : Node → Fin 4,
      (6987435 : ℝ) ≤ (score F1 F2 e : ℝ) := by
    intro e
    have h : (6987435 : ℤ) ≤ score F1 F2 e := by
      simpa only [EJMPartialBoundData.scale] using
        PreparedEJMCompleteFrontier.original_score_lower_bound e
    exact_mod_cast h
  have radius : noiseBoxRadius 6987435 53480245575024 =
      (2329145 / 438110171750596608 : ℝ) := by
    norm_num [noiseBoxRadius]
  obtain ⟨positive, excludes⟩ := EJMAmplitudeProbe.original_margin_physical_noise_box
    6987435 (by norm_num) margin
  rw [radius] at positive excludes
  refine ⟨positive, ?_⟩
  intro x y z hx hy hz
  have radius_le_one : (2329145 / 438110171750596608 : ℝ) ≤ 1 := by norm_num
  have hxunit : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hyunit : y ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
  have physical := triangle_noise_distribution
    whiteNoise singlet whiteNoise singlet whiteNoise singlet
    ejm ejm ejm x y z hxunit hyunit hzunit
  exact ⟨physical.1, physical.2.1, excludes x y z hx hy hz⟩

-- The same actual margin also gives the larger sufficient simplex in the
-- three visibility deficits; the source visibilities remain independent.
example (x y z : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (deficits : (1 - x) + (1 - y) + (1 - z) <
      (2329145 / 146036723916865536 : ℝ)) :
    ¬ TriangleSymmetricLocalRefutation.IsTriangleLocal (ejmProbability x y z) := by
  apply positive_score_excludes_physical_noise F1 F2 x y z
    53480245575024 6987435 hx hy hz (by norm_num)
  · intro e
    exact_mod_cast EJMAmplitudeProbe.original_triangle_amplitude e
  · intro e
    have h : (6987435 : ℤ) ≤ score F1 F2 e := by
      simpa only [EJMPartialBoundData.scale] using
        PreparedEJMCompleteFrontier.original_score_lower_bound e
    exact_mod_cast h
  · have multiplied := mul_lt_mul_of_pos_left deficits
      (by norm_num : (0 : ℝ) < 8192 * 53480245575024)
    norm_num at multiplied ⊢
    exact multiplied

#print axioms PreparedEJMCompleteFrontier.original_score_lower_bound
#print axioms EJMAmplitudeProbe.original_triangle_amplitude
#print axioms EJMAmplitudeProbe.original_margin_physical_noise_box

end D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalPhysicalDelivery
