import D5.S3.Quantum.Entanglement.EJM.EJMAmplitudeCertificates
import D5.S3.Quantum.Entanglement.EJM.EJMExactCertificate
import D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseRobustness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMNoiseRegion
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMAmplitudeCertificates (actual_F1_real_abs_bound)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJMInflationScore (score)
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementInflation (Node)
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseRobustness
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise (ejmProbability)

/-! The radius uses the actual coefficient amplitude and the actual global
integer margin. All three visibilities refer to the independent physical
source-noise law; none is replaced by a uniform mixture of output laws. -/

def radius : ℝ := 6987435 / (24576 * 53480245575024)

theorem actual_noise_box :
    0 < radius ∧ ∀ x y z : ℝ,
      x ∈ Set.Ioc (1 - radius) 1 →
      y ∈ Set.Ioc (1 - radius) 1 →
      z ∈ Set.Ioc (1 - radius) 1 →
      ¬ D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation.IsTriangleLocal
        (ejmProbability x y z) := by
  have hmargin : ∀ e : Node → Fin 4,
      (6987435 : ℝ) ≤ (score F1 F2 e : ℝ) := by
    intro e
    exact_mod_cast EJMExactCertificate.score_lower_bound e
  have hbox := positive_score_physical_noise_box F1 F2
    (53480245575024 : ℝ) (6987435 : ℝ) (by norm_num) (by norm_num)
    actual_F1_real_abs_bound hmargin
  have hradius : noiseBoxRadius (6987435 : ℝ) (53480245575024 : ℝ) = radius := by
    norm_num [noiseBoxRadius, radius]
  simpa only [hradius] using hbox

#print axioms actual_noise_box
end D5.S3.Quantum.Entanglement.EJM.EJMNoiseRegion
