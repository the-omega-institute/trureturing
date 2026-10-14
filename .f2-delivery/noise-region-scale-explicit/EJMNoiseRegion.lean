/- GID: D5/S3/Quantum/Entanglement/EJM/EJMNoiseRegion
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMNoiseRegion
   mirror-E: none(waiver:actual-independent-quantum-source-noise-region)
   anchors: []
   utility: none
   digest: The earned exact EJM margin and coefficient amplitude give a strictly nonlocal box for the original independent quantum-source Born law. -/

/-
admission_basis: escape-witness
actual_noise_box: proof_shape: content after inlining the same-delivery
actual certificate, coefficient-tree soundness and physical-noise perturbation
bound. The real normalization of the explicit radius supplies no separate
escape and is consumed by the full source-law nonlocality conclusion.
Every margin, amplitude and physical-source hypothesis is discharged by
canonical proofs in this delivery. There is no external producer acceptance
premise, uniform-output noise substitution or asserted optimal threshold.
The exact global check and the complete actual local receipts remain pending
until their real kernel build succeeds; this source is not a delivered claim
before that acceptance. Four-slot source registration remains unfinished
under issue #16309.
-/

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

def radius : ℝ := (scale : ℝ) / (24576 * 53480245575024)

theorem actual_noise_box :
    0 < radius ∧ ∀ x y z : ℝ,
      x ∈ Set.Ioc (1 - radius) 1 →
      y ∈ Set.Ioc (1 - radius) 1 →
      z ∈ Set.Ioc (1 - radius) 1 →
      ¬ D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation.IsTriangleLocal
        (ejmProbability x y z) := by
  have hmargin : ∀ e : Node → Fin 4,
      (scale : ℝ) ≤ (score F1 F2 e : ℝ) := by
    intro e
    exact_mod_cast EJMExactCertificate.score_lower_bound e
  have hbox := positive_score_physical_noise_box F1 F2
    (53480245575024 : ℝ) (scale : ℝ) (by norm_num) (by norm_num [scale])
    actual_F1_real_abs_bound hmargin
  have hradius : noiseBoxRadius (scale : ℝ) (53480245575024 : ℝ) = radius := by
    norm_num [noiseBoxRadius, radius, scale]
  simpa only [hradius] using hbox

#print axioms actual_noise_box
end D5.S3.Quantum.Entanglement.EJM.EJMNoiseRegion
