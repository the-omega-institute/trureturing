/- Uncompiled exact application for the original EJM delivery.
The full original root is a proof dependency, never a premise. This file
cannot establish an unconditional noise region until every original cut
receipt and the root have passed the kernel. The box is a sufficient region;
no optimal noise threshold is asserted. These consequences stay transient;
the substantive refutation first freezes with the complete original root.
-/
import D5.S3.Quantum.Entanglement.EJM.EJMOriginalPhysicalNonlocality

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
  refine ⟨by norm_num, ?_⟩
  intro x y z hx hy hz
  have radius_le_one : (2329145 / 438110171750596608 : ℝ) ≤ 1 := by norm_num
  have hxunit : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hyunit : y ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
  have physical := triangle_noise_distribution
    whiteNoise singlet whiteNoise singlet whiteNoise singlet
    ejm ejm ejm x y z hxunit hyunit hzunit
  refine ⟨physical.1, physical.2.1, ?_⟩
  intro hlocal
  apply EJMOriginalPhysicalNonlocality.result
  refine ⟨x, y, z, hxunit, hyunit, hzunit, ?_, hlocal⟩
  linarith [hx.1, hy.1, hz.1]

-- The same actual margin also gives the larger sufficient simplex in the
-- three visibility deficits; the source visibilities remain independent.
example (x y z : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (deficits : (1 - x) + (1 - y) + (1 - z) <
      (2329145 / 146036723916865536 : ℝ)) :
    ¬ TriangleSymmetricLocalRefutation.IsTriangleLocal (ejmProbability x y z) := by
  intro hlocal
  exact EJMOriginalPhysicalNonlocality.result ⟨x, y, z, hx, hy, hz, deficits, hlocal⟩

#print axioms PreparedEJMCompleteFrontier.original_score_lower_bound
#print axioms EJMOriginalPhysicalNonlocality.result

end D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalPhysicalDelivery
