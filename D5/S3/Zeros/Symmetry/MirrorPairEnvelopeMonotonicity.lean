/- GID: D5/S3/Zeros/Symmetry/MirrorPairEnvelopeMonotonicity
   generality: G
   mirror-B: D5/B/S3/Zeros/Symmetry/MirrorPairEnvelopeMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The positive-slope mirror-pair envelope is strictly increasing on nonnegative inputs. -/

/- Library-search audit trail (2026-08-14):
   * Exact local hit: `mirror_pair_envelope_eq_two_cosh` identifies the
     exponential envelope with twice the hyperbolic cosine.
   * Exact pinned-library hit: `Real.cosh_strictMonoOn` proves strict
     monotonicity of the hyperbolic cosine on nonnegative inputs.
   * Searches for the complete exponential `StrictMonoOn` statement found no
     exact hit in the pinned library or the local formal modules.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import D5.S3.Zeros.MirrorPairEnvelope

namespace D5.S3.Zeros.Symmetry.MirrorPairEnvelopeMonotonicity

open Set
open D5.S3.Zeros.MirrorPairEnvelope

/-- Above the symmetry line, the mirror-pair envelope is strictly increasing
along the nonnegative log-scale. -/
theorem mirror_pair_envelope_strictMonoOn {beta : Real} (hbeta : 1 / 2 < beta) :
    StrictMonoOn
      (fun u : Real =>
        Real.exp ((beta - 1 / 2) * u) + Real.exp (-((beta - 1 / 2) * u)))
      (Ici 0) := by
  intro u hu v hv huv
  change
    Real.exp ((beta - 1 / 2) * u) + Real.exp (-((beta - 1 / 2) * u)) <
      Real.exp ((beta - 1 / 2) * v) + Real.exp (-((beta - 1 / 2) * v))
  rw [mirror_pair_envelope_eq_two_cosh, mirror_pair_envelope_eq_two_cosh]
  have hslope : 0 < beta - 1 / 2 := sub_pos.mpr hbeta
  have harg : (beta - 1 / 2) * u < (beta - 1 / 2) * v :=
    mul_lt_mul_of_pos_left huv hslope
  have hcosh :
      Real.cosh ((beta - 1 / 2) * u) < Real.cosh ((beta - 1 / 2) * v) :=
    Real.cosh_strictMonoOn (mul_nonneg hslope.le hu) (mul_nonneg hslope.le hv) harg
  linarith

/-- The strict-slope hypothesis is satisfiable. -/
example : (1 / 2 : Real) < 1 := by norm_num

/-- The nonnegative input domain is inhabited. -/
example : (0 : Real) ∈ Ici 0 := self_mem_Ici

#print axioms mirror_pair_envelope_strictMonoOn

end D5.S3.Zeros.Symmetry.MirrorPairEnvelopeMonotonicity
