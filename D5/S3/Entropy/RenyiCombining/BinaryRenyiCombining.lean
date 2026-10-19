/- GID: D5/S3/Entropy/RenyiCombining/BinaryRenyiCombining
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/BinaryRenyiCombining
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary Renyi entropy and binary convolution with its multiplicative bias identity. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-!
proof_shape: hRenyi: bind-only; escape_witness: none
  consumers: RenyiInformationCombiningOrderThree.hRenyiInv, HircheCachinCombiningConcavity.h
proof_shape: bconv: bind-only; escape_witness: none
  consumers: bconv_bias, RenyiInformationCombiningOrderThree.claim, HircheCachinCombiningConcavity.star
proof_shape: bconv_bias: bind-only; escape_witness: none
  consumers: RenyiInformationCombiningOrderThree.hRenyi_three_combining,
    HircheCachinCombiningConcavity.bias_combining
-/

namespace D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining

noncomputable def hRenyi (alpha p : ℝ) : ℝ :=
  (1 / (1 - alpha)) * Real.log (p ^ alpha + (1 - p) ^ alpha)

noncomputable def bconv (p q : ℝ) : ℝ := p * (1 - q) + (1 - p) * q

lemma bconv_bias (p q : ℝ) : 1 - 2*bconv p q = (1 - 2*p)*(1 - 2*q) := by
  unfold bconv
  ring

end D5.S3.Entropy.RenyiCombining.BinaryRenyiCombining
