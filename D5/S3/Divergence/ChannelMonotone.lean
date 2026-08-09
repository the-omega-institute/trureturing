/- GID: D5/S3/Divergence/ChannelMonotone
   generality: G
   mirror-B: D5/B/S3/Divergence/ChannelMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Restate DpiDefect.dpi_defect_nonneg in finite-channel inequality form. -/

/- Library-search audit trail (2026-08-09):
   * This module restates D5.S3.Divergence.DpiDefect.dpi_defect_nonneg in inequality form.
   * The mathematical content lives in DpiDefect; this module only preserves the frozen
     theorem name and statement as a thin corollary.
-/

import D5.S3.Divergence.DpiDefect

namespace D5.S3.Divergence.ChannelMonotone

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.DpiDefect

/-- Applying a strictly positive finite channel cannot increase classical KL divergence. -/
theorem kl_divergence_channel_le
    {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hp : (∀ x, 0 < p x) ∧ ∑ x, p x = 1)
    (hq : (∀ x, 0 < q x) ∧ ∑ x, q x = 1)
    (hW : (∀ x y, 0 < W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    klDivergence (channelOutput W p) (channelOutput W q) ≤ klDivergence p q := by
  exact sub_nonneg.mp (dpi_defect_nonneg p q W hp hq hW)

end D5.S3.Divergence.ChannelMonotone
