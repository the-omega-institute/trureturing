/- GID: D5/S3/Quantum/Divergence/CanonicalChannelDPIComposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CanonicalChannelDPIComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Support-aware quantum relative entropy contracts along a composite finite channel. -/

import D5.S3.Quantum.Divergence.CanonicalChannelDPI
import D5.S3.Quantum.Foundation.FiniteStateChannel

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.CanonicalChannelDPIComposition

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI

universe u v w

/-- Data processing is closed under sequential composition of finite quantum channels.

The proof exposes the pathway explicitly: apply the second channel's DPI to the
intermediate pair, then apply the first channel's DPI to the original pair. -/
theorem extended_quantum_relative_entropy_comp_dpi
    {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (second : QuantumChannel b c) (first : QuantumChannel a b)
    (rho sigma : DensityState a) :
    extendedQuantumRelativeEntropy ((second.comp first).mapState rho)
      ((second.comp first).mapState sigma) ≤
      extendedQuantumRelativeEntropy rho sigma := by
  simpa only [QuantumChannel.comp_mapState] using
    (extended_quantum_relative_entropy_channel_dpi
      second (first.mapState rho) (first.mapState sigma)).trans
      (extended_quantum_relative_entropy_channel_dpi first rho sigma)

#print axioms extended_quantum_relative_entropy_comp_dpi

end D5.S3.Quantum.Divergence.CanonicalChannelDPIComposition
