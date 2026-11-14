/- GID: D5/S3/Combinatorics/Orthogonality/SixBitLineTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixBitLineTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Combinatorics/Orthogonality/SixBitLineTransfer.result; instance=D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weight_check
   digest: The complete twelve-color result on the actual one-dimensional Submodule graph. -/

import D5.S3.Combinatorics.Orthogonality.SixBitLineChromatic
import D5.S3.Combinatorics.Orthogonality.SixBitSubmoduleBridge
import D5.S3.Combinatorics.Orthogonality.BinaryLineGraph

/-! This is the actual graph transport of O2. The domain is every nonzero
six-coordinate vector and every one-dimensional Submodule, with no examples
or coordinate-line restriction replacing the received full theorem. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Orthogonality.SixBitLineTransfer

open SixBitSubmoduleBridge

noncomputable def vectorEquiv : SixBitLineChromatic.LineVertex ≃
    BinaryLineGraph.VectorVertex 6 :=
  bitsEquiv.subtypeEquiv (fun v => by
    change v ≠ 0 ↔ bitsEquiv v ≠ 0
    have hz : bitsEquiv 0 = 0 := bits_zero
    rw [← hz, bitsEquiv.injective.ne_iff])

noncomputable def maskGraphIso : SixBitLineChromatic.lineGraph ≃g
    BinaryLineGraph.vectorGraph 6 where
  toEquiv := vectorEquiv
  map_rel_iff' := by
    intro x y
    change (vectorEquiv x ≠ vectorEquiv y ∧ dotProduct (bits x.1) (bits y.1) = 0) ↔
      (x ≠ y ∧ BinaryOrthogonality.dot x.1 y.1 = 0)
    rw [vectorEquiv.injective.ne_iff, bits_dot]

/-- The target theorem uses the full induced graph on the actual lines of
NikandishClique.orthogonalityGraph6. Its finite premises are discharged by
current kernel checks; the original twelve source classes are unchanged. -/
theorem result : (BinaryLineGraph.lineGraph 6).chromaticNumber = 12 := by
  exact (SimpleGraph.chromaticNumber_congr (maskGraphIso.trans (BinaryLineGraph.graphIso 6))).symm.trans
    SixBitLineChromatic.result

#print axioms result

end D5.S3.Combinatorics.Orthogonality.SixBitLineTransfer
