/- GID: D5/S3/Quantum/AURICOmega/TransportedContrastEndpoints
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/TransportedContrastEndpoints
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: []
   utility: none
   digest: Bound the reading contrast at overlap three fifths by two translated Gram probes. -/

import Mathlib.Algebra.Order.Field.Rat
import OmegaMath.Geometry.TransportedContrastEndpoints

namespace D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints

/-- At overlap three fifths, bilateral heap transport gives a uniform gap of one
two-thousand-five-hundredth below the five-point contrast endpoint. Repeated
sample points are allowed in the five-point Gram hypothesis. -/
theorem abs_contrast_le {M : Type*} (k : M → M → ℚ) (tri : M → M → M → M)
    (hdiag : ∀ a, k a a = 1) (hsymm : ∀ a b, k a b = k b a)
    (hnonneg : ∀ a b, 0 ≤ k a b)
    (hcancelLeft : ∀ a b, tri a a b = b) (hcancelRight : ∀ a b, tri a b b = a)
    (hassoc : ∀ a b c d e, tri (tri a b c) d e = tri a b (tri c d e))
    (hinvLeft : ∀ a b c d, k (tri a b c) (tri a b d) = k c d)
    (hinvRight : ∀ a b c d, k (tri a c d) (tri b c d) = k a b)
    (hgram : ∀ (p : Fin 5 → M) (c : Fin 5 → ℚ),
      0 ≤ ∑ i, ∑ j, c i * c j * k (p i) (p j))
    (x y z : M) (ht : k x y = 3 / 5) : |k x z - k y z| ≤ 406 / 625 :=
  Omega.Geometry.TransportedContrastEndpoints.abs_contrast_le k tri hdiag hsymm hnonneg hcancelLeft hcancelRight
    hassoc hinvLeft hinvRight hgram x y z ht

end D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints
