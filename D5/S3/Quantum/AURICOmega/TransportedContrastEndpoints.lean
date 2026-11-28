/- GID: D5/S3/Quantum/AURICOmega/TransportedContrastEndpoints
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/TransportedContrastEndpoints
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: []
   utility: none
   digest: Bound the squared contrast by the two reflected Gram deficits. -/

import Mathlib.Algebra.Order.Field.Rat
import OmegaMath.Geometry.TransportedContrastEndpoints

namespace D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints

/-- Reflection at the third point bounds the squared rational contrast at every overlap. -/
theorem reflected_contrast_sq_le {M : Type*} (k : M → M → ℚ) (tri : M → M → M → M)
    (hdiag : ∀ a, k a a = 1) (hsymm : ∀ a b, k a b = k b a)
    (hcancelLeft : ∀ a b, tri a a b = b) (hcancelRight : ∀ a b, tri a b b = a)
    (hinvLeft : ∀ a b c d, k (tri a b c) (tri a b d) = k c d)
    (hinvRight : ∀ a b c d, k (tri a c d) (tri b c d) = k a b)
    (hgram : ∀ (p : Fin 4 → M) (c : Fin 4 → ℚ),
      0 ≤ ∑ i, ∑ j, c i * c j * k (p i) (p j)) (x y z : M) :
    (k x z - k y z) ^ 2 ≤ (1 - k x y) * (1 - k z (tri x z y)) :=
  Omega.Geometry.TransportedContrastEndpoints.reflected_contrast_sq_le k tri hdiag hsymm
    hcancelLeft hcancelRight hinvLeft hinvRight hgram x y z

end D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints
