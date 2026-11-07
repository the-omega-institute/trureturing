/- GID: D5/S0/Certificates/FiniteSymmetryDAGNode
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteSymmetryDAGNode
   mirror-E: none(waiver:finite-cached-certificate-replay)
   anchors: [D5/S0/Certificates/FiniteSymmetryBoundReplay]
   utility: none
   digest: Finite certificate nodes retain literal coordinates and every value child while leaving all acceptance obligations to the checker. -/

import D5.S0.Certificates.FiniteSymmetryBoundReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteSymmetryDAGNode

/-- Untrusted finite certificate data. A node supplies a bound test, a symmetry
action to check, or the child for every value of its literal split coordinate.
Sharing an index supplies no acceptance proof for any partial context. -/
inductive Node (N : ℕ) (Coord Value Sym : Type*) where
  | bound
  | symmetry (s : Sym)
  | split (i : Coord) (children : Value → Fin N)

end D5.S0.Certificates.FiniteSymmetryDAGNode
