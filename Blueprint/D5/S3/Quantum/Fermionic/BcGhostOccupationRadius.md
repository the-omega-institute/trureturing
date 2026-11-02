# Finite radii on the original ghost Fock carrier

## Abstract

Finite radii on the original ghost Fock carrier

The radius uses even sites 2j with j<A-1 and odd sites 2j+1 with j<A+2. Every finite-excitation vector admits such a radius. The bounds are purely algebraic, and use the original occupation creation and annihilation operators.

**Definition 1.1 (The actual b/c creator-site prefix).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.sites`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.sites` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For A at least two, the even creator labels range from minus A to minus two and the odd creator labels range from minus A to one. This parity-sensitive prefix is the cutoff used by the tensor coupling.

**Definition 1.2 (Finite support inside the actual prefix).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.Radius`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.Radius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Radius A w means that every occupation in the finitely supported state w is a subset of sites A.

**Theorem 1.3 (Every original ghost state has a radius).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.exists_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.exists_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every w in the original complex countable occupation Fock carrier, there is a natural A at least two with Radius A w. The largest site in the union of the finite support supplies a bound.

**Theorem 1.4 (The actual positive ghost tails vanish).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.high_modes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.high_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every A at least two, state w in Radius A and integer t>A, both b_t w and c_t w vanish. The proof uses their exact odd and even annihilation indices, not an imposed truncation.

**Theorem 1.5 (Single-mode occupation growth).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.mode_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.mode_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original state in radius A at least two and integer t, both b_t w and c_t w lie in radius max(A,abs(t),2). Annihilation erases a site and creation inserts the site specified by the original mode.

**Theorem 1.6 (The original ghost Virasoro radius bound).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.virasoro_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.virasoro_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer r, the original locally finite L_r maps Radius A into Radius A+max(0,-r). The finite normal-order sum is captured on q in [r-A,A]. In the right normal-order branch the b annihilator preserves Radius A before the c high-mode cutoff is used.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.Radius`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.exists_radius`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.high_modes`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.mode_radius`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.sites`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.virasoro_radius`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostVirasoro](BcGhostVirasoro.md)
