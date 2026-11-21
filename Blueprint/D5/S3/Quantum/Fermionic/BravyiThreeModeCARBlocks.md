# The three-mode channel in chiral coordinates

## Abstract

Clifford conjugations and the exact block reduction of the three-mode channel.

**Theorem 1.1 (The Majorana relations).**

Lean statement: `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.majorana_anticomm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.majorana_anticomm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct Majorana matrices anticommute. The signed row permutations compute the two products over the Gaussian integers.

**Theorem 1.2 (The action on Majorana products).**

Lean statement: `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.conjugateWord_majorana_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.conjugateWord_majorana_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by a Clifford word gives a sign on each Majorana generator. The signs multiply on an ordered word of generators.

**Theorem 1.3 (Exact real blocks for the normal form).**

Lean statement: `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.channel_normal_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.channel_normal_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the rank-one projector of the real spinor with entries c, 0, 0, 0, p, q, 0, 0 and squared norm one. Applying the weighted Clifford channel and changing to the signed basis gives the complex embedding of the four-dimensional chiral block and two copies of the two-dimensional complementary block.

**Theorem 1.4 (The block characteristic polynomial).**

Lean statement: `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.determinantBlocks_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.determinantBlocks_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed ordering places the three blocks on the diagonal. The characteristic polynomial of the assembled real matrix is the chiral characteristic polynomial times the square of the complementary characteristic polynomial.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.channel_normal_blocks`
- Truth anchor: `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.conjugateWord_majorana_prod`
- Truth anchor: `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.determinantBlocks_charpoly`
- Truth anchor: `D5/S3/Quantum/Fermionic/BravyiThreeModeCARBlocks.majorana_anticomm`
- Dependency: [D5/S3/Quantum/Fermionic/BravyiThreeModeDeterminantOrder](BravyiThreeModeDeterminantOrder.md)
