# The Two-Coordinate Metallic Transfer

## Abstract

The metallic transfer word returns the pair (1,0) after each cycle and bounds both coordinates by the set {-1,0,1,2}.

**Definition 1.1 (The ordered transfer coefficients).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransfer.topWord`

*Formalization.* `D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransfer.topWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

At n = 2 the word of pairs (d,b) is (2,-1),(0,1),(0,-1),(1,-1),(0,-1),(0,-1),(2,1),(-1,-1). For every other nonnegative n it starts with (2,-1),(0,1), contains n-2 copies of the triple (1,-1),(1,-1),(-1,-1), then (0,-1),(1,-1),(0,-1),(-1,-1), then n-3 copies of the same triple, and ends with (1,-1),(1,-1),(0,-1),(2,1),(-1,-1). Repetition counts use natural subtraction truncated at zero.

**Theorem 1.2 (Periodicity and bounds of the transfer coordinates).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransfer.block_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransfer.block_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

Let n be at least two, let W be its transfer word of length L, and let z_p be a sequence of integer pairs with z_0 = (1,0). If W at position p modulo L is (d,b), require z_{p+1} = (d x - b y,x), where z_p = (x,y). Then for every nonnegative p, z_{p+L} = z_p and both coordinates of z_p belong to {-1,0,1,2}. Repeated triples and the two end segments give the return and the bounds at every intermediate position.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransfer.block_transfer`
- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransfer.topWord`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs](MetallicHankelDefs.md)
