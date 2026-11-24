# Affine Steiner Switch Counts

## Abstract

Exact switch counts in binary extensions of affine ternary Steiner loops.

**Theorem 1.1 (Every affine pivot pair has the same switch count).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerAffineSwitchCount.labelledAffineSwitchCount`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerAffineSwitchCount.labelledAffineSwitchCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Take a finite additive group V with x+x=-x for every x and more than three elements. Adjoin a new identity to V. Two different points x and y multiply to -x-y, and two equal points multiply to the new identity. Choose any triple labelling with values in a finite binary vector space A and form the normalized extension.

There is one numbering of the extension and one complete Steiner triple system for this labelling. Its centre is the fibre over the adjoined identity. For each ordered pair of distinct affine points p and q, delete the label of (p,0) and retain (q,0) as pivot. Using the actual matching of uncovered pairs, there are exactly |A|(|V|-3) successful starts.

Off the affine line through p and q the composite of the left translations is translation by q-p, so each such point has period three. On the line together with the identity the composite consists of two transpositions. Each two-step return uses the same triple twice after normalization, so its binary return row vanishes. The off-line calculation also supplies a witness to failure of associativity at each affine point and gives trivial centre in the quotient. Every off-line point contributes a full fibre to the count.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerAffineSwitchCount.labelledAffineSwitchCount`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerReturnDependencies](SteinerReturnDependencies.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerSchreierSwitchCount](SteinerSchreierSwitchCount.md)
