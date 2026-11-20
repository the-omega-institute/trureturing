# Equality in the cograph distance multiplicity bound

## Abstract

The connected cographs attaining the eligible distance multiplicity bound and an explicit infinite family.

**Theorem 1.1 (Characterization and explicit infinite family).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/CographDistanceMultiplicity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Cographs/CographDistanceMultiplicity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Commentary.*

Open Problem 14.2(ii) asks which connected cographs attain the ordinary distance multiplicity bound at a real shift other than −1 and −2, and asks for an explicit infinite family. The width is the least number of chains for the vicinal preorder.

Every width-one connected cograph attains. At greater width the normalized join root must have exactly one nonleaf child and at least one leaf child. Attainment holds exactly when an eligible real guard root gives a nullity deficit of one in the nonleaf child and its scalar response g satisfies 1 + g − ℓ/(x+1) = 0, where ℓ counts the leaf children. The guard polynomials give a mathematically exact finite candidate set, with the scalar recursion valid also at poles and coincident roots. Executable root isolation lies outside this statement.

For every integer s ≥ 2, join a clique of size 3(s−1) to the disjoint union of the complete bipartite graph with parts of size s and s isolated vertices. Its order is 6s−3, its width is two, and its ordinary distance multiplicity is two at the eligible shift s−2. Strictly increasing orders give pairwise nonisomorphic connected cographs.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/CographDistanceMultiplicity.result`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion](../CographDistanceCriterion.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance](UniversalCliqueCographDistance.md)
