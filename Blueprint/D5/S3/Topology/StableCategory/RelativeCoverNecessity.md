# An exact relative criterion for extending two categorical pieces

## Abstract

An exact relative criterion for extending two categorical pieces

**Theorem 1.1 (Relative extension is equivalent to hitting the maximal lower chains).**

Lean statement: `D5/S3/Topology/StableCategory/RelativeCoverNecessity.exists_relative_two_cover_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/RelativeCoverNecessity.exists_relative_two_cover_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Let two categorical lower regions cover the chains avoiding a chosen set of maximal elements. Assume each chosen maximum has a strict predecessor. An extension at the first chain subdivision, with the prescribed old intersections and order homotopies fixing them, exists exactly when one predecessor per maximum and per side suffices to hit every maximal lower chain in an eligible old region. To prove necessity, follow the singleton of a chosen maximum through a relative homotopy. Its first increase must add an element common to all maximal lower chains assigned to that side, because the homotopy fixes those old chains. The preceding extension theorem supplies the converse.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/RelativeCoverNecessity.exists_relative_two_cover_iff`
- Dependency: [D5/S3/Topology/StableCategory/MaximalChainCoverExtension](MaximalChainCoverExtension.md)
