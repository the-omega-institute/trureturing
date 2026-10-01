# Symmetric scene lifting sufficiency

## Abstract

A connected free C2 incidence geometry satisfies every literal source count but has an algebraically generic nontrivial symmetric scene.

**Definition 1.1 (The complete source lifting assertion).**

Lean statement: `D5/S3/Geometry/SymmetricScenesRefutation.liftingSufficiency`

*Formalization.* `D5/S3/Geometry/SymmetricScenesRefutation.liftingSufficiency` (`✓ std3`).

*Citation.* Signe Lundqvist, Bernd Schulze, Klara Stokes (2026). *Symmetric polyhedral scenes and parallel redrawings*. DOI: [10.48550/arXiv.2609.27605](https://doi.org/10.48550/arXiv.2609.27605). URL: <https://arxiv.org/html/2609.27605v1#S6>.

*Commentary.*

For every d >= 2, finite connected labelled incidence geometry with degree at least d, finite group acting freely and faithfully on both point and hyperplane labels, orthogonal representation, sign character and actual representative gain chart, the full orbit-count equality and every incidence-orbit subset inequality imply minimal symmetric flatness of every generic symmetric picture. Genericity means algebraic independence over Q of all coordinates of point-orbit representatives. Component penalties are the finranks of the actual invariant hyperplane subspaces for unbounded closed gain walks. This is the lifting clause of Conjecture 6.1.

**Theorem 1.2 (A generic connected lifting counterexample).**

Lean statement: `D5/S3/Geometry/SymmetricScenesRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SymmetricScenesRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lundqvist-schulze-stokes-symmetric-scenes-lifting-refutation` (refuted) by `D5/S3/Geometry/SymmetricScenesRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lundqvist-schulze-stokes-symmetric-scenes-lifting-refutation","declaration_gid":"D5/S3/Geometry/SymmetricScenesRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Signe Lundqvist, Bernd Schulze, Klara Stokes (2026). *Symmetric polyhedral scenes and parallel redrawings*. DOI: [10.48550/arXiv.2609.27605](https://doi.org/10.48550/arXiv.2609.27605). URL: <https://arxiv.org/html/2609.27605v1#S6>.

*Commentary.*

The result proves Not OriginalSource.liftingSufficiency. Use d=3, C2 with tau=-I2 and the trivial character, three point orbits and two distinct hyperplane orbits. At each hyperplane label the gain incidences are (P0,0),(P0,1),(P1,0),(P2,0). The connected full cover has 6 points, 4 hyperplanes and 16 distinct incidences, a free faithful action, and degree 4 at every hyperplane.

Every literal orbit subset, supported component, unbounded gain closure and genuine invariant-space dimension transports from the C2 witness to the general source telescope. The same representative coordinates are algebraically independent. The explicit scene uses positive-copy normal (-b,a), zero constants, and heights 0,-(ad-bc),-(af-be). Opposite-copy normals differ, so the scene is nonflat. No affine-spanning premise is used.

Nonflatness contradicts the necessary flatness clause of minimal flatness. The parallel-redrawing clause and Conjecture 6.2 remain outside this conclusion.

## References

- Truth anchor: `D5/S3/Geometry/SymmetricScenesRefutation.liftingSufficiency`
- Truth anchor: `D5/S3/Geometry/SymmetricScenesRefutation.result`
