---
bibkey: steiningeryurkevich2026octahedron
authors: Jakob Steininger and Sergey Yurkevich
year: 2026
title: The Nieuwland number of the Octahedron
doi: 10.48550/arXiv.2609.10788
url: https://arxiv.org/abs/2609.10788v1
claim: The unnumbered conjecture in section 3 bounds the supremum of the diameter-plus-square scalar of octahedral projections by 3 sqrt(2)/4 times its infimum.
strata_touched:
  - D5/S3/Geometry/Polygons/SteiningerYurkevichOctahedronScalarRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2609.10788

Source: https://arxiv.org/abs/2609.10788v1

The source is version 1. The unnumbered scalar conjecture is in section 3,
“Remarks and discussion”, printed page 8. The separate Nieuwland-number
Theorem 1 is not the assertion refuted here.

## Source statement

The source TeX reads verbatim:

```tex
As an application of the above statement, we believe to have found a samurai function, that precisely takes its extremes at the optimal solution of the Octahedron: Define $\square(\PP)$ to be the side length of the smallest square, into which $\PP$ fits, and further define
\[
    \frak{o}(\PP) \coloneqq \Diam(\PP)+\frac{23}{10}\square(\PP).
\]
As $\Diam$ and $\square$ are samurai functions, so is $\frak{o}$. We conjecture that any projection of the Octahedron satisfies
\[
\sup_\pi \frak{o}(\pi(\OOO)) \leq \frac{3\sqrt{2}}{4} \inf_\pi \frak{o}(\pi(\OOO)),
\]
which would yield another proof of the Nieuwland number of the Octahedron.
```

Printed page 1 specifies the vertices:

```tex
Let $\OOO \subseteq \R^3$ be the Octahedron with vertices at $(e_1,e_2,e_3,-e_1,-e_2,-e_3)$, where $e_i$ denotes the $i$-th Cartesian unit vector.
```

On printed page 2 the projection domain is:

```tex
Any such orthogonal projection can be written as $M \cdot \OOO$, for some matrix $M \in \R^{2 \times 3}$ satisfying $M M^T = \id \in \R^{2\times2}$, and writing $M \cdot \PPP \coloneqq \{ MP \colon P \in \PPP \}$.
```

Printed page 4 defines:

```tex
\item $\Diam(\PP)$ is the diameter of $\overline{\PP}$, i.e. the largest distance between two points of $\overline{\PP}$,
```

The formalization uses the Euclidean filled convex hull of the six signed
coordinate vectors, all real orthonormal-row projection matrices, and all
rotations and translations of enclosing squares. The infimum of weak enclosing
lengths equals that of strict enclosing lengths by arbitrarily small positive
enlargement. The coefficient remains exactly 23/10.

## Mathematical consequence

The hexagonal shadow H has diameter 2√6/3 and enclosing-square side 1+√3/3.
The shadow I has diameter 4√2/3 and enclosing-square side 4/3. Their scalar gap
is greater than 9/1250. The formal result negates the displayed scalar
inequality; it does not negate Theorem 1 or the separate polar-duality result.

The experiment is in the-omega-institute/trureturing-experiments, commit
`ae622f18ab6637289c7036795a18ba5749b5d749`, at
`docs/reports/sy2609oct-octahedron-square-obstruction/check.py`.
Its SHA-256 is `55fd072af0ec65285f6c34439943de3d5ef450800dfd723b6be5394c8f3f16ff`;
the recorded exact-check exit code is 0 with final output `ALL_CHECKS_OK`.

## Scope

The source statement is literature-attested. The refutation is derived in this
repository. Literature completeness is ASSUMED-UNVERIFIED: the screen on issue
#27498 has unavailable sources and a stale third-party snapshot. This note
cites mathematical statements and reproduces no third-party program.
