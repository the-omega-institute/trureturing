---
bibkey: dasmohanty2024inverse
authors: Joyentanuj Das; Sumit Mohanty
year: 2024
title: Inverse of the Squared Distance Matrix of a Complete Multipartite Graph
doi: 10.13001/ela.2024.8283
url: https://arxiv.org/abs/2311.01069v2
claim: "The concluding conjecture asks for both the exact positive eigenvalue multiplicities and the inertia of the singular squared-distance Laplacian-like matrix defined in equation (3.6)."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance
license: citation-only
triage: anchor
---

# Singular squared-distance Laplacian of a complete multipartite graph

## Verified locator

- Author source: https://arxiv.org/abs/2311.01069v2, version 2,
  2024-04-18; the definitions of Phi, Psi, Theta and omitted parameter lists,
  equation (3.6), and the complete concluding conjecture.
- Version of record identifier: https://doi.org/10.13001/ela.2024.8283,
  Electronic Journal of Linear Algebra 40 (2024), 475–490. This identifier
  does not certify inspection of the publisher full text, license or erratum.
- Omission convention: the original version at
  https://arxiv.org/abs/2311.01069v1, and version 2 Lemma 3.1(d) and
  Appendix A(c), specify applying the same function to the shortened list.

## Source definitions and target

The source uses the squared graph-distance matrix of a complete multipartite
graph. The cofactor condition preceding equation (3.6) is nonzero sum of
all cofactors, not a single principal cofactor. Phi is the product of the
factors 3n_i−4; Psi sums n_i times the product with parameter i omitted;
Theta is Phi plus Psi. A hat removes exactly the indicated parameters,
including when two parameters are omitted. Equation (3.6) defines the
diagonal, same-part off-diagonal and between-part entries of the
Laplacian-like matrix on this domain.

The complete concluding conjecture states: if the squared-distance matrix is
singular, “1/4 and 1 are the only positive eigenvalues” of this Laplacian-like
matrix, with multiplicities n−t and h−1 respectively, and its inertia is
(n−s−1,1,s). Here t=s+h, the s nonsingleton parts have size at least two,
and the h singleton parts have size one. The inertia order is positive,
zero, negative. The inherited nonzero sum-of-cofactors condition remains
part of the formal target.

Version 2's expanded hatted-Psi products omit the indicated list parameters
but fail to omit the summation index. Those displays conflict with the
same source's original omitted-list equalities. The formal definitions use
the latter semantics, consistent with the cited lemma and appendix.
Equation (3.6) and the complete conjecture are unchanged between the two
author versions. The malformed expansion is not certified, substituted
as a definition, or used as a counterexample.

The finite dependent vertex carrier and the names d and ratio are repository
encodings and proof abbreviations for these source parameters. The block
inverse, rank-one reduction, basis and eigenspace arguments are repository
proof constructions. The authors' target and definitions are attributed
to this note; the new proof is repository-derived.

## Rights and literature boundary

The arXiv record has the nonexclusive distribution license. It does not
supply a reuse license for publisher text or code. This note is citation-only;
publisher full text, reuse license and any publisher correction remain
unverified. No publisher file or source archive is retained.

The authorized bounded source and literature screen in issue #25619 found
no complete resolution in its inspected scope. Complete forward citations,
worldwide openness, hidden repository aliases and priority are not established.
The source's nonsingular inverse formula and previously proved inertia of
the squared-distance matrix are distinct from this singular Laplacian target.
