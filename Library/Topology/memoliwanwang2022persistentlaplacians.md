---
bibkey: memoliwanwang2022persistentlaplacians
authors: Facundo Mémoli, Zhengchao Wan and Yusu Wang
year: 2022
title: Persistent Laplacians — Properties, Algorithms and Implications
doi: 10.1137/21M1435471
url: https://arxiv.org/html/2012.02808v3
claim: The nullity of the weighted persistent q-Laplacian equals the q-th persistent Betti number for every finite simplicial pair and every nonnegative degree.
strata_touched:
  - D5/S3/Geometry/SimplicialPersistence/WeightedPersistentHodge
license: citation-only
triage: anchor
---

# Weighted persistent harmonic representatives

Theorem 2.7 of Mémoli, Wan and Wang states, for each integer q ≥ 0,
that the persistent Betti number equals the nullity of the persistent
Laplacian. The chain spaces are real oriented simplex chains of a finite
weighted simplicial pair K contained in L. Weights are strictly positive,
and the canonical simplex vectors have squared norms equal to the
reciprocals of their weights.

The restricted incoming domain is the entire inverse image of Cq(K)
under the boundary of L. It contains linear combinations whose boundaries
cancel outside K, including combinations of simplices whose individual
boundaries are not carried by K. Its inner product is inherited from the
weighted chain space of L. The Laplacian is TT* + D*D, where T is the
restricted incoming boundary and D is the outgoing boundary of K.
The degree-zero outgoing boundary is zero.

Appendix A identifies the persistent homology image with cycles of K
modulo boundaries obtained from this restricted domain. Claim A.1 gives
the finite linear-algebraic harmonic quotient identification. Theorem 3.1
records the weight matrices and the inherited Gram matrix on the
restricted incoming domain. These passages support the weighted
interpretation; a plain transpose in arbitrary coordinates does not
represent the required adjoint.

The canonical map from a harmonic chain h to the class of its included
chain gives a real linear equivalence onto the image of the induced
homology map. This explicit representative interface is stronger than the
wording of Theorem 2.7; it is established by the chain-level construction
and the naturality of categorical real homology, rather than quoted as
that theorem's literal statement. No mathematical originality or
resolution of an open problem is asserted.

The scope includes empty face sets, degrees above dimension, equal
complexes, disconnected complexes, zero boundary ranks and classes
killed only by new filling chains in L. No homology-vanishing,
boundary-invertibility or lower or uniform weight bound is assumed.
Scalar extension is performed on integer chains and boundaries before
taking actual real homology. No commutation of scalar extension with
homology is assumed.

## Verified locator

- DOI: 10.1137/21M1435471
- URL: https://arxiv.org/html/2012.02808v3
- Theorem 2.7; Appendix A, Claim A.1 and the proof of Theorem 2.7;
  Theorem 3.1.
