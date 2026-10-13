---
bibkey: abiad2026graphpowers
authors: Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker
year: 2026
title: The Zero Forcing Number of Graph Powers
doi: 10.48550/arXiv.2610.03892
url: https://arxiv.org/abs/2610.03892v1
claim: Section 3, Conjecture 10 asks whether Z(S_m(ell)^k)=(m-1)k for m>=2, k>=1, ell>=k+1.
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing
license: citation-only
triage: anchor
---

# Ordinary powers of equal-legged spiders

## Verified locator

DOI: 10.48550/arXiv.2610.03892

URL: https://arxiv.org/abs/2610.03892v1

The version-labelled HTML https://arxiv.org/html/2610.03892v1 has SHA256
`e20d2cd7aa89230043f32f29b304f0f9ad0091004055237990f9fe50280fc2f0` and 526121 bytes.
Section 3, PDF page 7, Conjecture 10, TeX label `conj:spider`, states:
“Let m ≥ 2, k ≥ 1 and ℓ ≥ k+1. Then Z(S_m(ℓ)^k) = (m−1)k.”

## Source correspondence

Each of the m paths has ell vertices. Attaching their first endpoints to a new center gives
m*ell+1 vertices. With depth i starting at one, center distances are i, same-leg distances are
|i-j| and different-leg distances are i+j. Ordinary powers retain every vertex and join distinct
vertices at distance at most k. The forcing source is black and has a unique white neighbor.

Proposition 9 proves the upper bound by the last k vertices of each of the first m-1 legs.
It then completes these legs inward, forces the center, reaches depths one through k of the last
leg from the first leg and the center, and completes that leg outward. The k=1 middle phase is empty.
The source notes S_2(ell)=P_(2ell+1); this subcase and the tree case k=1 are known cases.

## Mathematical prerequisites and provenance

Noga Alon, *A propagation process on Cayley graphs*, Theorem 2.1 and section 3,
https://www.cs.tau.ac.il/~nogaa/PDFS/pn.pdf, gives the arbitrary-field row-kernel restriction
argument with arbitrary diagonal and nonsymmetric matrices. The PDF has SHA256
`6db8137fd086bce4b5aa73439a4620ff40450ef012c9f53e1e007d8dc55104ab` and 109668 bytes.
The ordinary Black induction is its directly consumed formal prerequisite. It is a known
mechanism, with no mathematical novelty claimed here.

The rectangular C/D ladder, polynomial coefficient rules, finite-root bound, rank-nullity and
finite-product dimension formulas supply the construction. Elementary ladder identities and
linear-algebra prerequisites carry no novelty claim. The matrix is nonsymmetric: its kernel
bounds ordinary zero forcing directly and makes no symmetric minimum-rank or maximum-nullity claim.

DeAlba et al., *Minimum rank of powers of trees*, ELA 23 (2012), 151–163,
DOI 10.13001/1081-3810.1511, supplies an ordinary path-power subcase and a strict tree-square
result. Those hypotheses do not give the full ordinary spider statement.

## Applicability

The formal target includes all m>=2, k>=1, ell>=k+1, including the simultaneous boundary
m=2, k=1, ell=k+1. It concerns ordinary zero forcing, ordinary powers and equal leg lengths.
It does not assert a result for unequal legs, strict powers, positive semidefinite forcing,
symmetric maximum nullity or the separate grid conjecture.

## Prior-resolution boundary

The supplied bounded primary-source and ownership screen is recorded in
https://github.com/the-omega-institute/trureturing/issues/16346 . The inspected source retains
the conjecture in v1. Bounded searches do not certify global unresolvedness, originality or priority.
