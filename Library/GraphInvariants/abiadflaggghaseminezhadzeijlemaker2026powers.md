---
bibkey: abiadflaggghaseminezhadzeijlemaker2026powers
authors: Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker
year: 2026
title: The Zero Forcing Number of Graph Powers
doi: 10.48550/arXiv.2610.03892
url: https://arxiv.org/abs/2610.03892v1
claim: Conjecture 12 asserts Z((P_b Cartesian P_ell)^k)=b*k for every b>=1, k>=1 and ell>=k+1, without a b<=ell condition. Section 3, Conjecture 10 asks whether Z(S_m(ell)^k)=(m-1)k for m>=2, k>=1, ell>=k+1.
strata_touched:
  - D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation
  - D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing
license: citation-only
triage: anchor
---

# The Zero Forcing Number of Graph Powers

## Verified locator

DOI: 10.48550/arXiv.2610.03892

https://arxiv.org/abs/2610.03892v1 ; original TeX at https://arxiv.org/src/2610.03892v1 ; rendered source at https://arxiv.org/html/2610.03892v1 . Version 1, 2 October 2026, §3, Conjecture 12, label `conj:grid`. The archive has 22050 bytes and SHA-256 `daceb11bdb649d725106ee67726ed39470178a01232a5d685184c89b30a2396e`; `main.tex` has 67168 bytes and SHA-256 `3e54c8b75acc83ace6adf491775d2c8eb046e9f5f755e0f941967ea92f044517`.

## GridPowerZeroForcingRefutation: Conjecture 12

### Statement

> Let b≥1, k≥1 and ℓ≥k+1. Then Z((P_b □ P_ℓ)^k)=bk.

Section 2 defines P_n as the path on n vertices, □ as the Cartesian product, and graph-power adjacency by 1≤dist_G(v,w)≤k. Ordinary zero forcing changes the unique white neighbor of a black vertex to black; Z is the minimum initial black-set size.

The preceding grid proof uses all pairs (r,t) with 1≤r≤b and 1≤t≤ℓ. A full-source and preceding-context scan finds no b≤ℓ convention. The paragraph before the conjecture reports exhaustive attainment for 1≤b≤3, 1≤k≤3 and k+1≤ℓ≤10, and cites the classical k=1 formula Z(P_b □ P_ℓ)=min(b,ℓ). The instance (3,2,1) lies in that reported range and contradicts the unrestricted attainment assertion and conjecture. No author-intent inference or correction to b≤ℓ is claimed.

### Classical reference

The source's reference AIM is AIM Minimum Rank – Special Graphs Work Group, “Zero forcing sets and the minimum rank of graphs”, Linear Algebra and its Applications 428 (2008), 1628–1648. The min(b,ℓ) formula is cited here as the source's literature attribution, not as newly proved mathematics or as an independently checked complete reading of that article. The formal refutation uses explicit forces and does not depend on this formula.

### Search boundary

Preregistration: https://github.com/the-omega-institute/trureturing/issues/16240 . Its bounded literature/ownership screen found no exact prior adjudication. Current source retrieval matches the above hashes; the abstract lists v1, and the v2 URL returns 404. The searched source and repository contain no correction or prior exact settlement. This does not certify absence in all literature. Search failures and access-limited services provide no negative evidence. A located correction or prior exact adjudication would disqualify this candidate for open-problem credit.

## SpiderPowerZeroForcing: Conjecture 10

### Verified locator

DOI: 10.48550/arXiv.2610.03892

URL: https://arxiv.org/abs/2610.03892v1

The version-labelled HTML https://arxiv.org/html/2610.03892v1 has SHA256
`e20d2cd7aa89230043f32f29b304f0f9ad0091004055237990f9fe50280fc2f0` and 526121 bytes.
Section 3, PDF page 7, Conjecture 10, TeX label `conj:spider`, states:
“Let m ≥ 2, k ≥ 1 and ℓ ≥ k+1. Then Z(S_m(ℓ)^k) = (m−1)k.”

### Source correspondence

Each of the m paths has ell vertices. Attaching their first endpoints to a new center gives
m*ell+1 vertices. With depth i starting at one, center distances are i, same-leg distances are
|i-j| and different-leg distances are i+j. Ordinary powers retain every vertex and join distinct
vertices at distance at most k. The forcing source is black and has a unique white neighbor.

Proposition 9 proves the upper bound by the last k vertices of each of the first m-1 legs.
It then completes these legs inward, forces the center, reaches depths one through k of the last
leg from the first leg and the center, and completes that leg outward. The k=1 middle phase is empty.
The source notes S_2(ell)=P_(2ell+1); this subcase and the tree case k=1 are known cases.

### Mathematical prerequisites and provenance

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

### Applicability

The formal target includes all m>=2, k>=1, ell>=k+1, including the simultaneous boundary
m=2, k=1, ell=k+1. It concerns ordinary zero forcing, ordinary powers and equal leg lengths.
It does not assert a result for unequal legs, strict powers, positive semidefinite forcing,
symmetric maximum nullity or the separate grid conjecture.

### Prior-resolution boundary

The supplied bounded primary-source and ownership screen is recorded in
https://github.com/the-omega-institute/trureturing/issues/16346 . The inspected source retains
the conjecture in v1. Bounded searches do not certify global unresolvedness, originality or priority.
