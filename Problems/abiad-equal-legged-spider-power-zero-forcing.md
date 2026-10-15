---
slug: abiad-equal-legged-spider-power-zero-forcing
bibkey: abiadflaggghaseminezhadzeijlemaker2026powers
doi: 10.48550/arXiv.2610.03892
url: https://arxiv.org/abs/2610.03892v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.result
---

# Zero forcing the ordinary powers of equal-legged spiders

## Problem

Aida Abiad, Mary Flagg, Sina Ghasemi Nezhad and Sjanne Zeijlemaker,
*The Zero Forcing Number of Graph Powers*, arXiv:2610.03892v1, section 3,
Conjecture 10: “Let m ≥ 2, k ≥ 1 and ℓ ≥ k+1. Then Z(S_m(ℓ)^k) = (m−1)k.”
The spider consists of m paths on ell vertices, joined at their first endpoints to a new center.
It has m*ell+1 vertices. The kth ordinary power joins distinct vertices at distance at most k.

## Motivation

The lower bound quantifies over every ordinary zero forcing initial set, and the published
Proposition 9 gives a forcing set of the claimed cardinality. Their equality includes the known
path case m=2 and tree case k=1, with no independent credit assigned to either case.

## Gap

The source proves the upper bound and reports finite computations. The missing universal lower
bound requires a matrix with both exact ordinary off-diagonal support and a sufficiently large
kernel, on all original vertices. An assumed support or nullity interface does not fill that gap.
Prospective registration: https://github.com/the-omega-institute/trureturing/issues/16346 .

## Route

Use the integer tridiagonal leg matrix with diagonal ell-1 and opposite directed weights
ell-1-i and i+1. Rectangular deflation yields P(k,B)=QR, exact positive band support and
nullity at least k. The zero-sum subspace of m leg kernels embeds with center coordinate zero
into ker P(k,A(t)), of dimension at least (m-1)k for every center parameter t.

Polynomial center corrections have zero coefficients above the distance budget and positive
coefficients at its boundary. Combined with the constant leg block, this proves all edge
polynomials nonzero and all nonedge polynomials zero. One common natural parameter avoids the
finite collection of zeros. Alon's nonsymmetric row-kernel restriction argument, encoded with
the repository's ordinary Black constructor, then bounds every forcing set. The source's
complete upper chronology gives equality.

## Falsifier

A triple m>=2, k>=1, ell>=k+1 with ordinary zero forcing number different from (m-1)k
would refute the conjecture. A failure of a matrix identity, support coefficient or forcing
step invalidates this construction, without by itself refuting the original conjecture.

## Evidence

The D5 result and matching Blueprint specify the exact original-domain equality. Current kernel,
axiom and registration results are provided by the scoped verification artifacts; this dossier
is not a second machine-state source. No numerical sample is used as the universal proof.

## Triage

### What the settlement shows

**Proved** (`D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.result`):
For natural m>=2, k>=1 and ell>=k+1, the ordinary zero forcing number is
Z(S_m(ell)^k)=(m-1)k, exactly the original Conjecture 10. For fixed m and k in this
domain, its value is independent of the equal leg length: any two lengths at least k+1
give the same value.

**Proved** (`D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.result`):
The direct application m=2 gives value k for ell>=k+1; the direct application k=1
gives value m-1 for m>=2 and ell>=2. These are the known path and tree subcases,
with no new mathematical novelty or separate open-problem resolution assigned to them.

**Proved** (`D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.result`):
Throughout m>=2, k>=1 and ell>=k+1, Proposition 9's tail forcing set of size (m-1)k
is optimal. Its upper bound is sharp on the entire original domain, and every ordinary
zero forcing set has at least (m-1)k vertices; no smaller ordinary forcing set exists.

**Proved, proof mechanism**
(`D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing.result`):
Rectangular leg deflation gives leg-kernel dimension at least k. Zero-sum tuples of
these leg-kernel vectors embed with center coordinate zero into the full spider-matrix
kernel, giving dimension at least (m-1)k for every center parameter. Polynomial support
and finite common-root avoidance select one natural parameter for exact ordinary
off-diagonal support on all m*ell+1 original vertices. The same rational matrix supplies
both support and kernel dimension to the ordinary row-kernel restriction bound for every
forcing set. The existing proof path is `spider_supported_parameter` and
`spider_kernel_dimension` into `spider_all_sets_lower`, then `tail_forces` and `tail_card`
into `result`.

**Open in this delivery:** Removing any original hypothesis, allowing unequal legs,
using strict-distance powers or positive semidefinite forcing, obtaining a symmetric
maximum-nullity extension, and extending to the separate grid question are unproved here.
The nonsymmetric rational matrix above supplies no symmetric-matrix maximum-nullity
conclusion. This marks the limits of this delivery, without claiming that these targets
are globally open.

**Source inspection (arXiv:2610.03892v1; distinct from formal grades):** The independent
v1 source review identified no later theorem invoking Conjecture 10. The proved sharpness
above upgrades Proposition 9's tail upper bound to the exact optimum. The source's
independently established path, cycle and spectral results and its separate grid question
acquire no new proof from this settlement. Section 4.2 (Multiplicities), Example 23 (PDF page 15;
https://arxiv.org/html/2610.03892v1#S4.SS2) has ell=2 and k=2,
outside ell>=k+1; it retains its separate source result and is not covered by `result`.

## ASSUMED-UNVERIFIED

The bounded prior-adjudication and ownership search is the one recorded in issue 16346. It does
not certify global absence of an earlier resolution or mathematical priority. Independent
source, proof, nonvacuity and admission review, freeze, publication and required integration
checks remain separate obligations.
