---
bibkey: lundstrom2025crown
authors: Teemu Lundström and Leonardo Saud Maia Leite
year: 2025
title: "Order polytopes of crown posets"
doi: 10.48550/arXiv.2504.05123
url: https://arxiv.org/abs/2504.05123v3
claim: "Conjecture 3.7: for every positive integer n, the full geometric f-vector of the order polytope of the crown on 2n vertices is log-concave. Theorem 3.6 supplies the face-count formula, not a proof of this conjecture."
strata_touched:
  - D5/S3/Combinatorics/Geometry/CrownOrderPolytope
  - D5/S3/Combinatorics/Geometry/CrownOrderPolytopeFaceCounts
  - D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive
  - D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity
  - D5/S3/Analytic/RealRootedCoefficientNewton
license: citation-only
triage: anchor
---

# Crown order polytopes and Conjecture 3.7

## Verified locator

DOI: 10.48550/arXiv.2504.05123

URL: https://arxiv.org/abs/2504.05123v3

The inspected primary version is arXiv:2504.05123v3, dated 9 December
2025 in the supplied HTML. Both the 25-page PDF and the HTML were read
directly for the definitions, enumeration and conjecture. The PDF SHA-256 is
`90581682c5daf1125ccf1bc937a581aa4c0d43254e0d4c62fca5553299864400`;
the supplied arXiv HTML SHA-256 is
`9e6cbda3cc5a9793adf3781afc374d58d29f5df43d29ee39ebf5f04f431f2abd`.
These identify the inspected files, not a claim that a later download has
identical bytes. A fresh read of the unversioned arXiv abstract on
2026-09-20 still identifies v3 as its current version and also records the
journal DOI `10.1016/j.ejc.2025.104304` (European Journal of Combinatorics).
The mathematical source inspected here remains the versioned arXiv text.
The supplied HTML states the arXiv perpetual non-exclusive license.
This note supplies citation, a short quotation, and mathematical mapping;
it does not redistribute the paper or assert a software license for it.

Conjecture 3.7, PDF page 12 (also checked against the supplied HTML), states:

> For any positive integer n, the entries of the f-vector of O(C₂ₙ) form a log-concave sequence.

Here `O(C₂ₙ)` transcribes the source's calligraphic order-polytope notation.
The preceding paragraph reports tests for `n = 1,...,200` and explicitly
says the authors were unable to prove the assertion for every `n`.
That experiment is neither a domain restriction nor a universal proof.

## Geometric object and hypotheses

The introduction defines the crown on `[2n]` by
`1 < 2 > 3 < ... > 2n-1 < 2n > 1`. Section 2 defines its order
polytope as the real vectors in `[0,1]^(2n)` satisfying `x_i <= x_j`
for all order comparisons. In Lean, source vertex `j` is coordinate
`j-1 : Fin (2*n)`. Thus zero-based even vertices are the lower vertices;
`crownRelation` compares each with its cyclic successor and predecessor.
The resulting set is `CrownOrderPolytope.crownOrderPolytope n`.
At `n=1` the two neighbor descriptions coincide, giving a two-element
chain and a triangle, not a simple cycle of length at least three.

The source defines the full f-vector as `(f_-1,f_0,...,f_(2n))`.
The empty face and whole polytope both occur. Lean uses actual exposed
faces of the real polytope. For a polytope these are the usual geometric
faces; the formalization proves its face/partition correspondence from
the defining affine inequalities. `crownGeometricFaceCount n d` is
`Nat.card` of the nonempty exposed faces whose affine-span direction
has real `Module.finrank` equal to `d`. It is not defined by a counting
formula. `crownGeometricFVector n : Fin (2*n+2) -> Nat` has entry zero
equal to one and entry `k>0` equal to that geometric count at `k-1`.

The target quantifies `n,k : Nat`, `0<n`, `0<k`, `k<2*n+1` and asserts
`F(n,k-1)*F(n,k+1) <= F(n,k)^2`. These are every internal index of
the full vector. There is no assumed face formula, real-rootedness,
asymptotic qualification, or finite cutoff in the target's hypotheses.

The 19-module formal chain is canonically frozen. Its final declaration,
`CrownOrderPolytopeLogConcavity.crownGeometricFVector_log_concave`,
has a typed `Proved` claim in the matching Scribe document bound to
`Problems/crown-order-polytope-log-concavity.md`. The displayed formula
is a handwritten presentation of that compiled declaration with `F`
defined as the full geometric vector. Only the full named conjecture is
the resolution target; the prerequisite freeze count is not a KPI.
Final artifact reviews, required CI for this increment and dev merge
remain pending.

## Published prerequisites and formal correspondence

| Source | Formal content and scope |
| --- | --- |
| Section 2; Theorem 3.1, attributed there to Stanley [20] | `CrownOrderPolytope`, `CCP`, and `Dimension` construct the actual face/connected-compatible-partition correspondence and prove dimension equals quotient-block cardinality minus two for nonempty faces. |
| Lemma 3.2 and its proof | `CycleCuts`, `CyclePartitions`, and `OddBlocks` express connected cyclic blocks, parity, compatibility, and lower/upper extremality. `CycleIntervals` separately proves the interval description and has no D5 importer. Cycle arguments explicitly require `n>=2`. |
| Proposition 3.3(i)-(iii) | `EndpointMergers`, `EndpointRecovery`, and `TwoExceptions` implement source-selected endpoint merging, its inverse, all quotient sizes at least three, and the two exceptional two-block partitions. |
| Lemmas 3.4 and 3.5 | `Enumeration`, `MarkedCuts`, and `SelectionCounts` construct parity-adjusted compositions, marked cuts, actual quotient-block counts, and the selection sum, including the one-block edge. |
| Theorem 3.6 | `FaceCounts` proves the geometric formula for `n>=2`; `Positive` supplies the separate chain case and proves the same formula for every `n>0`. |

Theorem 3.6 is
`f_d = delta_d + sum_(i=2)^(2n) sum_(m=1)^(floor(i/2))
(2n/i) choose(i,2m) choose(n+m-1,i-1) choose(2m,i-d)`, where
`delta_0=2`, `delta_1=1`, and all later corrections vanish.
The binomial coefficient is zero when its lower index is negative or
larger than its upper index. Lean's natural subtraction would lose the
negative-index condition; the actual sum therefore uses
`if d <= i then Nat.choose (2*m) (i-d) else 0`.
Its natural division by `i` is justified by the counting proof before
transport to the rational scalar expression.

These correspondences formalize published mathematics. Their
implementation details are not an assertion of new enumerative results.
The source's introductory `4n` facet observation uses the nondegenerate
cycle picture; it must not be used at `n=1`, where the vector is
`(1,3,3,1)`. The Lean chain argument handles that boundary explicitly.

## Contribution and classical ingredients

Write `A(n,m)=(n/m) choose(n+m-1,2m-1)` and
`S_n(X)=sum_(m=1)^n A(n,m)(1+X)^(n+m)`. `Scalar` proves
`f_d = 2*[d=0] + [d=1] + coeff(S_n,d)` for every positive `n`.
`Chebyshev` proves `X Q_n(X)=2(T_n((X+2)/2)-1)` with
`Q_n(X)=sum_(m=1)^n A(n,m)X^(m-1)`; hence
`S_n(X)=2(1+X)^n(T_n((X+3)/2)-1)`.

The final proof factors `T_n-1` by parity, retaining squared factors and
their repeated roots. It obtains real splitting of the auxiliary `S_n`
from the pinned Chebyshev root API. The licensed upstream Newton inequality
give `(j+1)s_(j+1)^2 >= (j+2)s_j s_(j+2)`.
For `n>=2`, the additional bounds `s_0>=n^2` and
`s_0<=s_1<=2n s_0` prove all three affected comparisons:
`s_1+1 <= (s_0+2)^2`, `(s_0+2)s_2 <= (s_1+1)^2`, and
`(s_1+1)s_3 <= s_2^2`. All other comparisons follow from Newton.
The actual `n=1` vector supplies both internal inequalities separately.

`RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm` is the reduced
elementary-symmetric Newton inequality transplanted from the immutable
upstream source identified in `tao2026newton.md`. It is classical
mathematics. Its derivative-root reduction and strong induction retain
multiplicities. The Crown proof applies it to `p.roots.map Neg.neg` at
index `p.natDegree-k-2`; the pinned Vieta formula supplies the coefficient
conversion inside that proof. The leading coefficient is squared, and
the extra degree factor is discarded by a nonnegative-square estimate.
When `k+2` exceeds the degree, that coefficient vanishes. There is no
standalone coefficient-conversion theorem or independent Newton reproof.

Remark 3.8, PDF page 13, explicitly says the actual f-polynomials displayed in Table 1
are not real-rooted, even under the alternative convention omitting the
empty and whole faces. The proof claims splitting only for the auxiliary
scalar polynomial; it makes no real-rootedness claim for the actual
f-polynomial or any h/Ehrhart polynomial.

## Bounded library-first and prior-resolution audit

The 2026-09-20 local refresh inspected repository D5 sources and pinned
Mathlib at `db584cd6d46c92f209a44c0f1c829460d327499d`, with Lean
`v4.33.0`. The semantic pattern `newton|laguerre|log.?concav|real.?root`
matched 12 Mathlib files; adding `crown.*polytop` for D5 matched 99 files.
The targeted coefficient/inequality and derivative searches found the
current Crown/Newton chain and Mathlib's
`Polynomial.card_roots_le_derivative`, but no public exact general
coefficient-Newton theorem elsewhere in the inspected scope.
Repository `SourceJensenPositiveExtension` already contains a private
`laguerre_splits`; this is acknowledged prior formal work, not a public
coefficient API. Newton power-sum identities and Newton-Hankel root
criteria have different conclusions. The pinned split-polynomial and
Chebyshev root APIs are used directly inside the content proofs.
This bounded name/shape audit is not an exhaustive semantic search.

The public API refresh found an upstream candidate:
[Mathlib PR 42876](https://github.com/leanprover-community/mathlib4/pull/42876),
open and unmerged when inspected on 2026-09-20, with head
`e3c1793d0e097d9b8d782a323e91c99c2ef0d64c`.
Its `Mathlib/Analysis/MeanInequalitiesSymmetric.lean` (231 lines,
SHA-256 `daab9424b8817d3e6bf62f14fe1bfb1c35cf96a47157897d46af2f64a70da2f2`)
defines `Multiset.nesymm` and proves
`Multiset.nesymm_mul_nesymm_le_sq_nesymm` for every real multiset and
natural index, together with the degree-sharp unnormalized forms
`esymm_mul_esymm_le_sq_esymm` and `esymm_mul_esymm_le_sq_esymm'`.
The public source supplies the derivative/root argument and its
elementary-symmetric prerequisites. It is outside the pinned dependency
set. Its immutable `lean-toolchain` is
`leanprover/lean4:v4.34.0-rc1`, whereas this repository uses `v4.33.0`;
thus direct dependency admission fails the toolchain-equality requirement.
The local port retains the reduced Newton result, with its normalization
prerequisites internal to the proof. The full Apache license, all source
copyrights, immutable source hashes, modifications, and the condition for
retirement at this repository's future Mathlib pin are preserved in
`tao2026newton.md`. The toolchain and dependency pins are unchanged.
The GitHub issue/PR query `repo:leanprover-community/mathlib4 Newton inequality`
returned seven entries (`incomplete_results=false`); these are a bounded
API search, not all third-party Lean libraries.

For prior resolutions, OpenAlex's title query `Order polytopes of crown posets`
returned 44 indexed matches; the first 25 metadata records were inspected.
The narrower query `crown order polytope log concavity` returned eight
records, all inspected at metadata level. Neither inspected result set
identified an exact resolution. The two indexed records for the journal
DOI, `W4416118597` and `W7125216265`, had zero results in their combined
citing-work query. That zero is not a reliable absence claim:
[arXiv:2607.22767v1](https://arxiv.org/abs/2607.22767v1),
*Greedy Records and Bernstein Transfers for Fence and Circular-Fence Order
Polynomials* (the HTML title; the index reverses the first two phrases),
was found in the title search and its full HTML explicitly
cites the Crown paper as reference 12. Its inspected abstract and circular
section concern coefficients of order polynomials and Kahane's circular-fence
conjecture. The text searches for `log.concav` and `f.vector` each returned
zero matches; no resolution of the present geometric conjecture was found
in that inspected text. Its HTML SHA-256 is
`28c982cfc8a368137dec0de30d942263951843a042b7b0e2528eabdb0fd022ac`.

The inspected primary v3 still labels the target a conjecture. The public
refresh above establishes only bounded findings: other title-search hits
were not all read in full, and worldwide priority remains unverified.
The metadata searches do not rule out an unindexed proof or a resolution
inside a work with a different title. The caller identifies issue 8670
as preregistration and PR 8714 as publication context; their remote contents
and chronology were not reverified in this artifact-only lane. Full
pre-freeze native reviews, including source fidelity and the Newton
license, are approved. Their bounded literature findings do not establish
worldwide priority; final artifact review and publication remain pending.
