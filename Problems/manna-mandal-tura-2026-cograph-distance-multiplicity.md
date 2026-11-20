---
slug: manna-mandal-tura-2026-cograph-distance-multiplicity
bibkey: mannamandaltura2026cographdistance
doi: null
url: https://arxiv.org/pdf/2611.06981v1#page=22
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/Cographs/CographDistanceMultiplicity.result
---

# Equality in the distance multiplicity bound for connected cographs

## Problem

Pallabi Manna, Santanu Mandal and Fernando C. Tura ask in Open Problem 14.2(ii)
of *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*,
arXiv:2611.06981v1, p. 22

> Characterize the connected cographs for which $m_G(\lambda)=\nabla(G)$ for some $\lambda\ne -1,-2$, and give an explicit infinite family attaining the bound of Theorem 6.4.

The pinned arXiv version is available under CC BY 4.0.
[Published statement](https://arxiv.org/pdf/2611.06981v1#page=22) ·
[Bibliographic record](../Library/QuadraticForms/mannamandaltura2026cographdistance.md) ·
[arXiv rights metadata](https://arxiv.org/abs/2611.06981v1) ·
[License text](https://creativecommons.org/licenses/by/4.0/) ·
[Registered statement](https://github.com/the-omega-institute/trureturing/issues/32326)

| Source clause | Lean counterpart |
| --- | --- |
| Every finite connected cograph | A finite native vertex type, a connected simple graph and exclusion of an induced four-vertex path. Connectedness supplies nonemptiness and admits the singleton. |
| Ordinary distance multiplicity $m_G(\lambda)$ | `distanceMultiplicity G λ` is the real nullity of the shifted shortest-path distance matrix. Its real symmetry identifies this dimension with spectral multiplicity. |
| Vicinal width $\nabla(G)$ | `width G` is the least chain-cover size for $N(u)\subseteq N[v]$. `dilworthNumber_eq_width` identifies it with the existing extended-natural width. |
| A real shift other than −1 and −2 | `Eligible λ` imposes both exclusions. Positive width makes equality witness a genuine eigenvalue. |
| Characterize all attaining graphs | The left part of `result` is an equivalence with the width-one branch and the normalized join-root criterion at a real guard root. |
| Give an explicit infinite attaining family | The right part of `result` supplies $K_{3(s-1)}\vee (K_{s,s}\sqcup s K_1)$ at $\lambda=s-2$ for every integer $s\ge2$. The orders $6s-3$ give infinitely many isomorphism classes. |

## Motivation and literature

Theorem 6.4 gives the eligible multiplicity bound. Lou–Lin gives the bound,
Du gives fixed-shift distance diagonalization, Ghorbani treats the adjacency
bound and complement width, and the distance-join formulas give the family
quotient. The bounded literature check in the preregistration found neither
the join-root equality criterion nor the clique parameter locus in the
sources examined. The full texts of Lou–Lin and Du were unavailable in that
check. Literature completeness beyond that scope is ASSUMED-UNVERIFIED.
[Survey, §6](https://arxiv.org/pdf/2611.06981v1#page=14) ·
[Preregistration and literature scope](https://github.com/the-omega-institute/trureturing/issues/32326)

## Characterization

A singleton attains at zero. Every connected cograph of width one attains,
using a positive distance eigenvalue in the nonsingleton case. The
distance matrix in that case is nonzero, symmetric and traceless, so its
spectrum has a positive member.

For width above one, use the normalized cotree of connected-component and
complement-component cuts. The root is a join. Equality at an eligible
shift requires exactly one internal root child and $\ell>0$ root leaves,
which are the universal vertices. The internal child has nullity one
below its width and admits the scalar response $g$ with
$1+g-\ell/(\lambda+1)=0$. These conditions also suffice.

The local operator is $(2-q)J-(\lambda+2)I-A$ with parent label $q$,
where join has label one, union has label two and the root uses zero.
The rank-one update carries the nullity and either a nonzero sum on the
kernel or the scalar response to the all-ones vector. The three possible
updates are checked at the common real shift, including poles and
coincident roots. Integer guard polynomials are monic of subtree-size
degree. The union of their real roots contains every attaining shift,
has cardinality bounded by the sum of the distinct guards' degrees, and
can be filtered by eligibility and exact recursive nullity. Executable
real-root isolation and a complexity bound are outside this result.

## Explicit family

In $K_r\vee(K_{s,s}\sqcup bK_1)$ with $r,b>0$ and $s\ge2$, the fixed
shift $s-2$ has multiplicity two precisely when
$b(r-2(s-1))=s(s-1)$ over the integers. The four distance cells reduce
the full kernel to two coordinates subject to one scalar residual
equation. The chain cover by two chains and incomparability between the
two bipartite parts give width two. Taking $r=3(s-1)$ and $b=s$ gives
equality at the eligible shift $s-2$, with order $6s-3$.

## Evidence

The typed `OpenProblemResolutionClaim` with resolution `Proved` is
attached to `CographDistanceMultiplicity.result`. It consumes the native
`distanceMultiplicity_attains_iff` and `UniversalCliqueCographDistance.family`.
The family kernel and the classifier's Euclidean kernel have equal real
dimension via the coordinate linear equivalence. The per-shift finite
candidate statement is `distanceMultiplicity_guard_candidates`.
