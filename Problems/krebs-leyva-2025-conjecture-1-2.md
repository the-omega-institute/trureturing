---
slug: krebs-leyva-2025-conjecture-1-2
bibkey: krebsleyva2025ranktwo
doi: 10.48550/arXiv.2511.03028
url: https://arxiv.org/abs/2511.03028v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement.result
---

# Fixed-rank chromatic stabilization of standardized Abelian Cayley graphs

## Problem

Mike Krebs and Alejandro Leyva state Conjecture 1.2 in §1.1.3, printed
page 3 of *Chromatic numbers of rank-two Abelian Cayley graphs*,
arXiv:2511.03028v1 (CC BY 4.0). Typography is normalized in this quotation.
[Primary text](https://arxiv.org/pdf/2511.03028v1#page=3)

> Let $r$ be a positive integer. Then for all sufficiently large $m$, if
> $M_X$ is an $m \times r$ integer matrix and $X = M_X^{\mathrm{SACG}}$
> (the Abelian Cayley graph associated with $M_X$), and $M_X$ has no zero
> rows and $X$ is not bipartite and has no loops, then $\chi(X) = 3$.

### Statement echo and clause correspondence

For every natural $r>0$ there exists a natural threshold $m_0$, depending
on $r$. For every $m\ge m_0$ and every integer matrix indexed by
`Fin m` and `Fin r`, the conjecture assumes every row has a nonzero
entry, the associated graph is nonbipartite, and the same graph is
loopless. Its conclusion is chromatic number three. A threshold may be
raised to one when comparing with positive row dimensions. The source
calls the number of columns the rank, irrespective of linear
independence.

In Lean, `Matrix.mulVecLin.range` gives the integer span of the
columns and `QuotientAddGroup.mk'` takes coordinate vectors to their
cosets. The generator set is the set of both signs of those cosets.
`HasLoops` tests membership of zero. `IsBipartite` requires
looplessness and Mathlib two-colorability. `chromaticNumber` is
infinity on a looped source graph and is Mathlib's extended chromatic
number of the simple Cayley graph otherwise. These definitions give a
graph and truth values for every matrix quantified over by `claim`.

## Motivation

Theorem 1.1 in the preprint settles the two-column case from five rows
onwards under the same premises. The paper's row-merging
homomorphisms supply upper bounds and motivate the proposed
extension to every fixed positive number of columns.

## Gap

The named assertion is in the preprint. The preregistration's
literature screen found no public settlement within its search scope.
Cervantes and Krebs, arXiv:2303.06262v2, Lemma 2.7, give a
maximum-chromatic-number formula for block-diagonal Heuberger matrices.
The present family uses a column coupling the first and additional
coordinates. [Related source](https://arxiv.org/abs/2303.06262v2)

## Route

For $k\in\mathbb N$ choose $m=4(k+1)+3$ and three columns
$e_2-2e_1$, $e_3-3e_1$, and $4e_1+\sum_{j=1}^{4(k+1)}j f_j$, where
$f_j$ is the $j$th additional coordinate vector. Each row has a nonzero
entry. If a standard basis vector were a column combination, its
first five row equations would force all three coefficients to vanish.
Its unit entry rules this out. In the actual quotient the two first
columns identify $[e_2]$ with $2[e_1]$ and $[e_3]$ with $3[e_1]$.
Each increasing difference among $0,[e_1],2[e_1],3[e_1]$ is a nonzero
coordinate generator. Pairwise adjacency gives a four-clique and
therefore a lower bound of four on the chromatic number.

## Falsifier

Specialize a proposed stabilization threshold to rank three, then
take $k=m_0$. This gives $m\ge m_0$ and one matrix satisfying all
three source premises. Chromatic number at least four contradicts
the claimed equality. The compiled result has literal type
`Not claim`.

## Evidence

- The preprint's title, exact statement and matrix-to-graph definitions are
  anchored in the Library note `krebsleyva2025ranktwo`.
  [Preprint](https://arxiv.org/pdf/2511.03028v1#page=3)
- The Tier 1 open-problem-resolution target and probe were preregistered
  for the whole conjecture.
  [Issue #31850](https://github.com/the-omega-institute/trureturing/issues/31850)
  [Forecast](https://github.com/the-omega-institute/trureturing/issues/31850#issuecomment-7056408054)
- The typed Blueprint resolution names
  `D5/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement.result`.
  Its mathematical proof uses the signed-coordinate quotient of the
  same matrix that witnesses the premises.

## Triage

`theorem` with outcome **refuted** for Conjecture 1.2 in arXiv version 1.

### What the settlement shows

**Proved** by `D5/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement.result`
and its live family construction. The row count can grow without bound
at rank three while three coordinate steps still generate a four-clique.
The absence of zero rows leaves this obstruction possible.

**Literature-attested.** The rank-one and rank-two special cases are
covered by Theorems 1.9 and 1.1 of the preprint, respectively. The
rank-three obstruction is compatible with the row-merging
homomorphism theorem. The discussion in §1.1.3 uses the earlier
theorems to motivate the conjecture. [Preprint](https://arxiv.org/pdf/2511.03028v1)

**Open here.** An exact chromatic upper bound for this family, a
replacement stabilization statement at rank three, and a
classification of rank-three square matrices are outside the
certified conclusion.

## ASSUMED-UNVERIFIED

The publisher PDF endpoint serves subscription-preview HTML. The
journal body, its conjecture wording and its disposition of the
question remain unverified. The bounded literature and duplicate
screen in the preregistration covers the accessible preprint, related
papers and indexed settlement sources. The reviewed repository
snapshots contain no corresponding dossier, Library note or Lean
settlement. Priority and coverage of inaccessible or unindexed
versions remain unverified.
[Journal record](https://doi.org/10.1007/s00373-026-03080-2)
[Screen](https://github.com/the-omega-institute/trureturing/issues/31850)
