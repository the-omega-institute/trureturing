---
slug: brown-mol-2018-conjecture-4-2
bibkey: brownmol2018subtree
doi: null
url: https://arxiv.org/pdf/1810.08655v1#page=14
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/SubtreePolynomial/BrownMolConjecture42Refutation.conjecture42_false
---

# Brown–Mol Conjecture 4.2

## Problem

For every finite tree $T$ of order $n\ge2$ and every complex root $z$ of
its subtree polynomial, the conjectured annulus is
$1/2\le |z+1/2|\le 1/2+(n-1)^{1/(n-1)}$. The polynomial counts nonempty
connected induced vertex sets by size. [Brown and Mol, Conjecture 4.2, p. 14](https://arxiv.org/pdf/1810.08655v1#page=14) · [Jin, Ma and Wang, Conjecture 5.1, p. 16](https://arxiv.org/pdf/2608.07898v2#page=16)

## Motivation

Issue #34339 preregisters the tree and root certificate.
[Preregistration #34339](https://github.com/the-omega-institute/trureturing/issues/34339)

## Gap

Brown and Mol report verification through order 18.
Jin, Ma and Wang's Theorem 1.3 proves the
separate origin-centered upper bound $|z|\le 1+(n-1)^{1/(n-1)}$.
[Preregistration #34339](https://github.com/the-omega-institute/trureturing/issues/34339) · [Jin, Ma and Wang, Theorem 1.3, p. 3](https://arxiv.org/pdf/2608.07898v2#page=3)

## Route

1. Use a hub, 41 branch centers and four leaves per center. The connected induced
   sets give $P_T(z)=zF(z)$ with $F(z)=(1+z(1+z)^4)^{41}+41(4+(1+z)^4)$.
2. Set $D=1000$, $C=-539+496i$ and $S=D^{205}$. For
   $N(h)=S F((C+h)/D)=\sum_{k=0}^{205} a_k h^k$, the analytic bounds use
   $O(205)$ coefficient work after convolution. The inclusive estimates are
   $1000|a_0|\le2537S$, $5225S\le1000|a_1|$ and
   $1000\sum_{k=2}^{205}2^k|a_k|\le425S$.
3. On the boundary of the square $[-1,1]+i[-1,1]$, use
   $1\le |h|\le2$ and $2537+425<5225$ in the pinned rectangle zero-count
   theorem. The comparison polynomial $a_1h$ has one simple zero there.
4. Transfer a zero of $N$ to a zero of $P_T$ at $z=(C+h)/D$.
   Since $|C+500|<498$, the exact bound $|z+1/2|<1/2$ follows.

## Falsifier

An invalid tree, an incorrect connected-set count, or a failure of the strict
inner inequality would invalidate the witness. Lean checks the tree and its
order, the subset polynomial identity, and the existence of its root in the
strict inner disk.

## Evidence

`BrownMol.Conjecture42 : Prop` states both annulus bounds.
`BrownMol.conjecture42_false : Not BrownMol.Conjecture42` settles the claim
by violating the inner bound. The proof leaves the outer annulus bound
as a separate question.

## Triage

Tier 1 source conjecture. The settling declaration is linked as
`ResolutionKind.Refuted` in the Scribe definition.

## ASSUMED-UNVERIFIED

The cited source check covers the identified preprint versions. Worldwide
priority and the status of the translated outer bound fall outside that check.
