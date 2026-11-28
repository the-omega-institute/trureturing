---
slug: lewis-won-conjecture-3-17
bibkey: lewis2026crossword
doi: 10.48550/arXiv.2609.03081
url: https://arxiv.org/abs/2609.03081v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CrosswordGrid/LewisWonConjecture317Refutation.result
---

# Lewis–Won Conjecture 3.17 and the excluded size-three endpoint

## Problem

Lewis and Won, *Non-attacking rook placements on crossword grids*, arXiv:2609.03081v1, §3.4, printed p. 22.

> For a fixed positive integer n, the maximum value of the expression in (3.1) is obtained when m ∈ (m∗, m∗ + 2).

Equation (3.1) on p. 20 defines the objective

$$
E(n,m)=\sum_{k=1}^{m}\bigl(S(m,k)\,k^{n-2m}\,k!\bigr)^2,
$$

where $S(m,k)$ is the Stirling number of the second kind. The positive balanced sizes are the integers $m\ge1$ with $2m\le n$.
Page 21 defines the lower cutoff $x=m_*$ as the real solution with $x\ge1$ and
$n=\log(x+1)/\log(1+1/x)+2x$ for $n\ge3$.
The existential reading requires, for every such $n$ and $x$, some admissible $m$ with $E(n,j)\le E(n,m)$ for every admissible $j$
and with $x<m<x+2$. [Existing literature note](../Library/Combinatorics/lewis2026crossword.md) · [Printed pp. 20–22](https://arxiv.org/pdf/2609.03081v1#page=20)

## Motivation

The asserted interval narrows the search for a balanced block size in the rook-placement objective. At $n=3$ its left endpoint is itself
the only admissible positive size, so a strict interval excludes every possible maximizer.

## Gap

The preregistration checked the exact arXiv ID and title, v1, citing records, and relevant repositories and problem catalogues.
It found existing dossiers for other questions in the same paper. OpenAlex reported one citing record, but its citing-work endpoint
and Semantic Scholar returned HTTP 429. MathDB returned HTTP 403. The bounded search identified no prior settlement of Conjecture 3.17.
[Preregistration #34932](https://github.com/the-omega-institute/trureturing/issues/34932)

## Route

1. Set $n=3$ and $x=1$. Since $\log 2>0$, the logarithm ratio equals one and the cutoff equation holds.
2. From $1\le m$ and $2m\le3$ obtain $m=1$ for every admissible $m$. The only such size is a global maximizer.
3. The asserted strict lower bound becomes $1<1$. The formal claim encodes the complete objective, all admissible comparisons and both strict endpoints.

## Falsifier

The cutoff equation would rule out the proposed witness if $x=1$ failed at $n=3$. An admissible integer in $(1,3)$ would defeat the
admissibility argument. The pinned proof checks both conditions needed for the contradiction.

## Evidence

The Lean owner defines `claim : Prop` and proves `result : Not claim`. An independently replayed author proof verifies the same
fully expanded quantified statement, and a kernel conversion check identifies it with the owner's claim. The replay also confirms that
the cutoff is unique at $n=3$, that the score at $m=1$ is one, and that the empty sum at $m=0$ is zero. The positive and nonnegative
comparison domains give the same maximizers for $n\ge3$. The proof uses Lean 4.35.0, Mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and the axioms `propext`, `Classical.choice` and `Quot.sound`.
[Official result](https://github.com/the-omega-institute/trureturing/issues/34932#issuecomment-7225188463) · [Registered forecasts](https://github.com/the-omega-institute/trureturing/issues/34932#issuecomment-7224898395)

## Triage

`theorem`, Tier 1, `open-problem-resolution`, with computational utility `certified-instance` for the exact size-three contradiction.

- Proved. The existential strict-interval statement on the defined cutoff domain fails at $n=3$. Admitting $m=0$ does not change the maximizer.
- Proved at $n=3$. Replacing the lower strict inequality by a weak one admits $m=1$, which still satisfies the upper strict inequality.
- Source mechanism. The p. 21 comparison from $m$ to $m+1$ leads from $1$ to $2$ at this input, and the resulting size violates $2\cdot2\le3$.
  That comparison does not supply an admissible improvement at the boundary.
- Open in this result. The restriction to $n\ge4$, a general weak-endpoint variant, and the separate upper-cutoff analysis. The paper
  motivates Corollary 3.18 by the largest term of Eq. (3.1) and states it separately. This refutation concerns the location of a
  maximizing block size and leaves the corollary's lower bound outside the scope of the result.

## ASSUMED-UNVERIFIED

The preregistration's literature search has the access limits stated above. Historical priority beyond that scope remains unverified.
