---
bibkey: benedettimenara2026diameter
authors: Bruno Benedetti and Giuliamaria Menara
year: 2026
title: Diameter bounds for complexes that are close to flag or close to normal
doi: 10.48550/arXiv.2611.08071
url: https://arxiv.org/abs/2611.08071v1
claim: "Question 9.1 asks whether normality, the gap condition G_k and unchanged pure dimension force the flag completion to be normal for k >= 2."
strata_touched:
  - D5/S3/Combinatorics/SimplicialComplexes/BenedettiMenaraNormalityRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2611.08071

Source: https://arxiv.org/abs/2611.08071v1

## Question 9.1

On page 21, Section 9, the source asks:

> In Main Theorem A with k ≥ 2, does normality of Δ̂ follow from normality of Δ together with (Gₖ) and purity of Δ̂? (For k ≤ 1 it does, by Proposition 3.5.)

```tex
In Main Theorem~\ref{thm:A} with $k\ge2$, does normality of $\Chat$ follow from normality of $\Delta$ together with $(\mathrm G_k)$ and purity of $\Chat$? (For $k\le1$ it does, by Proposition~\ref{prop:normalhat}.)
```

Here `\Chat` denotes the flag completion, `thm:A` is Main Theorem A and
`prop:normalhat` is Proposition 3.5.

## Definitions and scope

Page 1 defines normality:

> The question is typically asked for normal complexes, i.e. complexes Δ where for every face σ, including the empty one, the facets containing σ induce a connected subgraph of 𝒢(Δ).

```tex
The question is typically asked for \emph{normal} complexes, i.e. complexes $\Delta$ where for every face $\sigma$, including the empty one, the facets containing $\sigma$ induce a connected subgraph of $\G(\Delta)$.
```

Page 2 defines the completion:

> Let now Δ̂ be the flag completion of Δ, that is, the clique complex of its 1-skeleton.

```tex
Let now $\Chat$ be the \emph{flag completion} of $\Delta$, that is, the clique complex of its $1$-skeleton.
```

Page 2 states the gap condition:

> Δ has no minimal nonfaces of size 3, 4, …, d − k.

The source explicitly includes k=d-2, for which the condition is vacuous. Page 7 states:

> Throughout, Δ is a (finite) pure simplicial complex of dimension d − 1 on a vertex set V with |V| = n.

> The dual graph 𝒢(Δ) has the facets of Δ as nodes, and its edges join facets that are adjacent, i.e. that share exactly d − 1 vertices; diam(Δ) is its diameter.

Purity of dimension d-1 means every inclusion-maximal face has d
vertices. The formal encoding uses nonempty Mathlib faces and the existing
augmented-face predicate for the empty face; all vertices are present.

Proposition 3.5 preserves normality in the G_1 range. Main Theorem A assumes
normality of the completion explicitly, so a negative answer to Question 9.1
does not refute that theorem or its diameter bound.

The ten-vertex refutation uses d=4 and k=2. Its completion adds the tetrahedron
{6,9,3,4}; the face {6,9} then lies in two tetrahedra with no dual edge between
them. The uniform family for all N>=6 and preservation under a nonvacuous G_k
with 2<=k<d-2 are separate questions.

The exact finite experiment is in the-omega-institute/trureturing-experiments,
commit 16cfc9c75399bfdb5b7d96f4e0b890a3b1c6743b,
`docs/reports/benedetti_menara_q9_1_normality_flag_completion/check.py`, SHA-256
`f6fd9d203346fb40318c74b9ec30611d27140309bcf56610988eb661efb1a48e`.
The preregistration reports exit 0 and `ALL_CHECKS_OK` for 6<=N<=24. These
finite experiments do not prove a uniform family theorem.

Literature completeness is ASSUMED-UNVERIFIED. The bounded screen recorded in
issue #29020 did not identify an external settlement. AFTD and CoPEER program
sources were excluded because no compatible code licence was established.
