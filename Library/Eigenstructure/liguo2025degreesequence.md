---
bibkey: liguo2025degreesequence
authors: Wen-Jun Li; Ji-Ming Guo
year: 2025
title: "A new conjecture on Laplacian eigenvalues and degree sequence of a graph"
doi: 10.2298/FIL2513551L
url: https://www.pmf.ni.ac.rs/filomat-content/2025/39-13/39-13-22-25952.pdf
claim: "Conjecture 2.22 bounds the truncated signless Laplacian square sum by the degree sequence."
strata_touched:
  - D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.2298/FIL2513551L

Source: https://www.pmf.ni.ac.rs/filomat-content/2025/39-13/39-13-22-25952.pdf

The published version is *Filomat* 39:13 (2025), 4551–4564. Its PDF has
SHA-256 `d2ddb2139168dcf95e6973eab596c9fea8915767e589fc8e8b8a2106238492f9`.
The quotations below use the visually checked publisher-PDF transcription in issue #23307.

## Source statement

Page 4551 defines the relevant spectra and degrees:

> Let $G$ be a graph with $n$ vertices and $m$ edges, and $d_1(G)\geq d_2(G)\geq\cdots\geq d_n(G)$ be the degree sequence of $G$.

> Let $Q(G)=D(G)+A(G)$ be the signless Laplacian matrix of $G$ and $q_1(G)\geq q_2(G)\geq\cdots\geq q_n(G)$ be the signless Laplacian eigenvalues of $G$.

Page 4564 states:

> **Conjecture 2.22.** Let $G$ be a graph with degree sequence $d_1\geq d_2\geq\cdots\geq d_n$. Then
>
> $$
> \sum_{q_i\geq 2}(q_i-2)^2\leq\left(1-\frac{1}{d_1}\right)\sum_{i=1}^{n}d_i(d_i-1).
> $$

The source orders degrees and eigenvalues decreasingly. The Lean expressions use vertex
summation and a multiplicity-preserving eigenvalue multiset, since both sums are symmetric.
The printed denominator restricts the mathematical domain to positive maximum degree.
Replacing the truncated summand by $\max(q-2,0)^2$ preserves its value, including at $q=2$.
The Lean refutation uses $C_3$, whose signless spectrum is $4,1,1$ and whose degrees are all 2.
It gives the strict violation $4>3$. It does not certify the infinite cycle-family formula.

The source is cited for its definitions and conjecture; the counterexample proof is derived
in this repository. No source program or figure is included. The literature screen in #23307
found no settlement in the inspected material; its completeness is `ASSUMED-UNVERIFIED`.
