---
bibkey: asgarli2021pseudopaley
authors: Shamil Asgarli; Chi Hoi Yip
year: 2024
title: The subspace structure of maximum cliques in pseudo-Paley graphs from unions of cyclotomic classes
doi: 10.48550/arXiv.2110.07176
url: https://arxiv.org/abs/2110.07176v5
claim: Definition 1.1 defines pseudo-Paley graphs; Conjecture 5.9 classifies two-dimensional cliques containing one in PP(p^4,p+1,I); Proposition 5.10 gives a conditional implication to Conjecture 5.8.
strata_touched:
  - D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2110.07176

Source: https://arxiv.org/abs/2110.07176v5

The v5 source is *Finite Fields and Their Applications* 99 (2024), 102492. The first preprint appeared in 2021. The v5 title above differs from the initial preprint title, *Van Lint–MacWilliams' conjecture and maximum cliques in Cayley graphs over finite fields*.

## Source statements

Cyclotomic classes (p. 1):

> Let $N \mid (q-1)$. Let $C_0$ be the subgroup of $\mathbb F_q^*$ with index $N$, and let $C_1, \ldots, C_{N-1}$ be all the cosets of $C_0$, where $C_j=g^j C_0$. The sets $C_0, C_1, \ldots, C_{N-1}$ are called the $N$-th cyclotomic classes of $\mathbb F_q$.

Definition 1.1 (pp. 1–2):

> Suppose $q$ is a prime power, $d$ a positive integer such that $2d \mid (q-1)$, and $I=\{m_1, \ldots, m_d\} \subset\{0, 1, \ldots, 2d-1\}$ with $|I|=d$. Let $C_0, C_1, \ldots, C_{2d-1}$ be the $2d$-th cyclotomic classes of $\mathbb F_q$. The graph $PP(q,2d,I)$ is defined to be the Cayley graph $\operatorname{Cay}(\mathbb F_{q}^+, D)$ where $D=\bigcup_{j=1}^{d} C_{m_j}.$

Conjecture 5.9 (p. 17):

> Let $V$ be a $2$-dimensional subspace in $\mathbb{F}_{p^4}$, such that $1 \in V$. Then $V$ is a clique in $PP(p^4,p+1,I)$ for some $I$ if and only if $V=\mathbb{F}_p \oplus a\mathbb{F}_p$, where $a=g^{(p+1)k}$ and $k$ is an odd integer.

Proposition 5.10 (pp. 17–18):

> Conjecture 1.4, Conjecture 5.6, and Conjecture 5.9 together imply Conjecture 5.8.

The Proposition's proof counts $(p^2+1)/2$ subspaces of the indicated form. That count and the implication to Conjecture 5.8 are literature statements; the Lean classification does not certify a general counting theorem or prove Conjectures 1.4, 5.6, or 5.8. Proposition 5.7 is a separate density proposition.

## Encoding and scope

The formal field is `GaloisField p 4`, with prime field `ZMod p`. The cyclotomic class is the literal set of powers `g ^ (j + (p+1)*m)` for natural `m`. The graph is `SimpleGraph.fromRel` of the difference-in-connection relation. The permitted index sets lie in `Finset.range (p+1)` and have cardinality `Nat.div (p+1) 2`. A two-dimensional subspace containing one is a clique for some such set exactly when it is `Submodule.span (ZMod p) {1, g ^ ((p+1)*k)}` for an odd natural index `k`. Natural odd indices represent the same powers as odd integer indices because the generator order is even.

The class-map argument uses the norm power $(b+t)^{p^2+1}$ and its quadratic expansion. Nonconstant projective fibers have at most two points. Cliquehood forces paired fibers; the norm of the selected generator power is a square exactly when the index is even. The internal projective line is `Option (ZMod p)`, with `none` representing infinity and the mate exchanging infinity with zero.

The related Xiong–Yip theorem (arXiv:2604.04126v1, Theorem 1.8, with Corollary 1.9) assumes $q\equiv-1\pmod d$. Here $q=p^2$ and $d=p+1$ give $q\equiv1\pmod d$, so that result does not supply this classification. Its application and the absence of a prior settlement remain subject to the literature readings in the problem dossier.
