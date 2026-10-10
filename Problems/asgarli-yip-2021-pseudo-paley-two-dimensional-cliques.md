---
slug: asgarli-yip-2021-pseudo-paley-two-dimensional-cliques
bibkey: asgarli2021pseudopaley
doi: 10.48550/arXiv.2110.07176
url: https://arxiv.org/abs/2110.07176v5
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.result
---

# Asgarli–Yip two-dimensional pseudo-Paley cliques

## Problem

Conjecture 5.9 of S. Asgarli and C. H. Yip, “The subspace structure of maximum cliques in pseudo-Paley graphs from unions of cyclotomic classes”, arXiv:2110.07176v5 (2024), asks for the classification of two-dimensional cliques containing $1$ in $PP(p^4,p+1,I)$:

> Let $V$ be a $2$-dimensional subspace in $mathbb F_{p^4}$, such that $1\in V$. Then $V$ is a clique in $PP(p^4,p+1,I)$ for some $I$ if and only if $V=\mathbb F_p\oplus a\mathbb F_p$, where $a=g^{(p+1)k}$ and $k$ is odd.

The formal convention is `GaloisField p 4`, with `ZMod p` as the prime field, `cyclotomicClass`, `connection`, and `PP` as defined in the settling module. The quantified claim ranges over odd primes, primitive roots, two-dimensional subspaces containing $1$, and index sets contained in `Finset.range (p+1)` with cardinality $(p+1)/2$.

## Motivation

The source leaves Conjecture 5.9 open after a finite verification. The settling declaration is
`D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.result`, and its Scribe node records the proved open-problem resolution for this dossier. The source’s Proposition after Conjecture 5.9 counts $(p^2+1)/2$ subspaces; the finite count below agrees with that statement, while the Lean result supplies the classification and not a separate general counting theorem.

## Gap

Issue [#14878](https://github.com/the-omega-institute/trureturing/issues/14878) preregistered the source statement, conventions, route and criteria. The pinned v5 source states Conjecture 5.9 and does not give a universal proof. The related Xiong–Yip result, arXiv:2604.04126v1, Theorem 1.8 and Corollary 1.9, assumes $q\equiv-1\pmod d$; here $q=p^2$ and $d=p+1$ give $q\equiv1\pmod d$, so it does not supply this classification.

The source-bound escape audit is unfinished under [#14979](https://github.com/the-omega-institute/trureturing/issues/14979). The delivered head carries no registration for the public theorem targets. Their DTR verdict is `DTR-Unregistered`; the missing evidence is a decodable, faithful typed registration with enrolled-template binding for each target. This audit status does not alter the kernel-checked settlement.

## Route

For $N=(p^2+1)(p-1)$, use $\chi(x)=x^N$. Write a plane containing $1$ as $\mathbb F_p\oplus b\mathbb F_p$ and parameterize its projective line by $\infty\mapsto1$ and $t\mapsto b+t$. The norm power

$$
Q_b(t)=(b+t)^{p^2+1}=t^2+(b+b^{p^2})t+b^{p^2+1}
$$

lands in the quadratic subfield. Equal classes give the cross-product equation for two affine parameters. Its nonconstant quadratic fiber has at most two points, and the infinity fiber has at most one affine point. A clique uses at most $(p+1)/2$ classes, so every projective fiber is a pair. The mate of infinity gives $a=g^{(p+1)k}$; the projective mate map is $t\mapsto C/t$ with $C=a^{p^2+1}$ and exchanges $0$ and $\infty$. Its fixed points are the square roots of $C$. The parity criterion makes $C$ a square exactly when $k$ is even, so precisely the odd indices yield the required fixed-point-free pairing and the classification.

## Falsifier

A counterexample would be an odd prime, primitive root, admissible two-dimensional subspace and index set satisfying the formal hypotheses while violating the stated equivalence. The proof does not classify the source’s Conjectures 1.4, 5.6, or 5.8, higher-dimensional cliques, or other divisors $d\mid q+1$.

## Evidence

The source module and Scribe mirror are
`D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.lean` and
`Blueprint/D5/S3/Combinatorics/PseudoPaley/TwoDimensionalCliques.scribe.cs`; the emitted document is at the matching `.md` path. The Freeze event is `sha256:86e92ea23cd9f0caf572e881c076022ce8abcb2fd48783985e457cc81f7704ea` and has no prerequisite frozen node. The state pin is `sha256:eb1a0068db8f893273d99666c1f171780f8a406d23c6b999e83526a6565c9a6a`.

The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. No `sorry` or additional axiom is used. The module has admission basis `open-problem-resolution (#14878; Proved)` and utility `none`. All non-settling helpers are consumed bind-only helpers; the settling result is the sole result declaration.

The numerical reading is the experiment entry [`check.py`](https://github.com/the-omega-institute/trureturing-experiments/blob/12835f31559db7e776a6d1c75f2fe05c89e1b259/docs/reports/asgarli-yip-2021-pseudo-paley-two-dimensional-cliques/check.py), pinned to commit `12835f31559db7e776a6d1c75f2fe05c89e1b259`, SHA-256 `4c1c5a9ef3fa872513d822230bde1adac20d87a0427ba4aa5bf1d95b420ab56e`. Command `python3 check.py 3 5 7` exits $0$ and reads $(p^2+1)/2$ cliques: $5$ for $p=3$, $13$ for $p=5$, and $25$ for $p=7$.

## Triage

### What the settlement shows

- **Proved:** the map induced by $\chi$ on the $p+1$ projective points is nonconstant with degree-two affine fibers, so every class meets the projective line in at most two points. This is the mechanism formalized by `projective_fiber_card_le_two`.
- **Proved:** cliquehood forces all fibers to be pairs and forces $V=\mathbb F_p\oplus a\mathbb F_p$ with $a=g^{(p+1)k}$. The settling result supplies the complete equivalence.
- **Proved:** the fibers for the selected generator are the orbits of $t\mapsto C/t$ with $C=a^{p^2+1}$, and the parity of $k$ decides whether $C$ is a square and singleton fibers occur. Odd $k$ gives the clique and even $k$ is excluded.
- **Computed:** the number of cliques is $(p^2+1)/2$ in the tested scope $p\in\{3,5,7\}$. The command, exit code and script SHA-256 are recorded in Evidence above; a uniform counting theorem beyond the tested scope remains open.
- **Literature:** Xiong–Yip arXiv:2604.04126v1, Theorem 1.8 and Corollary 1.9, do not cover this congruence case $q\equiv1\pmod{p+1}$.
- **Open:** the source’s Conjectures 1.4, 5.6, and 5.8 are not addressed by this settlement; Proposition 5.7 is a separate density proposition.
- **Open:** classification by the degree-two class-map method for $PP(q^2,d,I)$ with other $d\mid q+1$ remains open.
- **Open:** higher-dimensional cliques remain open.
- **Open:** Proposition 5.10 states that Conjectures 1.4, 5.6, and 5.9 together imply Conjecture 5.8. After this settlement of Conjecture 5.9, that implication remains conditional on Conjectures 1.4 and 5.6.

## ASSUMED-UNVERIFIED

The literature non-settlement reading is bounded to the source and searches recorded in issue #14878; it is not an exhaustive priority certificate. The finite computation tests only $p=3,5,7$. Conjectures 1.4, 5.6, and 5.8, other divisors and higher-dimensional cliques remain outside this result. The escape audit remains unfinished at #14979 with `DTR-Unregistered` observations and missing registration evidence.
