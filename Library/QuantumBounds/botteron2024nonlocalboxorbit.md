---
bibkey: botteron2024nonlocalboxorbit
authors: P. Botteron; A. Broadbent; R. Chhaibi; I. Nechita; C. Pellegrini
year: 2024
title: "Algebra of Nonlocal Boxes and the Collapse of Communication Complexity"
doi: null
url: https://arxiv.org/abs/2312.00725v3
claim: "Conjecture 15 asks whether right multiplication maximizes CHSH over every parenthesization of copies of a box in the PR-SR-I triangle."
strata_touched:
  - D5/S3/Quantum/Entanglement/NonlocalBoxOrbitRightProduct
license: citation-only
triage: anchor
---

## Verified locator

Source: https://arxiv.org/abs/2312.00725v3

Quantum 8, 1402 (2024). The supplied DOI 10.22331/q-2024-07-11-1402
returned HTTP 404 from Crossref's work endpoint; the pinned arXiv version is
the verified source locator.

## Definitions and question

The box product in Section 1, Equation (9), sums over the four internal bits,
applying the input functions and the two output indicators of a wiring.
The wiring W_BS is decoded in Section 4 as f1(x,a2) = x, g1(y,b2) = y,
f2(x,a1) = x a1, g2(y,b1) = y b1, f3(x,a1,a2) = a1 XOR a2 and
g3(y,b1,b2) = b1 XOR b2.

The source defines PR(a,b|x,y) = (1/2) 1[a XOR b = xy], P0 = 1[a=b=0],
P1 = 1[a=b=1], I = 1/4 and SR = (P0+P1)/2. CHSH is one quarter of the
sum of P(a,b|x,y) over a XOR b = xy. The set tilde A consists of boxes
in Conv{PR,SR,I} with CHSH at least 3/4. The k-orbit includes every full
binary parenthesization of k copies of P; the right product is the left-nested
product, multiplying a fresh P on the right at each step.

Section 2.1, p. 12, defines the k-orbit by the words:

> all possible products with k times the term P, using the multiplication $\boxtimes_W$.

Theorem 13, p. 16, gives maximality in the tilted orbit under its distillation
hypothesis. Conjecture 15 (Dyck paths), p. 16, states verbatim:

> We conjecture that the same result actually holds without the tilde, i.e. the right multiplication $P^{\boxtimes k}$ gives the highest CHSH-value of $\mathrm{Orbit}^{(k)}(P)$, as observed numerically.

The Lean encoding uses Fin 2, with addition and multiplication modulo two,
and orders the arguments as P a b x y. The definition claim retains the
source domain tilde A and k >= 2, and drops the distillation hypothesis.
The theorem whole_triangle_max proves the bound for every box of the whole
triangle and every orbit depth; result specializes it to claim. The value
rightPow P 0 is P, while the zero-leaf orbit is empty.

## What the proof shows

Proved in the module: the explicit polynomial coordinate product admits a
closed invariant region. Its associator has a nonnegative second-coordinate
gap, and multiplication on the right preserves second-coordinate order when
the first coordinates agree. Structural induction straightens every tree to
the left-nested right product without decreasing CHSH. The bound needs neither
CHSH >= 3/4 nor the distillation hypothesis of Theorem 13.

Computed: the experiment entry
[check.py](https://github.com/the-omega-institute/trureturing-experiments/blob/176b380e9ff17530e14ceb4b896e5cc65fd1f57f/docs/reports/botteron-et-al-2024-nonlocal-box-orbit-right-product/check.py),
sha256 6f31d58efed171fec57acefa680b3d08e2d37f6a97429e9ecdae433a9007e2fc,
was run as `python3 check.py`, exit 0, `bad= 0`. This is finite computational
evidence, separate from the universal Lean theorem.

Open: other wirings, boxes outside the triangle, and an explicit formula for
the exact maximum CHSH value as a function of k. Maximality alone does not
assert that every such box distills or collapses communication complexity.
