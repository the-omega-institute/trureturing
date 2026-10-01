---
bibkey: abbott2015reconstruction
authors: John Abbott
year: 2015
title: "Fault-Tolerant Modular Reconstruction of Rational Numbers"
doi: null
url: https://arxiv.org/abs/1303.2965v2
claim: "Theorem 3.1 with no bad modulus gives unequal-height rational reconstruction from one exact composite modulus and identifies the last continued-fraction approximant below the denominator cutoff."
strata_touched: []
license: citation-only
triage: anchor
---

# Exact-modulus specialization of Abbott's reconstruction theorem

The inspected source is [arXiv:1303.2965v2](https://arxiv.org/pdf/1303.2965v2),
submitted 21 July 2015; the manuscript title page bears 1 May 2015.
The following locator refers to the manuscript's printed pagination.
Only the stated interface is used, without a claim of Lean verification or
an independent audit of the complete paper.

Theorem 3.1, p.4, takes $X\in\mathbb Z$, $M\ge2$, positive integer bounds
$P,Q$, and $M=M_{\rm good}M_{\rm bad}$ with
$2PQ M_{\rm bad}^2<M$. It reconstructs a rational $p/q$ satisfying
$|p|\le P$, $1\le q\le Q$, and $p\equiv qX\pmod{M_{\rm good}}$.
Use only the exact-modulus case $M_{\rm bad}=1$ here. A rational is represented
in lowest terms, and its denominator is a unit modulo $M$ in this case.

For a nonzero reconstructed numerator, let $R/S$ be the last continued-fraction
approximant to $X/M$ with denominator at most $Q$. The theorem gives

$$
\frac pq=X-M\frac RS,
\qquad q_{\rm next}>\frac{M}{2|p|}.
$$

Existence remains conditional: the theorem does not state that every residue
has a bounded rational lift. The standard corrected RR algorithm in
[Monagan's source](monagan2004reconstruction.md) supplies the finite
reconstruction-or-failure procedure.

For the [FIB host interface](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
substitute

$$
(X,M,P,Q,p,q)=(n_y,V,W,U,v,u).
$$

If a reduced positive $v/u$ exists, its associated $k/u$ is the last
convergent of $n_y/V$ with denominator at most $U$, with

$$
n_yu-kV=v,\qquad q_{\rm next}>V/(2v)\ge V/(2W)>U.
$$

The application's condition $v\mid n_y$ must be tested separately. Neither
the existence of this modular fraction nor its unique retrieval proves
that the resulting whole host has a low-loss divisor or satisfies Robin.
The fault-tolerant variants and bad-modulus heuristics are not used.
