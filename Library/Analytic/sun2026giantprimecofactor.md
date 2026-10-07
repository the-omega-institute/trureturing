---
bibkey: sun2026giantprimecofactor
authors: Wen Sun
year: 2026
title: "Tilting Billingsley's model toward a giant prime: two phase transitions"
doi: null
url: "https://arxiv.org/abs/2609.11735v1"
claim: "The preprint states an exact largest-prime/cofactor decomposition and uniform positive weighted prime estimates; its Gibbs cofactor law does not supply a bound for the actual signed Fibonacci Newton panel."
strata_touched: []
license: citation-only
triage: anchor
---

# Largest prime factors and uniform cofactor estimates

The primary version is [arXiv:2609.11735v1](https://arxiv.org/abs/2609.11735v1),
published 2026-09-10. The inspected original PDF has 25 pages and SHA-256
e9be86b82cd746552bd69a1f383df604ec8df3ab8d3648f9eafd7721b0c3d814.
The arXiv record supplies no DOI or journal reference. The abstract, model
conditions, and selected statements and proofs in Section 3 were read;
the complete paper was not independently audited or formalized. No source
text or PDF is vendored.

The model uses positive parameters \(\theta,\beta>0\), \(\gamma\ge0\), and
positive weights

\[
d_\theta(n)\exp\{\beta H_\gamma(n)\}.
\]

For \(\gamma>0\), Theorem 2.2 concerns the total variation approximation of the cofactor
\(n/P^+(n)\) by a normalized positive Euler-product law. Its parameter
\(\theta\) is not the FIB volume's cofactor cutoff exponent.

On printed page 9, Lemma 3.2 expresses the sector \(P^+(n)>\sqrt x\) as the
exact disjoint prime/cofactor sum

\[
Z_x^>=\theta\sum_{m<\sqrt x}d_\theta(m)
\left[A(x/m)-A(\sqrt x)\right],
\qquad
A(y)=\sum_{p\le y}e^{\beta(\log p)^\gamma}.
\]

Printed pages 10–12, Lemma 3.3, use classical PNT and Stieltjes integration
to estimate \(A(y)\); its error is uniformly small for \(y\ge Y\) as
\(Y\to\infty\). Printed page 12, Lemma 3.4, gives specified uniform ratio
limits for the same positive weight, including compact multiplicative
ratios when \(0<\gamma\le1\).

These tools organize a joint prime/cofactor range. They are reused as
literature context for [the FIB volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§396. The positive probability law is not instantiated with the signed
sequence \(e=\mu*\beta\), and the source's exponential prime weight is not
the FIB Newton kernel. The actual signed logarithmic moment and remainder
estimate must be supplied separately. No exact theorem covering that entire
FIB interface was identified in the inspected sections; this is not an
exhaustive literature search or an originality claim.
