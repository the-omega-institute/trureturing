---
bibkey: doumas2025fibonacciredheffer
authors: Aristides V. Doumas; Panayiotis J. Psarrakos
year: 2025
title: The Fibonacci--Redheffer Matrix and its Properties
doi: null
url: https://arxiv.org/abs/2511.13627v3
claim: The preprint studies a Redheffer matrix weighted by Fibonacci entries, with determinant equal to a Fibonacci factorial times a truncated Mobius sum; it does not supply a Robin estimate or an RH proof.
strata_touched: []
license: citation-only
triage: anchor
---

# The Fibonacci--Redheffer matrix

The inspected source is [arXiv:2511.13627v3](https://arxiv.org/pdf/2511.13627v3),
submitted 17 November 2025 and revised 27 September 2026. The statements below
are attributed to that version; the proof and numerical asymptotics were not
independently audited here, and no Lean verification is claimed.

For $n\ge3$, the source defines a matrix with Redheffer divisibility support and
Fibonacci weight $F_i$ on the entry in row $i$ whenever $i\mid j$. Its
determinant is

$$
\det(FR(n))
 =\left(\prod_{j=1}^{n}F_j\right)
   \sum_{k=1}^{n}\frac{\mu(k)}{F_k}.
$$

The paper proves that the displayed partial sums are negative for $n\ge3$ and
converge rapidly to a negative constant. More generally, for a positive weight
sequence $(a_j)$, Theorem 21 gives the determinant factor
$1+\sum_{k=2}^{n}\mu(k)/a_k$. It equals
$\sum_{k=1}^{n}\mu(k)/a_k$ when $a_1=1$, as in the Fibonacci
specialization; the general statement does not assume that normalization.

## Boundary for the FIB--Robin route

This is a genuine historical intersection of Fibonacci weights, divisibility
support, and the Möbius function. It is a finite matrix identity, however, and
its convergent weight $1/F_k$ is not the Robin weight $1/k$ or the complete
divisor average $\sigma(N)/N$. The source gives no map from a five-window FIB
address or from $N_g=1+F_rg$ to the matrix index $n$ that would preserve the
required prime-power coefficients. It therefore cannot be used as a Robin upper
bound, a signed FIB residual estimate, or a proof of RH without a new
coefficient-preserving bridge.

The reusable interface is the determinant factorization: a Fibonacci-weighted
divisibility operator can expose a truncated Möbius transform. Any proposed
spectral FIB argument should state how that transform relates to the ordinary
Möbius/Robin transform before importing conclusions from this source.
