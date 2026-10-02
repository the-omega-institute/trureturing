---
bibkey: browningverzobio2024sds
authors: Tim Browning; Matteo Verzobio
year: 2024
title: "Strong divisibility sequences and sieve methods"
doi: null
url: https://arxiv.org/abs/2402.19301v1
claim: "For strong divisibility sequences, sieve bounds control the density of indices whose terms have only large prime factors; the Fibonacci specialization is an index-density result and does not give a pointwise large-prime tail for every Fibonacci term."
strata_touched: []
license: citation-only
triage: anchor
---

# Strong divisibility sequences and sieve methods

The source is [arXiv:2402.19301v1](https://arxiv.org/pdf/2402.19301v1), by Tim
Browning and Matteo Verzobio. It studies strong divisibility sequences (SDS),
with Fibonacci and elliptic divisibility sequences as examples. The statements
below are attributed to that version; no independent proof audit or Lean
verification is claimed.

Theorem 1.2 gives a lower bound for the number of indices \(n\le N\) whose
term has no prime divisor below

\[
z=\tfrac12(\log N)(\log\log N),
\]

under an eventual rank-of-apparition hypothesis \(m_p<p^\alpha\). Theorem 1.4
gives an upper bound for the same index set when almost every term has a
primitive prime divisor. For Fibonacci numbers, Corollary 1.6 records the
corresponding two-sided density scale. Theorem 1.5 shows, under its stated
density condition, that prime terms in an SDS have density zero. Theorem 1.7
also gives a lower bound for the associated Eratosthenes--Legendre sieve
product.

These are aggregate statements over indices. They do not imply the pointwise
estimate displayed as a sufficient condition in FIB §195.4,

\[
(\log j)\sum_{\substack{p>j^{5/6}\\p\mid V_j}}\frac1{p-1}\longrightarrow0
\]

on a specified parity class. A sparse exceptional set of indices is
compatible with the quoted density bounds.

The current [FIB theory](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
already supplies a different route beyond that older interface: §§199–201
contain paper conclusions for every fixed primitive seed and for explicit
slowly growing norm families. Those results retain their stated analytic
inputs and seed-dependent or restricted-uniform thresholds; they are not
Lean verification. Section 195.4 must therefore not be described as an
unresolved fixed-seed Robin theorem.

The remaining broad bridges include unrestricted changing seeds and the
same actual candidate's full divisor weight. In §233.5 the candidate is
the unique remaining integer in the specified affine residue class, not
automatically a product \(gV_j\). The sieve-density theorem supplies
neither that joint weight nor a transport between the two families.
It is retained as a historical and reusable sieve input, rather than as
a reason to repeat the fixed-seed proofs.
