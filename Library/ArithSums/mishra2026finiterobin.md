---
bibkey: mishra2026finiterobin
authors: Challenger Mishra; Rahul Sarkar
year: 2026
title: A finite arithmetic form of Robin's inequality and its equivalence to the Riemann hypothesis
doi: null
url: https://arxiv.org/abs/2609.26787v1
claim: The preprint introduces an omega(n)-truncated exponential Robin bound, proves it for several arithmetic classes, and claims equivalence with Robin's inequality; it supplies no bridge from a FIB address to a bounded distinct-prime count.
strata_touched: []
license: citation-only
triage: anchor
---

# A finite arithmetic form of Robin's inequality

The source is [arXiv:2609.26787v1](https://arxiv.org/pdf/2609.26787v1), submitted 22 September 2026. This card records the stated theorem interfaces from that version. It is a preprint; the proofs and the Appendix B computations were not independently audited here, and no Lean verification is claimed.

## The truncated criterion

For $n>5040$, put

$$
P_K(x)=\sum_{j=0}^{K}\frac{x^j}{j!},
\qquad
C_\omega(n)=e^\gamma P_{\omega(n)}(\log\log\log n).
$$

The paper calls

$$
\frac{\sigma(n)}n<C_\omega(n)
$$

the $\omega$-inequality. Since $P_K(x)<e^x$ for $x>0$, this is pointwise stronger than Robin's bound. Theorem 1 claims the inequality unconditionally for $\omega(n)\le6$ and for primorials; the paper derives the square-free and odd cases. Its Appendix B reports a finite check through $10^9$, which is source data rather than a project verification.

The same paper claims that the $\omega$-inequality is equivalent to Robin's inequality, hence to RH, and that a minimal counterexample would have initial prime support, non-increasing exponents, and be superabundant. The CA restriction is a reduction of the claimed equivalent criterion, not a proof that any CA number is a counterexample.

## Boundary for the FIB route

The truncation order is the distinct-prime count $\omega(n)$, while a FIB five-window address records additive Zeckendorf inclusion states. No statement in the source bounds $\omega(N_g)$ for the canonical FIB family $N_g=1+F_r g$, and the local labels $[null,2,3,2\,5,5]$ do not encode the prime factorization of $N_g$. Thus the $\omega\le6$ theorem cannot be applied to that family without a new arithmetic bound.

The source's superabundant/CA reduction also requires the actual integer to be an extremizer for $\sigma(n)/n$. A FIB address, a congruence $N_g\equiv1\pmod{F_r}$, or a reversible composition coordinate does not establish that extremality. The result is therefore a candidate-class filter and an alternative Robin criterion, not the missing same-price bridge or a proof of RH.
