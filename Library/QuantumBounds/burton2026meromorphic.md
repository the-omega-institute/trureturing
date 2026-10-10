---
bibkey: burton2026meromorphic
authors: Simon Burton; Hussain Anwar
year: 2026
title: "Meromorphic Quantum Computing"
doi: 10.48550/arXiv.2605.06251
url: https://arxiv.org/abs/2605.06251v1
claim: "Conjecture 4.8: Any CSS code [[n,1,d]] with logical operators X^{⊗n}, Z^{⊗n} exhibits coherent error suppression O(ε^d) at z = 0, ∞, ±1."
strata_touched:
  - D5/S3/Quantum/Information/CSSMeromorphicSuppression
license: citation-only
triage: anchor
---

# Meromorphic Quantum Computing

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2605.06251

Source: https://arxiv.org/abs/2605.06251v1

## Section 4

Section 4 defines the weight enumerator

> $W_A(x,y)=\sum_{g\in A}x^{n-w(g)}y^{w(g)}$.

It introduces the meromorphic decoder and states Proposition 4.3, which relates the
decoder to the Hadamard-dual code. Theorem 4.4 gives the codeword formula

> Given CSS code $C$ with stabilizers $S_X,S_Z$ and logical operators
> $X^{\otimes n}, Z^{\otimes n}$ the meromorphic decoder of $C$ is given by
> $f(z)=W_{\langle S_X\rangle}(z,1)/W_{\langle S_X\rangle}(1,z)$.

The corollary following Theorem 4.4 is printed with the denominator
$W(1,h)-W(1,h)$; this is identically zero and is a typographical error. The
binary character-sum factorization used by the settling proof supplies the
nonzero polynomial identities required at $h=1$ and $h=-1$.

Conjecture 4.8 states:

> Any CSS code $[[n,1,d]]$ with logical operators $X^{\otimes n}, Z^{\otimes n}$
> exhibits coherent error suppression $O(\varepsilon^d)$ at the four stabilizer
> states $z=0,\infty,\pm1$.

The sentence immediately after the conjecture claims order $d-1$ zeros of the
derivative; the paper's own $[[15,1,3]]$ example has local degrees $7,7,3,3$,
so the settled statement is the lower bound by $d$.

## Appendix B

Appendix B gives the codeword derivation

> $L^\dagger\binom{x}{y}^{\otimes n}=\binom{W_{\langle S_X\rangle}(x,y)}{W_{L_X\langle S_X\rangle}(x,y)}$.

For the binary conventions in the settling module, the denominator is the sum of
$z^{w(g)}$ over $g\in G_X$ and the numerator is the sum of
$z^{w(g+1^n)}$ over the same stabilizers.
