---
bibkey: lichtman2020mertens
authors: Jared Duker Lichtman
year: 2020
title: Mertens' prime product formula, dissected
doi: null
url: https://arxiv.org/html/2002.03361v3
claim: Theorem 1.1 recalls the reciprocal-prime sum with an O(1/log x) error and the classical Mertens product asymptotic; these inputs control prime tails at two linked cutoffs.
strata_touched: []
license: citation-only
triage: anchor
---

# Mertens inputs for bounded arithmetic resolution

The inspected author version is [arXiv:2002.03361v3](https://arxiv.org/html/2002.03361v3).
Theorem 1.1 is explicitly attributed to Mertens (1874). Its equation (1.1)
includes

$$
\sum_{p\le x}\frac1p=\log\log x+\beta+O(1/\log x),
$$

and equation (1.2) states

$$
P(x):=\prod_{p\le x}(1-1/p)^{-1}\sim e^\gamma\log x.
$$

The symbol $\log_2 x$ in that source means the iterated logarithm, not the
base-two logarithm. The constant $\beta$ is the prime Mertens constant;
it is distinct from the Euler–Mascheroni constant $\gamma$.

For linked cutoffs $m<X$, subtraction of (1.1) gives

$$
\sum_{m<p\le X}\frac1p
=\log\log X-\log\log m+O(1/\log m).
$$

Replacing the summand by either $-\log(1-1/p)$ or $\log(1+1/p)$ costs
$O(\sum_{n>m}n^{-2})=O(1/m)$. Thus the reciprocal-prime estimate, including
its error term, supplies the rate needed for the factorial-congruence
comparison in FIB §§188–190. The product asymptotic alone suffices for
convergence of $P(m(\log m)^2)/P(m)$ to one, but is not used to claim a
sharper rate than its stated remainder provides.

The factorial-congruence comparison, its extremal witnesses and the FIB
near-boundary neighborhood deductions are project paper arguments using
these classical inputs. They are not assertions from Lichtman's paper,
not a priority claim, and not a formal proof of Robin or RH. No source
text or proof implementation is copied into the library.
