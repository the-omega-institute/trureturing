---
bibkey: skoric2021signatures
authors: Boris Škorić
year: 2021
title: Quantum digital signatures with smaller public keys
doi: 10.26421/QIC21.11-12-4
url: https://arxiv.org/abs/2012.15493v2
claim: 'Conjecture 1 in §6.2, equation (35), journal p.966 asserts that the cap-normalized mean of a truncated binomial row is decreasing in its cap.'
strata_touched:
  - D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.26421/QIC21.11-12-4

Source: https://arxiv.org/abs/2012.15493v2

Journal: *Quantum Information and Computation* **21** (2021), 955–973.
Conjecture 1 appears in §6.2, equation (35), journal p.966.

## Source statement

The source's TeX states, verbatim:

```tex
\begin{conjecture}
\label{conj:fdecreasing}
Let $f(x,r)$ be defined as
\be
	f(x,r)\isdef \frac1r\cdot \frac{\sum_{w=0}^r w{x\choose w}}{\sum_{w=0}^r {x\choose w}},
	\quad\quad r\leq \frac x2.
\ee
The function $f(x,r)$ is decreasing in~$r$.
\end{conjecture}
```

The source defines `\isdef` as `\stackrel{\rm def}{=}`. Both endpoints of
each sum are included. In the counting application, the upper argument is
the integer size `d−ℓ` of an unknown bit string.

## Mathematical reading

The Lean proposition quantifies over natural numbers `x ≥ 2` and positive
integer caps `r < s` with `2*s ≤ x`, and concludes `f x s ≤ f x r`.
The finite formula for `f` is retained, with ordinary `Nat.choose` coefficients
cast to the reals. Decrease is read as nonincrease. No interpolation in the
cap or real upper argument is asserted. Every denominator in these comparisons
is positive; the real field's totalized division at cap zero is outside the claim.

The repository proof uses positive factorially log-concave rows and convolution
block domination. Only the scalar conjecture is the public settling theorem.
Its application removes this named premise from source Propositions 1 and 2;
it does not verify their other derivations or the security analysis.

## Evidence boundary

The source and literature screen are identified in issue #24239. Literature
completeness is ASSUMED-UNVERIFIED: database omissions, unread citing material,
and the full Shanthikumar–Yao theorem's model correspondence remain unchecked.
No worldwide priority claim is made. This citation-only note incorporates no
source software.

The finite exact checks are in `the-omega-institute/trureturing-experiments`,
commit `bb743940e170f91b8b857c02220cdc6f35e8c3ea`, at
`docs/reports/skoric-truncated-binomial-mean/check.py`, sha256
`0edc1713935c3c2e946497746c197ff2b40ba9c9b50a77b69f3720c5aa954e28`.
The preregistration records command `python3 docs/reports/skoric-truncated-binomial-mean/check.py`,
exit 0, and final line `ALL_CHECKS_OK`. These are finite checks reported by
the research seat, separate from the universal Lean proof.
