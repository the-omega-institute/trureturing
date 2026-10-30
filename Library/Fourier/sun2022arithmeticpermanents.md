---
bibkey: sun2022arithmeticpermanents
authors: Zhi-Wei Sun
year: 2022
title: "Arithmetic properties of some permanents"
doi: 10.48550/arXiv.2108.07723
url: https://arxiv.org/abs/2108.07723v7
claim: "Conjecture 4.2(i), equations (4.3) and (4.4): the two absolute-difference permanent congruences for every odd prime."
strata_touched:
  - D5/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2108.07723

Source: https://arxiv.org/abs/2108.07723v7

## Source statements

Page 25, Conjecture 4.2(i), verbatim TeX (the source macros are retained):

```tex
\begin{conjecture} {\rm (i)} For any odd prime $p$, we have
\begin{equation}\label{|j-k|}\per[|j-k|]_{1\ls j,k\ls p}\eq-\f12\pmod p
\end{equation}
and
\begin{equation}\label{|j-k+1|}\per[|j-k+1|]_{1\ls j,k\ls p}\eq\f12\pmod p.
\end{equation}
```

Here `\per` denotes the permanent, `\ls` means ≤, `\eq` means ≡,
`\f12` means 1/2, and `\pmod p` means (mod p).

Page 1 defines the permanent, verbatim TeX:

```tex
The permanent of a matrix $A=[a_{j,k}]_{1\ls j,k\ls n}$ over a field is defined by
$$\per(A)=\sum_{\tau\in S_n}\prod_{j=1}^na_{j,\tau(j)},$$
where $S_n$ is the symmetric group consisting all permutations of $\{1,\ldots,n\}$.
```

## Integer encoding and proof

For `j k : Fin p`, the integer entry is
`|((j.val : ℤ) + 1) - ((k.val : ℤ) + 1) + s|`, with `s = 0` or `s = 1`.
Both casts precede subtraction and absolute value. Source indices are `j.val + 1`
and `k.val + 1`. Mathlib's `Matrix.permanent` sums `∏ i, M (σ i) i`;
transposing the product indexing, or replacing the permutation by its inverse,
gives the source's identical row-indexed sum. For an odd prime, clearing the
invertible denominator 2 gives the conjunction
`(p : ℤ) ∣ 2 * Matrix.permanent (A p 0) + 1` and
`(p : ℤ) ∣ 2 * Matrix.permanent (A p 1) - 1`.

Alternating row and column signs turn these reductions into circulants. The
prime-order fixed-point count on each permutation-weight fiber removes the
nonfixed weights in characteristic p. Fixed permutations are translations;
Fermat's identity and a telescoping alternating sum evaluate their contribution.
The prime circulant ingredient is the known Brualdi–Newman congruence
(Theorem 3.2, 1965), as identified in issue #22003; it is not claimed as new
mathematics. The entry reduction needs only odd order, while the counting step
uses primality. Part (ii) is outside this statement.

## Exact experiment

The experiment is in `the-omega-institute/trureturing-experiments`, commit
`8478b9fc028dfcf192a82eff0aa7b6b25fe0a111`, at
`docs/reports/sun-2108-conj42i-permanents/check.py`; its SHA256 is
`a549c0f6573ad0e1452dbe7719d51f6d6f7ed11d83e48917650986aed9cc4678`.
The recorded command is `python3 -u docs/reports/sun-2108-conj42i-permanents/check.py`,
exit 0, ending in `ALL_CHECKS_OK`. These finite integer computations support the
route and do not prove the universal assertion.

## Literature boundary

Issue #22003 records the original v7 text and a bounded literature screen.
Jiang–Sun's reciprocal-sum result concerns part (ii), rather than this pair.
Tao–Guo's publisher full text was unread; some search services were inaccessible.
Literature completeness and worldwide priority remain `ASSUMED-UNVERIFIED`.
