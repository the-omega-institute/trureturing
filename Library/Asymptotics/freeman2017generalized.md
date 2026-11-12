---
bibkey: freeman2017generalized
authors: David M. Freeman
year: 2017
title: Generalized Palindromic Continued Fractions
doi: 10.1216/RMJ-2018-48-1-219
url: https://arxiv.org/abs/1604.06755v2
claim: Conjecture 7.1 asserts an upper bound of one divided by the golden ratio for the upper-limsup density of non-eventually-periodic m-palindromic sequences.
strata_touched:
  - D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1216/RMJ-2018-48-1-219

Source: https://arxiv.org/abs/1604.06755v2

The quotations and page numbers below refer to arXiv v2. The DOI identifies the
journal publication in Rocky Mountain Journal of Mathematics 48(1), 219–236.
The journal text is unread; its agreement with the arXiv limit convention is
ASSUMED-UNVERIFIED.

## Source statements

Conjecture 7.1 (page 10): “For $m\in\mathbb{N}$ and $A\in\mathbb{N}^{\mathbb{N}_0}$ an $m$-palindromic sequence that is not eventually periodic, we have $d_m([A])\leq1/\varphi$. Furthermore, for $r,s\in\mathbb{N}$ with $r\not=s$, we have $d_m([F(m,r,s)])=1/\varphi$.”

Section 2 (page 2): “Given $i\in\mathbb{N}_0$, a (rational) continued fraction is denoted by $[a_0,a_1,\dots,a_i]$, where $a_0\in\mathbb{N}_0$ and, for each $k$ such that $1\leq k\leq i$, we have $a_k\in\mathbb N$.”

Section 2 (page 2): “For $A\in\mathcal{A}^*$, we write $|A|$ to denote the number of terms in $A$, and say that $A$ has length $|A|$.”

Section 2 (pages 2–3): “Given $A=(a_0,\dots,a_i)\in\mathbb{N}^*$, the reversal of $A$ is defined as $\widetilde A = (a_i,\dots,a_0)$. If there exists a number $m\in\mathbb{N}$ such that $[A]=m[\widetilde{A}]$, we say that $A$ is an $m$-palindrome, or $m$-palindromic.”

Section 2 (page 3): “In the case of an irrational continued fraction $\alpha=[A]=[a_0,a_1,\dots]$, we say that $\alpha$ (equivalently, $A$) is an $m$-palindrome, or $m$-palindromic, if there exist infinitely many indices $i$ for which the prefix $(a_0,\dots,a_i)$ is an $m$-palindrome.”

Section 6 (page 8): “Given any irrational $m$-palindromic continued fraction $\alpha=[A]$, let $\{P_k(A)\}_{k=0}^{+\infty}$ denote a sequence of $m$-palindromic prefixes $(a_0,\dots,a_{i_k})$ for $A$ such that, for each $k\in\mathbb{N}$, there is no index $j$ such that $i_{k-1}<j<i_{k}$ and for which $(a_0,\dots,a_j)$ is an $m$-palindrome. Define the $m$-palindromic density of $\alpha$ to be the number”

$$d_m(\alpha)=\limsup_{k\to+\infty}\frac{|P_k(A)|}{|P_{k+1}(A)|}.$$

The first sentence of Conjecture 7.1 is the target. Digits and lengths are
strictly positive; indices start at zero and a prefix ending at index i has
length i+1. Nat.nth lists all qualifying positive prefix lengths. Finite
continued fractions use Mathlib's rational GenContFract.convs' evaluator.
Lemmas 3.1–3.2 supply the matrix criterion, and section 7 supplies the
substitution a ↦ (mr,r), b ↦ (ms,s).

## Scope

The fixed construction uses m=2, r=2, s=3. Its nested stages begin with (4,2)
and concatenate k+2 copies of the preceding stage, k+1 copies of (6,3), and
k+2 further copies of the preceding stage. Qualifying powers force upper
limsup one; separator mismatches exclude eventual periodicity. The separate
Fibonacci equality, a liminf replacement, and a uniform formal family remain
open. The literature screen recorded in issue #22972 is not exhaustive;
priority and journal-version agreement remain ASSUMED-UNVERIFIED.

## Supporting finite computation

The experiment is in the private repository
https://github.com/the-omega-institute/trureturing-experiments at commit
`7abc41a29f3c5f18e4594875e8644e7d6dc5a2e1`, under
`docs/reports/palindromic-continued-fraction-density/`. The command is
`python3 check.py`; the script SHA-256 is
`208e436c59caaf1d4b58d24649136c3283db749f4176620af2e8de066518c19e`.
Issue https://github.com/the-omega-institute/trureturing/issues/22972 records
exit code 0 and the final line `ALL_CHECKS_OK`. These are cited experiment
readings, not a new execution. Finite prefix scans support the construction;
the infinite aperiodicity and density conclusions are proved in Lean.
