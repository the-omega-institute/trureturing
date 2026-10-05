---
bibkey: li2020rulerperioddoubling
authors: Shuo Li
year: 2020
title: "Palindromic length sequence of the ruler sequence and of the period-doubling sequence"
doi: null
url: https://arxiv.org/abs/2007.08317v1
claim: "Theorem 2 bounds period-doubling prefix palindromic length between one third of the binary run count and that run count."
strata_touched:
  - D5/S1/Words/Palindromes/PeriodDoubling/Word
license: citation-only
triage: anchor
---

# Ruler and period-doubling palindromic length

Page 2 identifies the period-doubling sequence as the fixed point of
0 → 01, 1 → 00, and as the ruler sequence reduced modulo two. The displayed
ruler sequence is indexed by positive integers and has value v₂(n) at n.
The Lean substitution iterate uses this coding literally and proves its
valuation-parity letters for every iterate.

Theorem 2, page 7 states the run-count estimate
$c(n)/3 \leq \operatorname{PL}(b[1,n]) \leq c(n)$, where c(n) is the number
of constant runs in the ordinary binary expansion. Since PL is integral,
the lower bound is equivalent to $\lceil c(n)/3\rceil \leq \operatorname{PL}(b[1,n])$.
This bound is literature content. It does not imply that the difference
sequence has infinitely many binary-kernel elements.

The printed palindrome cases require independent checking before use as an
exact legal-cut classification: the parity restrictions and the even factor
00 must be retained.
