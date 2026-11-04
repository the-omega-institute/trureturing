---
slug: kimoto-wakayama-2019-even-normalized-apery-congruence
bibkey: kimotowakayama2022apery
doi: 10.4171/aihpd/129
url: https://arxiv.org/abs/1905.01775v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.result
---

# The even Kimoto–Wakayama normalized Apéry congruence is refuted

## Problem

K. Kimoto and M. Wakayama define normalized Apéry-like rational numbers $\widetilde J_k(n)$ by a three-term inhomogeneous recurrence in Section 3.4 of *Apéry-like numbers for non-commutative harmonic oscillators and automorphic integrals*. The source TeX `Eichler20191217.tex`, lines 1608–1617, states the even part of Conjecture 3.6 as follows (the source macro `\tJ` is rendered as $\widetilde J$):

> For positive integers $m,n,s$ such that $mp\ge s$ and $mp^{n-1}\ge s$, we have
> $$\frac{p^{2sn}\widetilde J_{2s+2}(mp^n)}{p^{2s}\widetilde J_{2s+2}(mp)}\equiv\frac{p^{2s(n-1)}\widetilde J_{2s+2}(mp^{n-1})}{p^{2s}\widetilde J_{2s+2}(mp)}\ (\not\equiv0)\pmod{p^n}.$$

The compiled proposition `claim` is the odd-prime restriction of this assertion. It quantifies over natural $p$ with `p.Prime` and $p\ne2$, then over positive natural $m,n,s$ satisfying $s\le mp$ and $s\le mp^{n-1}$, and requires both the displayed rational congruence and noncongruence of the right ratio to zero. The declaration `result` has type $\neg\,\texttt{claim}$.

## Motivation

The conjecture proposes prime-power stability for the normalized numbers in weights $2s+1$ and $2s+2$. It is motivated by the recurrence and by the weak modularity of the generating functions discussed by Kimoto and Wakayama; a valid even assertion would extend the lower-weight congruence phenomena to all positive $s$ under the stated index bounds. A certified counterexample identifies the missing divisibility mechanism before any proposed repair is treated as a theorem.

## Gap

The preregistration in issue [#25637](https://github.com/the-omega-institute/trureturing/issues/25637) records that the arXiv v2 conjecture and the 2023 journal version retained the assertion, while the bounded issue and repository searches found no settlement: `not-found-in-searched-scope`. The issue records a search of citing works and a reading of the congruence appendix of Kimoto–Wakayama arXiv:2312.07912v2 without a settlement. J.-C. Liu’s 2024 paper is identified there, but its full text was not available for reproduction, so whether it treats this even assertion remains open.

## Route

`normalizedEven s j` is the module’s natural-number recursion over two consecutive rows of rational values. At index $0$ its row has value $1$ at $s=0$ and $0$ elsewhere; at index $1$ it has $3/4$ at $s=0$, $1$ at $s=1$, and $0$ elsewhere. For every later index the recurrence uses the preceding two rows and the lower-weight entry at the preceding index, with the $s=0$ lower-weight term set to zero. This is implemented by the definition `normalizedEven`; `sample_step (k : ℕ)` states the row update for every natural $k$.

The private lemmas `sample_0` through `sample_45` evaluate the eight entries needed for weight index $s=7$. `sample_value (j : ℕ)` identifies `normalizedEven 7 j` with the seventh entry of `sampleRows j` for every natural $j`; `value_fifteen` and `value_forty_five` then give the exact rational values at $j=15$ and $j=45$. `left_value` rewrites the left ratio at $(p,m,n,s)=(3,5,2,7)$ to its exact rational value. `right_value` rewrites the right ratio to $1$, using the nonzero value supplied by `value_fifteen`.

`ratio_not_congruent` proves that this exact left value is not `RatCongr 3 2` to $1$. Its witness contradiction clears the rational denominator; the resulting integer numerator difference is $3$ modulo $9$, so the equality would force $3$ to divide the witness denominator, contrary to the defining condition of `RatCongr`. Finally, `claim_instance (h : claim)` specializes $h$ at $p=3$, $m=5$, $n=2$, and $s=7$. The hypotheses `3.Prime`, $3\ne2$, positivity, and both bounds reduce to decidable facts, including $7\le15$. The theorem `result` combines that instance with `left_value`, `right_value`, and `ratio_not_congruent` to derive $\neg\,\texttt{claim}$.

## Falsifier

The falsifier is sensitive to the exact compiled definitions. `normalizedEven` is the recurrence computation above, with natural subtraction in its indices and rational division; at $s=7$ it is the source’s normalized number of weight $16$. `RatCongr p n x y` means
$$\exists a,b:\mathbb Z,\quad \neg((p:\mathbb Z)\mid b)\ \land\ (x-y)b=(p:\mathbb Q)^n a,$$
with the integer witnesses coerced to rationals in the equality. The definition imposes no separate nonzero-denominator premise on the rational expressions. `claim` uses exactly the two index inequalities, the positivity hypotheses, the odd-prime restriction, and the conjunction of the congruence with the right-ratio noncongruence. Thus the certified instance is a counterexample to the formal odd-prime claim; any reading of the source assertion that includes all odd primes is refuted as well.

## Evidence

The canonical source is `D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.lean.json`.

Declaration statements:
- `result`: `sha256:ea3e3d46f8e3658491474162cd321fb4438431fff13a6576cde4414f52a4a6e6`;
- `claim`: `sha256:bb344da016608d60132e7a620275e9e7c2e6ff74ede61c3218941c5af08c8a4e`.

- **Proof.** It proves `result : ¬ claim` by the exact certified instance described in the route.
- **Axioms.** `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`; the module contains no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a 2019 arXiv paper retained in the 2023 journal version, preregistered in issue #25637 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** The proposition `claim` is false: it is not the case that every odd prime $p$ and every positive natural $m,n,s$ with $s\le mp$ and $s\le mp^{n-1}$ satisfies both the `RatCongr` relation between the two displayed ratios and the non-`RatCongr` relation of the right ratio to $0$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- The failure mechanism is insufficient uniform $p$-adic divisibility: the two size inequalities constrain the indices but do not by themselves force the ratio difference to have valuation at least $n$; a general necessary-and-sufficient replacement condition is open.
- The first, odd-weight assertion of Conjecture 3.6 is not a component of `claim` and remains open here. Theorem 3.10 and the source’s modularity and generating-function statements are likewise outside this result and are not refuted by it.
- A smaller modulus, additional hypotheses, or a different normalization could yield a nearby true statement, but no such repair is proved here.
- Any later argument that uses the even assertion itself as an established premise loses that premise; which particular downstream source statements depend essentially on it is open in this dossier.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and searches recorded in issue #25637 and does not establish exhaustive worldwide coverage or priority. The full text of Liu’s 2024 paper and the issue’s citing-work survey were not independently reproduced here. The odd-weight assertion, Theorem 3.10, source modularity results, and every corrected congruence are not formalized by this settlement. The journal-version wording and any reading beyond the quoted arXiv v2 TeX remain assumed-unverified.
