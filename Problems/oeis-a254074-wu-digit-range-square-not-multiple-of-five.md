---
slug: oeis-a254074-wu-digit-range-square-not-multiple-of-five
bibkey: frohlich2017a254074
doi: null
url: https://oeis.org/A254074
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/WuDigitRangeSquareNotMultipleOfFive
---

# No A254074 term is a multiple of five

## Problem

OEIS A254074, NAME (`%N`, verbatim):

> Numbers k such that the decimal expansions of both k and k^2 have 5 as the digit with the smallest value and 9 as the digit with the largest value.

Chai Wah Wu's COMMENT (`%C`, verbatim):

> The first digit of a term is either 7, 8 or 9 and the last digit is either 5, 6 or 7. Conjecture: no term is a multiple of 5. - _Chai Wah Wu_, Sep 10 2017

The literal proved sentence is "Conjecture: no term is a multiple of 5."
Formally, every positive natural `k` whose decimal digits and square's decimal
digits both have minimum 5 and maximum 9 is not divisible by 5. The first
sentence of Wu's comment, concerning the first and last digits, is NOT
claimed. The sparsity, finiteness or infinitude of A254074, and every other
property of the sequence are also NOT claimed.

## Motivation

Wu's comment isolates a simple divisibility restriction seen in the known
terms. The theorem settles that restriction uniformly from the stated digit
extrema, without asserting any enumeration or asymptotic property of the
sequence.

## Gap

The preregistered probe reported the following literature readings on
2026-09-15 (verbatim):

> 文献门：OEIS #1–#24 全历史已读，猜想由 #18 加入，#19–#24 无结算；OpenAlex、arXiv、MathOverflow、Crossref、GitHub 的 A-number、exact quote 与数位平方形状检索均未发现陈述该 implication 的结果，状态为 not-found-in-searched-scope。OpenAlex 直连 /works 当日余额 0.0004 美元而单次需 0.001 美元，故直连为 HTTP 429；本次 OpenAlex 读数由直连 autocomplete 与 r.jina.ai 只读代理的同一 OpenAlex API URL 补齐，代理字节忠实性记 ASSUMED-UNVERIFIED。Semantic Scholar 为 HTTP 429，Google 为 CAPTCHA，均未冒充已核对。

These checked surfaces do not establish exhaustive literature coverage, and
no historical-priority claim is made.

## Route

1. If `5` divides `k`, while every decimal digit of `k` is at least `5`, its
   units digit is forced to be `5`.
2. Write `k = 10q+5`. Expanding the square gives `k^2` congruent to `25`
   modulo `100`, so its tens digit is `2`.
3. The maximum digit `9` in `k` makes `k` at least `59`, hence `k^2` at least
   `100` and the tens place is a real digit. `Nat.getD_digits` computes that
   digit at index one, `Nat.lt_digits_length_iff` proves the index is in
   range, and `List.getElem_mem` places `2` in the square's digit list. This
   contradicts its minimum digit `5`.

This route is bind-only over the pinned Mathlib statements: its local facts
are obtained by direct instantiation, projection, and normalization from the
digit-list and modular-arithmetic lemmas used by the module.

## Falsifier

Any positive natural `k` divisible by `5` for which both `k` and `k^2` have
decimal minimum digit `5` and maximum digit `9` would contradict the theorem.
The kernel-checked result quantifies over every positive natural `k`.

## Evidence

- Lean module:
  `D5/S1/Digit/Admissibility/WuDigitRangeSquareNotMultipleOfFive.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile on this worktree: wall time 4.31 seconds, cumulative type
  checking 68 milliseconds, and maximum resident set size 1,574,895,616
  bytes.
- Deleting the sole direct Mathlib import makes the module fail to compile;
  restoring it gives zero-exit serialized and profiled builds.
- An exhaustive exact-integer scan through `k = 12,000,000` found exactly one
  term, `k = 759576`, with `k^2 = 576955699776`; none of the found terms is
  divisible by `5`.
- For seed `254074`, 20,000 pseudorandom values of the form `k = 10q+5` all
  had `k^2` congruent to `25` modulo `100`.
- The bounded computations carry no proof. In particular, the exhaustive
  scan is thin in sequence-term count because it contains only one term.

## Triage

`theorem`. Wu's no-multiple-of-five sentence is proved for every positive
natural satisfying the two digit-range hypotheses; the resolution is
`proved`, not `refuted`.

## ASSUMED-UNVERIFIED

Historical openness outside the checked OEIS history, OpenAlex, arXiv,
MathOverflow, Crossref, GitHub, Semantic Scholar, and Google surfaces is
unverified; the literature search is not exhaustive and no priority claim is
made. The OpenAlex proxy's byte fidelity is unverified. The bounded scan does
not establish the universal theorem and is thin in term count.
