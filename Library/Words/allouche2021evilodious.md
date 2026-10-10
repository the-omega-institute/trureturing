---
bibkey: allouche2021evilodious
authors: Jean-Paul Allouche and Jeffrey Shallit
year: 2021
title: Additive properties of the evil and odious numbers and similar sequences
doi: 10.7169/facm/2108
url: https://arxiv.org/abs/2112.13627v3
claim: Conjecture 12 asserts eventual strict increase of sixfold evil and odious representation counts, with thresholds 37 and 5.
strata_touched:
  - D5/S1/Words/EvilOdious/CoefficientTableChecker
  - D5/S1/Words/EvilOdious/DyadicPrefixBounds
  - D5/S1/Words/EvilOdious/DyadicStatesFirstThree
  - D5/S1/Words/EvilOdious/DyadicStatesLastThree
  - D5/S1/Words/EvilOdious/MatrixBounds
  - D5/S1/Words/EvilOdious/SequenceCoefficients
  - D5/S1/Words/EvilOdious/SixfoldMonotonicity
  - D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.7169/facm/2108

Source: https://arxiv.org/abs/2112.13627v3

The journal version is Funct. Approx. Comment. Math. 70(1) (2024), 55–69.
Page numbers below refer to arXiv version 3.

## Definitions

Page 1 fixes $\mathbb N=\{0,1,2,\ldots\}$ and states: “It seems more natural to include $0$, and so (except in the last section) we adopt this convention”.

Page 2: “Let $\mathbf t=t_0t_1t_2\cdots$ be the Thue-Morse sequence, defined by $t_0=0$, $t_{2n}=t_n$, and $t_{2n+1}=1-t_n$ for $n\geq0$.”

Equations (2)–(3), page 2, define ordered tuples, with repetitions permitted:

$$r_j(n):=|\{(x_1,x_2,\ldots,x_j):n=\sum_{1\leq i\leq j}x_i\text{ and }t_{x_i}=0\text{ for }1\leq i\leq j\}|$$

$$s_j(n):=|\{(x_1,x_2,\ldots,x_j):n=\sum_{1\leq i\leq j}x_i\text{ and }t_{x_i}=1\text{ for }1\leq i\leq j\}|.$$

Lean uses `Fin j` for the tuple positions and `false` and `true` for the letters 0 and 1. Its `Finset.Nat.antidiagonalTuple j n` is the finite set of tuples whose coordinate sum is `n`. The frozen `D5.S1.Words.Complexity.thueMorse` supplies the source sequence.

## Conjecture 12

Section 4, page 10, states:

> The status for $6,7,8,$ and $9$ summands is currently unknown. Based on numerical evidence, we make the following conjectures:
>
> **Conjecture 12.**
>
> (a) Both $r_6(n)$ and $s_6(n)$ are eventually strictly increasing.
>
> (a) $r_6(n)<r_6(n+1)$ for $n\geq37$.
>
> (b) $s_6(n)<s_6(n+1)$ for $n\geq5$.

The duplicated label (a) is printed in the source.

## Mathematical scope

The sixfold proof controls the first differences through dyadic coefficient states. The polynomial main term dominates the signed Thue–Morse terms for every twelve-bit prefix and hence at every larger scale. The initial finite ranges connect this estimate to the source thresholds.

The experiment entry `docs/reports/allouche-shallit-2021-sixfold-evil-odious-monotonicity/check.py` in `the-omega-institute/trureturing-experiments`, revision `5782fa2e`, has SHA-256 `a49a4321de233171bcd7500c2a6505af9defaec4f878f0ef8c560452cb9b4f66`. The recorded command `python3 check.py` exited 0 with `ALL_OK`. It computes $r_6(36)=12152>11976=r_6(37)$ and $s_6(4)=s_6(5)=0$, showing that the proposed thresholds are optimal. Its prefix-certificate minima for 8–11 bits are $-1344904727$, $-13132136135$, $-93085057559$, and $-211507860935$; twelve bits is the shortest successful prefix length. These readings are computations, distinct from the kernel proofs.

The cases of seven, eight and nine summands, and the applicability of the same dyadic norm argument to them, remain open. The sixfold statement does not change the paper's proved fivefold and tenfold results.
