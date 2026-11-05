---
slug: sitnik-1993-exponential-remainder-differences
bibkey: sitnik1993expremainder
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Analytic/ExpRemainderDifferences.result
url: https://arxiv.org/abs/1608.08784
---

# A negative third difference of exponential remainder ratios

## Problem

S. M. Sitnik, *Inequalities for the exponential remainder of the Taylor
series* (*Неравенства для остатка ряда Тейлора экспоненты*),
Vladivostok preprint (1993), https://arxiv.org/abs/1608.08784v2,
appendix (Дополнение), additional problem list, Problem 11,
PDF pages 27–28:

> 11. Определим функцию при x > 0. gₙ(x) = Rₙ₋₁(x)/Rₙ(x). Исследовать, при каких k разности этой функции при любом фиксированном x неотрицательны ∆ᵏgₙ(x) > 0? Гипотеза: при любых k. При k = 1 гипотеза сводится к (42), при k = 2 к неравенству задачи 1 на стр. 20.

Translation: For $x>0$, define $g_n(x)=R_{n-1}(x)/R_n(x)$.
Investigate for which $k$ the differences of this function, at every
fixed $x$, are nonnegative, $\Delta^k g_n(x)>0$.
Conjecture: for all $k$. For $k=1$ the conjecture reduces to (42),
and for $k=2$ to the inequality of Problem 1 on page 20.

Equation (1) defines

$$R_n(x)=e^x-\sum_{j=0}^{n}\frac{x^j}{j!},\qquad x\ge0.$$

The difference is forward in the natural index:

$$\Delta^k g_n(x)=\sum_{j=0}^{k}(-1)^{k-j}\binom{k}{j}g_{n+j}(x).$$

The Lean assertion quantifies over every natural $k\ge1$, every natural
$n\ge1$ and every positive real $x$, and asserts $\Delta^k g_n(x)\ge0$.
This weakens the source's displayed strict inequality. A negative
instance refutes both the nonnegative and the strict readings.

| Source object | Lean declaration | Correspondence |
| --- | --- | --- |
| $R_n(x)$ | `R` | Exponential minus the finite Taylor sum through degree $n$. |
| $g_n(x)$ | `g` | $R_{n-1}(x)/R_n(x)$, used only at $n\ge1$. |
| $\Delta^k g_n(x)$ | `(fwdDiff 1)^[k] (fun m => g m x) n` | Iteration of Mathlib's positive unit-step difference. |
| Universal assertion | `claim` | All $k\ge1$, $n\ge1$, $x>0$, with a nonnegative conclusion. |
| Negative instance | `witness_neg` (private) | $\Delta^3 g_1(1)<0$. |
| Refutation | `result` | Exactly $\neg\,\texttt{claim}$. |

All declaration names have prefix `D5.S3.Analytic.ExpRemainderDifferences`.

## Motivation

The settling declaration is `D5/S3/Analytic/ExpRemainderDifferences.result`.
The source note is `D5/L/Asymptotics/sitnik1993expremainder`.
The conjecture asks whether the positivity known for the first two
orders extends to every order. The third difference already gives a
negative instance; the small-argument expansion explains an entire
family of failures at odd orders at least three.

## Gap

The universal assertion has the mathematical counterexample
$(k,n,x)=(3,1,1)$. The Lean module proves this instance and its contradiction with the
assertion; the axiom closure is not asserted in this dossier.
The individual source results at orders one and two remain applicable.
The existence of negative instances at every even order at least four,
and the full positivity regions for higher orders, remain unsettled here.

## Route

Write $e=\exp(1)$. Direct summation gives

$$R_0(1)=e-1,\quad R_1(1)=e-2,\quad R_2(1)=e-\frac52,
\quad R_3(1)=e-\frac83,\quad R_4(1)=e-\frac{65}{24}.$$

Mathlib's `fwdDiff_iter_eq_sum_shift` gives

$$\Delta^3g_1(1)=g_4(1)-3g_3(1)+3g_2(1)-g_1(1)$$

$$=\frac{e-8/3}{e-65/24}-3\frac{e-5/2}{e-8/3}
+3\frac{e-2}{e-5/2}-\frac{e-1}{e-2}.$$

Put $L=2.7182818283$ and $U=2.7182818286$.
Mathlib's `Real.exp_one_gt_d9` and `Real.exp_one_lt_d9` give $L<e<U$, so the
four denominators are positive. Each ratio $(e-a)/(e-b)$ is monotone in $e$,
and clearing its single denominator gives a linear inequality in $e$:

$$\frac{e-8/3}{e-65/24}<5.188239,\qquad
\frac{e-5/2}{e-8/3}>4.229025,$$
$$\frac{e-2}{e-5/2}<3.290617,\qquad
\frac{e-1}{e-2}>2.392211.$$

Hence $\Delta^3g_1(1)<5.188239-3(4.229025)+3(3.290617)-2.392211=-0.019196<0$.
The Lean proof evaluates the finite sums with `Finset.sum_range_succ` and
`norm_num`, obtains each bound with `div_lt_iff₀` or `lt_div_iff₀` and
`linarith`, and combines the four bounds linearly. The common-denominator form
of the same quantity is $(12e^3+34e^2-457e+750)/(288(e-2)(e-5/2)(e-8/3)(e-65/24))$.

## Falsifier

A single $k\ge1$, $n\ge1$, $x>0$ with a negative forward difference
refutes the universal assertion. Here all four ratios are defined with
strictly positive denominators. The contradiction therefore does not
use division by zero, the natural-subtraction endpoint $n=0$, a reversed
difference sign, or a negative argument.

The source index range is read as $n\ge1$, the domain of $R_{n-1}/R_n$.
If an independent source check instead requires $n\ge2$, the proposed
formal instance must be replaced: the computed value at
$(k,n,x)=(3,2,1)$ is negative but is not certified by this Lean theorem.
An error in the polynomial identity or interval comparison would defeat
this proof route without establishing the conjecture.

## Evidence

The source module `D5/S3/Analytic/ExpRemainderDifferences.lean` contains
the definitions, the exact quantified assertion, one private negative
instance and `result : ¬ claim`. Its only direct imports are
`Mathlib.Algebra.Group.ForwardDiff` and
`Mathlib.Analysis.Complex.ExponentialBounds`; no frozen D5 declaration
is used.

The counterexample and the numerical readings were obtained with the assistance of the Claude Opus 5.5 model, and the Lean proof was drafted with the assistance of the gpt-6.1-sol model.

Searches covered the source's 2016 supplement, which lists Mehrez–Sitnik
and other subsequent work without a settlement of Problem 11; Sitnik's
https://arxiv.org/abs/1207.0936v4, which reports the solution of Problem 1
(monotonicity of $f_n$) by Mehrez–Sitnik, https://arxiv.org/abs/1410.6120,
and does not mention Problem 11; OpenAlex, general web search and the
repository. OpenAlex lists no work citing arXiv:1608.08784. No treatment of Problem 11
was found in that scope; this is not a priority certification.

The numerical readings below were computed with mpmath at 60 decimal digits,
outside the Lean development, by the program
`experiments/sitnik-exp-remainder-differences/differences_scan.py` of
the-omega-institute/trureturing-experiments at revision
993fe8ecf15ae7c5ebafaa3774b4f597562573c3
(<https://github.com/the-omega-institute/trureturing-experiments/tree/993fe8ecf15ae7c5ebafaa3774b4f597562573c3/experiments/sitnik-exp-remainder-differences>) (sha256
`5b6d8e0fbb432fac6791131d47da263a980f59c769fbcd877d3a96b83dfe734a`), run from
that directory as `python3 differences_scan.py` with Python 3.12 and mpmath
1.4.1, exit code 0.

## Triage

### What the settlement shows

- **PROVED (Lean, `witness_neg`, `result`).** $\Delta^3g_1(1)<0$, hence
  $\neg\,\texttt{claim}$.
- **PROVED in prose.** For every fixed $n\ge1$ and every fixed odd
  $k\ge3$, $\Delta^k g_n(x)<0$ for all sufficiently small positive $x$.
  Indeed, the convergent exponential series gives
  $R_{n-1}(x)=x^n h_n(x)/n!$, where
  $h_n(x)=\sum_{j\ge0}x^j n!/(n+j)!$ and $h_n(0)=1$.
  Thus $h_n(x)=1+x/(n+1)+O(x^2)$, and division by the analytic function
  $h_{n+1}$ near zero gives
  $h_n/h_{n+1}=1+x/((n+1)(n+2))+O(x^2)$.
  Consequently
  $g_n(x)=(n+1)/x+1/(n+2)+O(x)$.
  For fixed $k\ge2$ the $k$-th difference annihilates the affine function
  $n+1$. Subtracting two successive reciprocal products proves
  inductively
  $\Delta^k(1/(n+2))=(-1)^k k!/\prod_{i=2}^{k+2}(n+i)$.
  Taking the finite difference of the finitely many remainder terms
  keeps an $O(x)$ error. For odd $k\ge3$ the resulting limit is
  $-k!/\prod_{i=2}^{k+2}(n+i)<0$.
  At $k=3$, $n=1$ the limit is $-1/60$.
  The case $k=1$ is excluded from this cancellation argument:
  its affine term has difference $1/x$.
- **PROVED in prose.** For each fixed even $k\ge2$ and fixed $n\ge1$,
  the same expansion gives a positive limiting difference, hence
  positivity for all sufficiently small positive $x$. The negative
  even-order readings below therefore concern other arguments.
- **PROVED in the source / literature.** Order $k=1$ is the source's
  inequality (42), $R_n^2>R_{n-1}R_{n+1}$ (Theorem 8), after division
  by $R_nR_{n+1}>0$. Order $k=2$ is the inequality of Problem 1,
  proved by Mehrez–Sitnik (2014), arXiv:1410.6120. In the source's
  indices that inequality is
  $R_{n-2}R_nR_{n+1}+R_{n-1}R_n^2>2R_{n-1}^2R_{n+1}$;
  it is $\Delta^2g_{n-1}>0$ after multiplication by positive
  $R_{n-1}R_nR_{n+1}$. Neither is a theorem asserted by the present Lean module.
- **COMPUTED (mpmath, 60 digits, outside the Lean development; `python3 differences_scan.py`, exit 0).** For
  $k=1,2$, no negative value was found on
  $x\in\{0.001,0.5,1,2,3,5,8,12,20,30,50\}$ and $n=1,\ldots,39$,
  consistent with the source's (42) and the Mehrez–Sitnik result.
- **COMPUTED (mpmath, 60 digits, outside the Lean development; `python3 differences_scan.py`, exit 0).** Each
  order $k=3,\ldots,12$ has a negative value on that grid.
  Examples at $n=1$ are $k=3$, $x=0.001$: $-0.01667$;
  $k=4$, $x=5$: $-0.001358$;
  $k=8$, $x=3$: $-0.000465$;
  $k=12$, $x=2$: $-3.0\cdot10^{-5}$.
  These are rounded readings; the assertion about each order is limited
  to $3\le k\le12$.
- **COMPUTED (mpmath, 60 digits, outside the Lean development; `python3 differences_scan.py`, exit 0).** At
  $k=3$, each of $x=0.001,1,5$ gives negative values for all
  $n=1,\ldots,8$. At $x=1$ the values at $n=1$ and $n=2$ are
  respectively $-0.0191991$ and $-0.008813$, after rounding.

- **OPEN.** Whether every even $k\ge4$ has a negative instance,
  beyond the computed range $k\le12$; in particular the
  existence question for every even $k\ge14$. Also open here is the
  full region of $(n,x)$ on which $\Delta^k g_n(x)\ge0$ for each
  higher order. The counterexample changes the all-orders conjecture;
  it supplies no contradiction to the independent first- and
  second-order results and no classification of the remaining problems.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The odd-order and small-argument even-order statements are
proved in prose, not in Lean. All numerical observations have the finite
scope stated above.
