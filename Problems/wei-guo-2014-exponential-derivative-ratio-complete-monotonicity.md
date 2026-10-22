---
slug: wei-guo-2014-exponential-derivative-ratio-complete-monotonicity
bibkey: weiguo2014completemonotonicity
doi: 10.1155/2014/851213
triage: theorem
motivation_gids:
  - D5/S3/Analytic/ExpRatioCM/Result.result
url: https://doi.org/10.1155/2014/851213
---

# Refutation and exact classification of exponential derivative ratios

## Problem

Section 5 of the source identified by
`D5/L/Asymptotics/weiguo2014completemonotonicity` states:

> Conjecture 12. For given i ∈ {0} ∪ ℕ, the functions ℱ_i(t) and 𝒢_i(t) defined in (10) or (27) are completely monotonic on (0, ∞).

Equation (6) defines

$$F_i(t)=(-1)^i\left(\frac1{e^t-1}\right)^{(i)},\qquad
G_i(t)=(-1)^i\left(\frac1{1-e^{-t}}\right)^{(i)},$$

and equation (10) defines

$$\mathcal F_i(t)=\frac{F_{i+1}(t)}{F_i(t)},\qquad
\mathcal G_i(t)=\frac{G_{i+1}(t)}{G_i(t)}.$$

The source verifies $i=0,1$ in (30). Complete monotonicity means
smoothness on $(0,\infty)$ and $(-1)^kh^{(k)}(t)\ge0$ for every
nonnegative integer $k$ and every $t>0$.

### Formal reading

All Lean names below have prefix `D5.S3.Analytic.ExpRatioCM`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| $F_i(t)$ in (6) | `Defs.F` | Exactly the globally defined signed iterated derivative of $1/(e^t-1)$. |
| $G_i(t)$ in (6) | `Defs.G` | Exactly the globally defined signed iterated derivative of $1/(1-e^{-t})$. |
| $\mathcal F_i$ in (10) | `Defs.ratioF` | Exactly $F_{i+1}/F_i$. The denominator is positive for $t>0$. |
| $\mathcal G_i$ in (10) | `Defs.ratioG` | Exactly $G_{i+1}/G_i$. The denominator is positive for $t>0$. |
| Complete monotonicity | `Defs.CompletelyMonotoneOn` | `ContDiffOn` with smoothness index `⊤` on `Set.Ioi 0`, and the sign condition for every natural derivative order at every positive argument. |
| Conjecture 12 | `Defs.claim` | Both complete-monotonicity assertions for every natural index, including zero. |
| Exact index sets | `Positive.cm_of_le_two`, `Result.not_cm_of_three_le` | The positive theorem covers $i\le2$, while the failure theorem excludes every $i\ge3$. |
| Failure on every right half-line | `Result.failure_on_every_tail` | For every $i\ge3$ and real $T$, there are a natural $k$ and $t>\max\{T,0\}$ at which both alternating derivatives are negative. |
| Universal refutation | `Result.result` | Exactly $\neg\,\texttt{Defs.claim}$. |

The globally defined derivatives agree with derivatives of the smooth
restrictions on the open positive half-line by neighborhood equality.
No derivative value at zero is used.

## Motivation

The settling declaration is `D5/S3/Analytic/ExpRatioCM/Result.result`.
Decreasingness controls the first derivative; complete monotonicity
requires simultaneous sign constraints at every order. Exponential
coefficients provide a way to distinguish these requirements.

## Gap

Status: **Refuted**. The exact completely monotone indices for each
family are $\{0,1,2\}$. At every index $i\ge3$, both families have a
negative alternating derivative on every interval $(T,\infty)$.
The smallest order producing any negative value, as a function of the
index, is not determined here.

## Route

For $t>0$, termwise differentiation gives

$$F_i(t)=\sum_{n\ge1}n^ie^{-nt},\qquad
G_0(t)=1+F_0(t),\qquad G_i(t)=F_i(t)\quad(i\ge1).$$

Write $z=e^{-t}$ and $D_i(z)=\sum_{n\ge0}(n+1)^iz^n$.
Then $\mathcal F_i=D_{i+1}/D_i$. Its coefficients satisfy

$$b_0=1,\qquad
b_n=(n+1)^{i+1}-\sum_{j=1}^n(j+1)^ib_{n-j}\quad(n\ge1).$$

For $B=2^{i+2}$, strong induction gives $|b_n|\le B^n$.
The coefficient convolution and absolute convergence give, for
$t>\log B$ and $k\ge1$,

$$(-1)^k\mathcal F_i^{(k)}(t)=\sum_{n\ge1}b_nn^ke^{-nt}.$$

Put $a_n=(49/32)n(4/7)^n$. The normalized derivative at
$t_k=k\log(7/4)$ is $\sum_n b_na_n^k$.
Here $a_1=7/8$, $a_2=1$, and
$a_{n+3}\le(6/7)(16/21)^n$. For $k\ge1$ satisfying
$B(16/21)^k\le1/2$, the explicit bound is

$$\left|\sum_n b_na_n^k-b_2\right|
\le |b_1|(7/8)^k+2B^3(6/7)^k.$$

Consequently,

$$\left(\frac{49}{32}\right)^k(-1)^k
\mathcal F_i^{(k)}\left(k\log\frac74\right)
\longrightarrow b_2=2\cdot3^i-4^i.$$

This limit is negative for every $i\ge3$. The normalization is
positive and $t_k\to\infty$, so both ratio families have negative
alternating derivatives arbitrarily far to the right.

For the remaining indices the closed forms are

$$\mathcal F_0=\frac1{1-z},\qquad
\mathcal F_1=\frac{1+z}{1-z},\qquad
\mathcal F_2=\frac{1+4z+z^2}{1-z^2},\qquad
\mathcal G_0=\frac z{1-z}.$$

Their exponential coefficients are nonnegative. In particular,
$\mathcal F_2=1+4F_0(t)-2F_0(2t)$ has coefficient four at positive
odd frequencies and coefficient two at positive even frequencies.
The formal sign argument uses the even-subseries inequality
$2^kF_k(2t)\le F_k(t)$. The positive-index ratios of the two families
coincide, completing the positive range; `Result.not_cm_of_three_le` excludes every index at least three.

## Falsifier

One index and one positive argument with a negative alternating
derivative refute the universal assertion. Index three supplies such
values. A completely monotone ratio at any index at least three would
contradict `Result.not_cm_of_three_le`. The decreasing property alone
does not imply the higher-order sign conditions.

## Evidence

`D5/S3/Analytic/ExpRatioCM/Result.result` proves exactly
`result : ¬ claim`. Its principal dependencies are
`Positive.cm_of_le_two`, `Result.not_cm_of_three_le`,
`Result.failure_on_every_tail`,
`Extraction.quotient_extraction_limit` and `Positive.cm_of_le_two`.
The extraction uses `Series.abs_quotCoeff_le`,
`Series.iteratedDeriv_ratioF` and `Series.quotCoeff_two`.
The positive cases use the moment expansion and the low-index closed
forms. The axiom closure of the result is exactly
`{propext, Classical.choice, Quot.sound}`.

The refutation route was derived with the assistance of the ChatGPT Pro model.
Guo–Qi, arXiv:2201.06970, Section 5, Proposition 5.1, strengthens the
decreasing property to the range $(1,\infty)$ and does not address
complete monotonicity of the ratios. No settlement was found in the
searched scope consisting of the title, DOI and conjecture queries;
Proskurnikov–Runvik–Medvedev, arXiv:2302.01364, Appendix B;
Formal Conjectures; conjectures.io; and the corresponding repository
mathematical, bibliographic and problem entries. The cited appendix
uses another theorem of the source. This scope does not establish
exhaustive citation-index coverage or priority.

## Triage

- **PROVED.** $\mathcal F_i$ and $\mathcal G_i$ are completely
  monotonic on $(0,\infty)$ for $i\le2$ by `Positive.cm_of_le_two`,
  and fail complete monotonicity for $i\ge3$ by
  `Result.not_cm_of_three_le`.
- **PROVED.** For every $i\ge3$, failure occurs on every interval
  $(T,\infty)$, by `Result.failure_on_every_tail`; the two families
  have negative alternating derivatives at the same order and point.
- **PROVED in prose.** For a function agreeing with
  $h(t)=\sum_{n\ge0}b_ne^{-nt}$ on a right half-line and satisfying
  $|b_n|\le B^n$ for some $B>0$,
  $(49/32)^k(-1)^kh^{(k)}(k\log(7/4))\to b_2$.
  Locally uniform termwise differentiation and the geometric tail
  estimate in the route apply to arbitrary such coefficients, detecting
  the sign of the second exponential coefficient.
- **COMPUTED.** With 80-digit arithmetic,
  $(-1)^k\mathcal F_3^{(k)}(k\log(7/4))$ is approximately
  $-0.0039$ at $k=12$. For $\mathcal F_4$ the sampled alternating
  derivatives are negative from $k=16$ onward among the evaluated
  orders $k\in\{16,17,20,24\}$. The quotient
  coefficients for $i=3$ begin $b_1,b_2,b_3,b_4=8,-10,56,-190$.
  These numerical values are separate from the formal proof and do
  not determine the smallest negative derivative order.
- **OPEN.** The smallest order $k$ at which
  $(-1)^k\mathcal F_i^{(k)}$ first takes a negative value somewhere
  on $(0,\infty)$, as a function of $i\ge3$.

## ASSUMED-UNVERIFIED

Exhaustive citation-index coverage and priority are unverified.
The bounded literature conclusions do not assert the absence of a
settlement outside that scope. The numerical evaluations have no
certified rounding bounds; the sign and classification conclusions
instead follow from the formal derivative and limit arguments.
