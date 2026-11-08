---
slug: ycz2015-psicm
bibkey: yangchuzhang2015psicm
doi: 10.1186/s13660-015-0674-8
url: https://arxiv.org/abs/1409.6411v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/YangChuZhangPsiCM/Refutation.result
---

# Yang–Chu–Zhang Conjecture 1(ii): complete monotonicity of the negative psi remainder

## Problem

Zhen-Hang Yang, Yu-Ming Chu and Xiao-Hui Zhang, *Necessary and sufficient conditions for functions involving the psi function to be completely monotonic*, Journal of Inequalities and Applications 2015:157, DOI [10.1186/s13660-015-0674-8](https://doi.org/10.1186/s13660-015-0674-8), Conjecture 1(ii), §4, p. 15:

> Let $R(x)$ be defined on $(0,\infty)$ by (1.10). Then we conjecture that
> (ii) the function $-G_a$ is completely monotone on $(0,\infty)$ if and only if $a\leq155/294$.

The corresponding versioned preprint is [arXiv:1409.6411v1](https://arxiv.org/abs/1409.6411v1). Its expressions are

$$R(x)=\psi(x+1/2)-\log x,$$

$$G_a(x)=24\left(x^4+ax^2+\frac7{40}a-\frac{31}{336}\right)R(x)-\left(x^2-\frac7{40}+a\right).$$

Here $\psi(x)=\Gamma'(x)/\Gamma(x)$ for $x>0$. Complete monotonicity requires smoothness and $(-1)^n f^{(n)}(x)\geq0$ for every $n\in\mathbb N$, including zero, and every $x>0$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Equation (1.10) | `R` | The real part of `Complex.digamma` at the real-to-complex coercion of $x+1/2$, minus `Real.log x`. |
| Equation (3.3) | `G` | Every coefficient, exponent and sign is retained. |
| Real parameter $a$ | `claim` | All real parameters are quantified without an added bound. |
| Complete monotonicity on $(0,\infty)$ | `ExpRatioCM.Defs.CompletelyMonotoneOn` | Existing owner; smoothness and every natural derivative order at every positive point. |
| If and only if $a\leq155/294$ | `claim` | Both directions are retained, with the negative sign on $G_a$. |
| Refutation | `result` | Negation of that universal equivalence. |

The total library functions outside the source domain impose no extra hypothesis: each monotonicity test is at a positive real argument. There are no extra public theorem hypotheses.

## Motivation

The proposed parameter threshold fails in its sufficient direction at a strictly positive point and at a parameter strictly below the asserted threshold. A second derivative already detects the failure.

## Gap

[Preregistration #21602](https://github.com/the-omega-institute/trureturing/issues/21602) supplies the source and the literature screen. No settlement was identified in that screen at preregistration. Its completeness is ASSUMED-UNVERIFIED: citation retrieval was incomplete, some services returned HTTP 429 or search challenges, and the inspected papers do not constitute an exhaustive bibliography.

**Independent later settlement.** The open-problem-resolution admission precondition is checked at preregistration, before any probe (CLAUDE.md §3.2); the recorded public chronology leaves this preregistered settlement eligible. An independent external settlement is public in PrincipiaMathOrg/math-solutions at [`site-backup/mathdb-328867/mathdb-328867-solution.tex`](https://github.com/PrincipiaMathOrg/math-solutions/blob/47371706c400c79d06e3fb62190fcf6f7a725c85/site-backup/mathdb-328867/mathdb-328867-solution.tex). The first public commit identified in #21602 is 2026-10-27, after the preregistration at 2026-10-25T09:23:40Z; MathDB records MJ Kang's solution on 2026-10-28. No priority over that independent mathematical solution is claimed. This delivery provides a Lean settlement of the preregistered assertion.

## Route

The proof uses `ExpRatioCM.Defs.CompletelyMonotoneOn`, `Zeta23.Stirling.differentiableAt_digamma` and `Zeta23.Stirling.hasSum_trigamma`. The reciprocal-square and reciprocal-cube series are `D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz` at exponents $2$ and $3$: its defining series is $\sum_{n=0}^{\infty}1/(n+b)^s$. Commutativity of addition identifies its summands with $1/(b+n)^s$. Real restriction and termwise differentiation give the first two derivatives of $R$. A telescoping reciprocal-cube majorant bounds the second differentiated series. At $r=1/64$, the private helpers establish

$$R(r)>5/3,\qquad R'(r)\geq-64,\qquad R''(r)\geq4078.$$

Positive polynomial coefficients combine these estimates into $G_a''(r)>1/2$ for every $a\geq155/294-1/10000$. The CM condition for $-G_a$ at order two has the opposite sign.

## Falsifier

Set $a_0=774853/1470000=155/294-1/10000$ and $r=1/64$. Then $a_0<155/294$ and $r>0$, but $(-G_{a_0})''(r)<-1/2$. This contradicts the claimed sufficient direction. No boundary evaluation or finite-order replacement of the full source predicate is used.

## Evidence

The frozen settling declaration is `D5.S3.Analytic.YangChuZhangPsiCM.Refutation.result` in [the Lean module](../D5/S3/Analytic/YangChuZhangPsiCM/Refutation.lean). The source definitions and full negated equivalence are mirrored by [its Blueprint](../Blueprint/D5/S3/Analytic/YangChuZhangPsiCM/Refutation.md). The only public theorem is `result`; all analytic helpers are private and used by its proof.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The experiment is [trureturing-experiments, `docs/reports/ycz2015-psicm/` at `ec4056f84cbbe087d1b1dc107475e05488987ca2`](https://github.com/the-omega-institute/trureturing-experiments/tree/ec4056f84cbbe087d1b1dc107475e05488987ca2/docs/reports/ycz2015-psicm). Command: `cd ../trureturing-experiments && python3 docs/reports/ycz2015-psicm/check.py`, with the local script checked against that revision, exit 0. Script SHA-256: `b5a91d08f0faa757b607bc5860b6e5f09d402f1072a525db5a138aba2aa216a8`. Exact rational and symbolic computations check the source Remark 4 identity, its sign for every integer $n\geq1$ with a cross-check at $n=1,\ldots,32$, and the nominated parameter certificate over the full interval $[155/294-1/10000,155/294]$. The computed lower bound is $249085992523/481689600000>1/2$. These computations do not certify the analytic interchange steps; those occur in the Lean proof.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Sufficient direction at $a=774853/1470000<155/294$, $x=1/64$, order $n=2$ | **Proved, kernel-checked:** `result`, using private `uniform_second_deriv` at $a_0$ and the order-two clause of the source predicate. |
| Positive second-derivative estimate for every $a\geq774853/1470000$ | **Proved, kernel-checked:** private `uniform_second_deriv` has exactly this quantified parameter range; no upper parameter bound is assumed. |
| Cancellation $(7/40)(155/294)=31/336$ and nominated full-interval certificate | **Computed:** the experiment entry above, exit 0 and the stated script SHA-256; the parameter interval is exactly $[155/294-1/10000,155/294]$. This computation is distinct from the stronger unbounded parameter range in the Lean helper. |
| Asymptotic divergence $G_{155/294}''(x)\to+\infty$ as $x\downarrow0$ | **Open:** not formalized here. The fixed positive point suffices for the refutation. |
| Corrected sharp CM cutoff and validity at lower parameters | **Open:** the proof excludes every $a\geq774853/1470000$ but supplies no positive classification below it. |
| Conjecture 1(i), the opposite sign in Theorem 4, and a lower-parameter sharp iff | **Open / outside this settlement:** Conjecture 1(i) is unresolved here; Theorem 4 concerns $G_a$, rather than $-G_a$, and its stated range is not refuted by this argument. No sharp lower-parameter iff is delivered. |

The failure mechanism is a negative second derivative of $-G_a$ on the source domain despite the asserted parameter inequality. The uniform positive bound for $G_a''(1/64)$ survives on the entire parameter half-line above $a_0$. The refutation concerns Conjecture 1(ii); the source Theorem 4 has the opposite sign and is outside this task. No independent later result relying on Conjecture 1(ii) was identified in the inspected literature; that negative search is subject to the completeness boundary below.

## ASSUMED-UNVERIFIED

Literature completeness, exhaustive downstream-dependency coverage, the corrected sharp cutoff, lower-parameter complete monotonicity, Conjecture 1(i), and the asymptotic divergence are not established by this delivery. The external settlement is independently attributed above. The computation's interval certificate does not extend its own tested scope to an unbounded parameter range.
