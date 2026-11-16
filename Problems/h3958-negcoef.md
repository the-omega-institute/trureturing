---
slug: h3958-negcoef
bibkey: hanna2026a395835
doi: null
url: https://oeis.org/A395835
triage: theorem
motivation_gids:
  - D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.result
---

# Hanna’s first-negative-coefficient infinitude conjecture

## Problem

Paul D. Hanna’s OEIS A395835 COMMENTS conjecture is “Conjecture: this sequence is infinite.” The source defines the integral formal series by
$F_n=1+XF_n^2-X^nF_n^{2n}$ and, for $n\ge2$, takes the first index $M(n)$ with a strictly negative coefficient. The sequence stops if an earlier parameter has no such index. The source note is [hanna2026a395835](../Library/AnalyticClosure/hanna2026a395835.md); the preregistration is [#21728](https://github.com/the-omega-institute/trureturing/issues/21728).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Integral formal power series and the literal equation | `Shared.SeriesEquation` | Powers are ordinary natural powers in `PowerSeries ℤ`. |
| Every natural parameter $n\ge2$ | `Shared.DefinedThrough` | Every parameter from $2$ through the upper bound must be defined. |
| First strictly negative coefficient | Mathlib `IsLeast` inside `Shared.DefinedThrough` and each term predicate | The index set uses strict coefficient negativity. |
| A395835 reads $M(n)$ | `A395835.Term835` | The natural index is explicitly cast to the integers. |
| A395836 reads $|[X^{M(n)}]F_n|$ | `A395836.Term836` | Integral absolute value. |
| A395837 reads $[X^{M(n)-1}]F_n$ | `A395837.Term837` | Natural predecessor; the equation gives constant coefficient one, so $M(n)>0$. |
| A395838 first differences | `A395838.Term838` | Forward difference $M(n+1)-M(n)$ with the prefix through $n+1$. The published table prepends $M(2)$ and shifts this tail; finite versus infinite length is preserved. |
| Infinite sequence | The four public claims and `result`, `result836`, `result837`, `result838` | Infinite domain of defined indices, with no distinctness condition on values. |

## Motivation

The settling GID is `D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude.result`, whose full Lean name ends in `A395835.result`. It proves the literal source infinitude claim. The companion claims are the equivalent readouts preregistered in #21729, #21730 and #21731. They share one uniform negative-coefficient argument. The source-specific module uses `generality: I`, `utility: none`, and `admission_basis: open-problem-resolution (#21728; Proved)`; every authored theorem is classified `bind-only`, with consumed private helpers.

## Gap

A finite list of negative coefficients cannot establish a first negative coefficient for every parameter. The uniform obstruction to nonnegative coefficients supplies the missing implication. The source and literature checks recorded in #21728 locate no prior settlement within their inspected scope; literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Normalized power-series contraction gives the unique integral formal solution for every $n\ge1$. Analytic inversion of $q(t)=t/(1+t-t^n)^2$ at zero supplies a convergent germ; uniqueness identifies its Taylor coefficients with that solution. The polynomial equation extends to its convergence disk.

If all coefficients were nonnegative, the real sum $f(x)$ would satisfy $1\le f(x)\le2$ and $x\le t(x)=xf(x)^2\le1$. Its radius is finite and positive, with $R\le1$. Monotonicity gives a limit $L\in[1,2]$, and $\tau=RL^2\in(0,1]$ satisfies $L=1+\tau-\tau^n$. The derivative numerator $1-\tau+(2n-1)\tau^n$ is positive, so the local inverse of $q$ at $\tau$ produces an analytic continuation at $R$. The published existing owner `CanonicalLiNonnegativeConverse.nonnegative_series_positive_boundary_obstruction` rules out that continuation for nonnegative coefficients. A negative coefficient therefore exists, and well-ordering supplies the first one and every required prefix.

## Falsifier

A parameter $n\ge2$ whose integral solution has no negative coefficient contradicts `Global.has_negative`. A failure of the literal stopping-prefix or readout correspondence would invalidate the external interpretation even if the Lean claims compiled; the statement echo fixes those conventions explicitly.

## Evidence

The kernel-checked settling declarations are `D5.S3.Analytic.AlgebraicSeries.HannaA3958Infinitude.A395835.result`, `A395836.result836`, `A395837.result837` and `A395838.result838` in the same namespace. The original Pringsheim owner is published with its proof intact. Its public declaration and the four settling declarations have an [unfinished escape audit, #22312](https://github.com/the-omega-institute/trureturing/issues/22312); no four-slot validation is claimed.

The independent exact experiment is [trureturing-experiments, immutable directory](https://github.com/the-omega-institute/trureturing-experiments/tree/c48fa1ae5c757a3fa1076a765ac1087108096b81/docs/reports/hanna-a3958-negcoef). The command `python3 /tmp/op-h3958/stage-b-experiment/check.py`, using `check.py` extracted byte-for-byte from that revision and path, exits 0 with `ALL_CHECKS_OK`. Its SHA-256 is `db2522833259ab9e14a822d5bf6fddc87d36a64f9d19c58179408301ab0d2267`. Recursion and exact Lagrange inversion agree at 2,115 coefficients, the four b-files agree for $n=2,\ldots,30$, and the derivative identity and positivity checks hold for $n=2,\ldots,30$ on $t=j/32$, $j=1,\ldots,32$. The source EXAMPLE coefficients for $n=2,\ldots,6$ agree. These are finite checks, not the uniform proof.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Decisive conflict between the Pringsheim singularity and the locally invertible rational parameter at the forced positive boundary | Proved; kernel-checked `Boundary.finite_boundary_obstruction`, using `Inverse.boundary_inverse` and the published Pringsheim owner | Arbitrary $n\ge2$ under the hypothetical nonnegative coefficient condition. |
| Uniform negative-coefficient existence, integral existence and uniqueness, and arbitrarily long defined prefixes for all four readouts | Proved; kernel-checked `Global.has_negative`, `Inverse.series_exists_unique`, `Inverse.common_of_all` and the four public settling results | Negative coefficients for every $n\ge2$; existence and uniqueness for every $n\ge1$. |
| Independent exact checker, b-files and derivative-grid checks | Computed; the immutable experiment and rerun in Evidence, exit 0 and the stated SHA-256 | Exactly 2,115 coefficients; four b-files for $n=2,\ldots,30$; derivative grid $j/32$ for $j=1,\ldots,32$. |
| First-negative-index asymptotics or bounds; A395836 root limits; A395838 difference-value distribution; infinitely many distinct readout values; infinitely many negative coefficients for each fixed $n$ | Open | None follows from the existence of one negative coefficient at each parameter. |

The companion infinitude conjectures change status together through the same shared proof. No additional source assertion that depends on stronger asymptotic, distributional or distinctness properties is settled. The boundary argument needs $n\ge2$; the separate formal existence and uniqueness statement extends to $n\ge1$.

## ASSUMED-UNVERIFIED

Literature completeness and first-publication priority are `ASSUMED-UNVERIFIED`. The inspected OEIS revisions are 48, 23, 9 and 13 for A395835–A395838. The literature screen covers those sources and the related arXiv, MathOverflow and GitHub searches recorded in #21728. OpenAlex, Semantic Scholar and Crossref rate limits prevent complete citation discovery; unavailable or unusable searches are not negative evidence. No exhaustive originality claim is made. The exact experiment does not establish any unbounded claim. Escape registration is unfinished under #22312.
