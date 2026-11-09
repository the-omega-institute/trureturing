---
slug: kurkov-a263634-log-polynomials
bibkey: kurkov2025a263634
doi: null
url: https://oeis.org/A263634
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.result
---

## Problem

Mikhail Kurkov's sole FORMULA conjecture in OEIS A263634, revision 166, is the universal logarithmic-polynomial recursion. Its source and quantified target are preregistered in [#26373](https://github.com/the-omega-institute/trureturing/issues/26373). The source is an unnumbered OEIS conjecture, with no source arXiv identifier or DOI. The Library note is [kurkov2025a263634](../Library/Certificates/kurkov2025a263634.md).

Let $A=\mathbb Q[x_1,x_2,\ldots]$ and $F(t)=1+\sum_{i\ge1}x_i t^i/i!$. The source family satisfies $\log F(t)=\sum_{n\ge1}L_n t^n/n!$. Define $R(1,k)=x_k$ and, for $n\ge2$ and $k\ge1$,

$$R(n,k)=R(n-1,k+1)-\sum_{j=1}^{n-1}\binom{n-2}{j-1}R(j,k)R(n-j,1).$$

The assertion is that a source family exists and that $R(n,1)=L_n$ for every such family and every $n\ge1$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The formal exponential series inside the logarithm | `sourceSeries` | Coefficient one at zero; coefficient $x_i/i!$ at positive $i$. |
| The generating function defining $L_n$ | `IsSourceFamily` | The complete formal-series equality; $L_0=0$ records its zero constant coefficient. |
| $R(1,k)=x_k$ | The row-one branch of `R` | All positive columns; the total function also assigns column zero. |
| The binomial convolution for $n>1$ | The final branch of `R` | $n=m+2$, $j=r+1$ and $r\in\mathrm{Fin}(m+1)$ give exactly the source indices and weight. |
| Every positive row is $R(n,1)$ | `claim` and `result` | Existence plus identification for every source family and every positive row. |
| Printed monomial order | No extra hypothesis | Ordering the printed coefficient list does not change a polynomial identity. |

The coefficient algebra is `MvPolynomial ℕ ℚ`. The variable with index zero is unused by the positive-column recursion; row zero is totalized by zero outside the source assertion. All factorials are invertible in the rational coefficient algebra. On every summand $r\le m$, so the natural subtraction $m-r$ does not truncate.

## Motivation

The frozen settling declaration is `D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.result`. It proves the whole unbounded assertion, with `generality: G`, `utility: none` and `admission_basis: open-problem-resolution (#26373; Proved)`. There is no atom or coverage claim.

## Gap

The defining formal logarithm supplies the family by coefficient normalization, but it does not by itself identify Kurkov's two-index recurrence. The missing mathematical bridge is the arbitrary-order quotient-jet realization, simultaneously over every positive column.

## Route

Write $D=d/dt$, $Q_k=(D^kF)F^{-1}$ and $J_n(H)=(D^nH)(0)$. The constant coefficient of $F$ is one, so its formal inverse exists. Differentiating $Q_kF=D^kF$ gives

$$DQ_k=Q_{k+1}-Q_kQ_1.$$

The iterated product rule yields exactly the binomial convolution in the source recurrence. Strong induction on $n$, simultaneously for all $k\ge1$, proves $R(n+1,k)=J_n(Q_k)$. The existing `PositiveNewtonSums.logarithmic_derivative` is applied to rational evaluations; `MvPolynomial.funext` transfers its identity to the polynomial algebra. Hence $D\log F=Q_1$, and coefficient comparison gives $R(n,1)=L_n$.

## Falsifier

A source-family witness and a positive row at which $R(n,1)\ne L_n$ would refute the stated conjecture. A disagreement in a finite experiment would instead require checking its definitions and exact polynomial arithmetic; a failed proof attempt alone is neither a refutation nor a counterexample.

## Evidence

The Lean source is [KurkovA263634LogPolynomials.lean](../D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials.lean), with its Scribe and emitted Blueprint at the matching address. The only new public theorem is `result`; the published owner theorem is `PositiveNewtonSums.logarithmic_derivative` with its existing statement and proof.

The four-slot escape audit is unfinished for these two targets: [#26975](https://github.com/the-omega-institute/trureturing/issues/26975). The result needs a complete existential-plus-universal source realization; the conditional scalar identity also lacks the full typed reconstruction, bridge, variation, sensitivity and observational-dependence evidence. No `declared_validated` claim is made.

### Exact finite experiment

The independent program and data are in [the immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/136cb381317bd127d73846849053869b47567e3e/docs/reports/oeis-a263634-kurkov-logarithmic-polynomial-recursion). The script `check.py` has SHA-256 `283ab9dfcf5b7e077f0ec8d23113631e1f2ee266f34d107bdddf682cc5b3c010`. The command `python3 /Users/auric/.sshx/2774939e4564f2e8ff0fe4b7/attempt-1/experiment/check.py` on that exact script exits 0 with `ALL_CHECKS_OK`. It reproduces source rows 1–6, checks the first-column identity through order 8 and checks the 36 positive pairs satisfying $n+k-1\le8$. These are finite exact checks, separate from the unbounded kernel proof.

## Triage

### What the settlement shows

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Complete unbounded claim, including family existence and every admissible family at every positive row | proved | Kernel-checked `KurkovA263634LogPolynomials.result`. |
| Quotient-jet realization at every nonnegative derivative order and every positive column | proved | Kernel-checked private `KurkovA263634LogPolynomials.quotient_jet`, consumed by `result`. |
| Every source family is pointwise the factorial-normalized coefficient/jet family | proved | Kernel-checked private `KurkovA263634LogPolynomials.source_family_jet`, consumed by `result`. |
| Constant-one formal inversion and formal differentiation; no analytic convergence assumptions | proved | Kernel-checked `source_inverse`, `quotient_derivative`, `quotient_jet` and `logarithm_derivative`; their compiled statements use formal power series. |
| Source rows 1–6, first-column identity through order 8 and all 36 positive quotient-family pairs with $n+k-1\le8$ | computed | Exact experiment above; command exit 0 and the stated script SHA-256. No uniform conclusion is inferred from these tests. |
| Other binomial weights, noncommutative coefficient algebras and separate generic coefficient-ring interfaces | open | No such extension is asserted by the delivered statements. |

The decisive mechanism is the quotient differential identity followed by simultaneous row induction. Its compiled range includes all positive columns, beyond the first-column conclusion. The formal logarithm and factorial normalization also construct the source family and identify every source family, rather than assuming existence. The source's conjectured first-column identity is therefore available as a theorem. No other source assertion is claimed to be newly proved by this delivery.

### Literature status

The bounded screen recorded in #26373 found no settlement of this exact auxiliary-array identity. It distinguishes the classical logarithmic-polynomial background in Comtet and Luschny (arXiv:2009.06743) from the source's binomial weight and two-index array. It also distinguishes the different recurrence proved in MathOverflow answer 510513. The cited recent cumulant and formal-series papers supply background, with no exact target settlement found in the passages screened. Literature completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The literature screen is bounded and does not establish exhaustive completeness or global priority. No mathematical verdict is asserted for the neighbouring open targets in Triage. The finite computation is limited to its stated rows, orders and 36 pairs. The missing four-slot audit evidence is tracked in #26975 and is distinct from the Lean proof.
