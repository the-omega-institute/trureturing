---
slug: ptaszynski-2022-unidirectional-kurtosis-lower-bound
bibkey: ptaszynski2022skewness
doi: 10.1103/PhysRevE.106.024119
url: https://arxiv.org/abs/2204.08421v4
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.result
---

# The sharp lower bound on the kurtosis of a unidirectional unicyclic current

## Problem

K. Ptaszyński, *Bounds on skewness and kurtosis of steady-state currents*, Phys. Rev. E 106, 024119 (2022), arXiv:2204.08421v4, Appendix, `main.tex` line 792:

> As discussed in Sec.~\ref{subsec:unmark}, it was numerically conjectured that the minimum and maximum values of $\mathcal{S}$, $\mathcal{K}$, $\mathcal{S}+\mathcal{K}$, $\mathcal{S}-\mathcal{K}$ and $\mathcal{S} \times \mathcal{K}$ are always obtained for a specific type of network topology, with all rates $k_{ij}$ equal to $k$ apart from one (here $k_{21}$) equal to $ak$, with the parameter $a$ depending on the optimized quantity and the number of states $N$.

Section III E 1, `main.tex` lines 424–428, gives the kurtosis lower endpoint $C=-(1+\sqrt5)/10$ in the limit $N\to\infty$ along rates $(A/N,1,\ldots,1)$, where $A=(3-\sqrt5)/2$. The asymptotic family supplies a candidate endpoint; the conjectured extremal topology leaves a universal bound over arbitrary positive rates to establish.

Issue [#25526](https://github.com/the-omega-institute/trureturing/issues/25526) fixes the reading. For each natural $n\ge2$ and strictly positive real rate vector $k:\mathrm{Fin}\,n\to\mathbb R$, put

$R_j=\sum_{i=0}^{n-1}k_i^{-j},\qquad \mathcal K(k)=\frac{15R_2^2}{R_1^4}-\frac{20R_3}{R_1^3}+\frac{6R_4}{R_1^2R_2},\qquad C=-\frac{1+\sqrt5}{10}.$

The claim is that $\mathcal K(k)>C$ for every such $n$ and $k$, and that $C$ is the greatest lower bound of the set of all these values, allowing $n$ to vary. This is proved. The endpoint is an infimum over state counts, with no attainment by a finite positive cycle of at least two states.

The source defines $\mathcal K$ as the fourth scaled current cumulant divided by the second (`main.tex` line 54). Substituting its current-cumulant formulas at lines 773–775 and waiting-time cumulants at lines 787–790 gives the displayed expression. This is the quantity encoded by `kurtosis`, rather than the standardized fourth central moment. See [the literature note](../Library/StatisticalMechanics/ptaszynski2022skewness.md).

## Motivation

A sharp lower bound separates variation of positive rates within a unidirectional cycle from departure from that model: a value at or below $C$ cannot come from any rate vector covered by the claim. The source uses higher current cumulants to constrain transport models and diagnose departures from unicyclic dynamics. The settlement supplies the unidirectional kurtosis lower endpoint in that programme, including its optimality over all state counts.

## Gap

Issue #25526 records the bounded literature check:

- The v4 source retains the numerical extremal-topology conjecture; the quoted passage and asymptotic kurtosis endpoint are checked against `main.tex`.
- The orchestrator reports three citing works listed by Semantic Scholar: arXiv:2305.09759, 2411.19643 and 2610.12652. The orchestrator reports reading the kurtosis passages of Gerry–Segal, arXiv:2305.09759, without finding this proof; the search author reports reading all three without finding a settlement.
- The orchestrator reports zero records for its Zenodo phrase search and no prior kurtosis settlement in its repository and issue searches. The related records are the skewness minimum in #22468 and the distinct heat-current question in #22747.

`not-found-in-searched-scope`.

## Route

Write $a=\sum_i x_i^2$, $b=\sum_i x_i^3$, $c=\sum_i x_i^4$ and $f(u)=15u^4-20u^3+6u^2$.

1. **Normalize inverse rates.** For any natural $n$ and any real vector $k:\mathrm{Fin}\,n\to\mathbb R$, `normalized` gives $\mathcal K(k)=15a^2-20b+6c/a$ with $x_i=k_i^{-1}/R_1$. This identity has no positivity hypothesis and uses total real division. In its application, `strict_lower_bound` assumes $n\ge2$ and $k_i>0$ for every $i$; these hypotheses give $R_1>0$ and hence $x_i>0$ for every $i$.
2. **Control moments.** For $n\ge2$ and any $x:\mathrm{Fin}\,n\to\mathbb R$ with every $x_i>0$, `moments` proves all four conditions $a>0$, $b\ge0$, $b^2\le ac$ and $c<a^2$. Cauchy–Schwarz supplies $b^2\le ac$. The strict inequality uses `HermiteMomentBounds.sum_sq_lt_sq_sum`, whose hypotheses are at least two coordinates and strict positivity of every coordinate, applied to the vector $i\mapsto x_i^2$.
3. **Bound the polynomial.** For every real $u\ge0$, `polynomial_lower_bound` proves $C\le f(u)$ by the identity

   $f(u)-C=\left(u-\frac{5+\sqrt5}{10}\right)^2\left(15u^2+(3\sqrt5-5)u+\frac{\sqrt5-1}{2}\right).$

   The second factor is nonnegative for $u\ge0$ because its coefficients are nonnegative.
4. **Obtain strictness.** For real $a,b,c$ satisfying all four conditions $a>0$, $b\ge0$, $b^2\le ac$ and $c<a^2$, `moment_lower_bound` proves $C<15a^2-20b+6c/a$. Put $t=b/a$; the hypotheses give $t\ge0$, $t^2<a$ and $at^2\le c$, so the expression is at least $Q=15a^2-20at+6t^2$. If $t\le2/3$, then $Q=\frac53(3a-2t)^2-\frac23t^2\ge-8/27>C$. If $t>2/3$, then $Q-f(t)=(a-t^2)[15(a+t^2)-20t]>0$, and item 3 applies to $t\ge0$. For $n\ge2$ and every strictly positive rate vector, `strict_lower_bound` combines this estimate with items 1 and 2.
5. **Approach the endpoint.** With $A=(3-\sqrt5)/2$, `sourceRates` assigns $k_0=A/(m+2)$ and $k_i=1$ for $i\ne0$ on $\mathrm{Fin}\,(m+2)$ for each natural $m$. For every such $m$, `source_rates_positive` proves positivity of all rates. The lemma `source_limit` proves $\mathcal K(\operatorname{sourceRates}(m))\to C$ as $m\to\infty$. The lemma `greatest_lower_bound` combines this admissible sequence with the strict bound: every lower bound of the full set is at most each sequence value, and hence at most $C$. Finally, `result : claim` combines the strict inequality and this `IsGLB` statement.

## Falsifier

A positive rate vector with $n\ge2$ and $\mathcal K(k)\le C$ would contradict the strict inequality. A universal lower bound strictly greater than $C$ over all these vectors and state counts would contradict the greatest-lower-bound assertion. The interpretation would miss the source problem if the encoded quantity had a different cumulant normalization or omitted admissible positive rate vectors.

The module uses exactly the displayed inverse-rate expression and quantifies over every strictly positive real vector indexed by $\mathrm{Fin}\,n$, for every natural $n\ge2$. Its connection to stochastic current cumulants is substitution into the source's renewal formulas, not a formal construction of a stochastic process. The claim uses `IsGLB` directly. The positive vectors `sourceRates m`, of sizes $m+2\ge2$, supply actual members of the set and establish approachability of the endpoint; there is no inference from an uninhabited infimum.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.lean.json`.

Declaration statements:

- `result`: `sha256:43d8e541f6a5dfd1b06c6ded0a00ae28ad0a919bd91a3b837f8a55078d915a3a`;
- `claim`: `sha256:734aa03645fc3fcb734ec489df4e449a2b1c637e5417ef07dde5d6c76f514f2c`.

## Triage

Tier 1 numerically conjectured extremal structure of a 2022 paper, preregistered in issue #25526 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n\ge2$ and every real rate vector $k:\mathrm{Fin}\,n\to\mathbb R$ whose entries are all strictly positive, the displayed quantity $\mathcal K(k)$ is strictly greater than $C=-(1+\sqrt5)/10$; the same $C$ is the greatest lower bound of the set of all these values over all such $n$ and $k$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Decisive mechanism.* The estimate `moment_lower_bound` requires exactly $a>0$, $b\ge0$, $b^2\le ac$ and $c<a^2$; `moments` supplies these for every strictly positive vector with at least two coordinates. Thus the universal estimate does not assume a finite-size extremizer of any prescribed topology. The split at $t=b/a=2/3$ separates a region uniformly above $C$ from a region controlled by the polynomial factorization, as detailed in the route.
- *Limiting geometry and sharpness.* For $N\ge2$ and rates $(A/N,1,\ldots,1)$ with the fixed positive $A=(3-\sqrt5)/2$, direct normalization gives $\sum_i x_i^j=[1+(N-1)(A/N)^j]/(1+A-A/N)^j$ for $j=2,3,4$. Each numerator tends to one and the denominator tends to $(1+A)^j$, so these moments tend to $\alpha^j$, where $\alpha=(1+A)^{-1}=(5+\sqrt5)/10$. In this limit $b^2=ac$ and $c=a^2$, and the normalized expression tends to $f(\alpha)=C$ by the factorization. This explains how the strict finite-vector moment inequalities can have a sharp unattained limit; `source_limit` certifies convergence for this fixed family.
- *Symmetries and a contrasting family.* For $n\ge2$, positive rates and any $r>0$, replacing $k_i$ by $rk_i$ multiplies $R_j$ by $r^{-j}$, which cancels in every term of $\mathcal K$. Permuting the coordinates preserves all power sums. Thus positive rescalings and permutations preserve the kurtosis values and yield corresponding approximating families. Equal positive rates instead give $R_j=n k^{-j}$ and $\mathcal K=(15-20+6)/n^2=1/n^2>0$, so they cannot approach the negative endpoint even as $n\to\infty$.
- *Effect on the paper and neighbouring questions.* The settlement establishes the lower side of the source's kurtosis interval for the positive unidirectional model without the conjectured extremal-topology assumption. It does not settle that topology conjecture at fixed $N$, the finite-$N$ optimizer or its monotonicity in $N$, the upper kurtosis bound, or the bounds on $\mathcal S\pm\mathcal K$ and $\mathcal S\times\mathcal K$. The source's numerical extension to bidirectional cycles in Section III E 2 remains outside this result. Consequently the source's broader deductions about multicyclicity from violations of unicyclic bounds do not acquire a proof for bidirectional systems from this settlement, and the separate heat-current conjecture in #22747 remains unaddressed.

## ASSUMED-UNVERIFIED

The bounded literature check in #25526 does not establish exhaustive worldwide novelty or priority. The claim that v4 is the latest version, the Semantic Scholar citation listing, the orchestrator's Gerry–Segal reading, the search author's readings of the three citing works, and the orchestrator's Zenodo, GitHub-issue and repository-wide absence searches are not independently reproduced. The v4 TeX conjecture, asymptotic endpoint and renewal formulas are checked against `main.tex`, md5 `5b72a7d5de1e5c34c76db21badb56492`.

The stochastic-process construction, the renewal identities as statements about that process, and the identification of the rational rate expression with a measured current-cumulant ratio are not formalized. The explanatory and symmetry arguments in "Argued, not formalized" are not additional formal conclusions of `result`; the cited private lemmas have the hypotheses stated in the route. The neighbouring finite-$N$, bidirectional, upper-bound and combined-cumulant questions listed above remain open here.
