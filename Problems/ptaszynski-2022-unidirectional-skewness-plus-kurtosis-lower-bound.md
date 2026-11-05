---
slug: ptaszynski-2022-unidirectional-skewness-plus-kurtosis-lower-bound
bibkey: ptaszynski2022skewness
doi: 10.1103/PhysRevE.106.024119
url: https://arxiv.org/abs/2204.08421v4
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound.result
---

# The sharp lower bound on skewness plus kurtosis of a unidirectional unicyclic current

## Problem

K. Ptaszyński, *Bounds on skewness and kurtosis of steady state currents*, Phys. Rev. E 106, 024119 (2022), arXiv:2204.08421v4, Appendix, `main.tex` line 792:

> As discussed in Sec.~\ref{subsec:unmark}, it was numerically conjectured that the minimum and maximum values of $\mathcal{S}$, $\mathcal{K}$, $\mathcal{S}+\mathcal{K}$, $\mathcal{S}-\mathcal{K}$ and $\mathcal{S} \times \mathcal{K}$ are always obtained for a specific type of network topology, with all rates $k_{ij}$ equal to $k$ apart from one (here $k_{21}$) equal to $ak$, with the parameter $a$ depending on the optimized quantity and the number of states $N$.

Section III E 1, `main.tex` line 424, specifies the limiting interpretation:

> The other bounds have been derived in the assymptotic limit $N \rightarrow \infty$ in which the saturating value of $a$ scales as $a=A/N$.

The lower endpoint displayed at lines 434–437 is $\min(\mathcal S+\mathcal K)=-8/27$ for $A=1/2$.

The reading fixed in issue [#25636](https://github.com/the-omega-institute/trureturing/issues/25636) concerns this lower endpoint for positive unidirectional cycles. For $n\ge2$ and $k:\mathrm{Fin}\,n\to\mathbb R$ with every $k_i>0$, put
$R_j=\sum_i k_i^{-j}$ and

$$
\mathcal S(k)=\frac{3R_2^2}{R_1^4}-\frac{2R_3}{R_1^3},\qquad
\mathcal K(k)=\frac{15R_2^2}{R_1^4}-\frac{20R_3}{R_1^3}+\frac{6R_4}{R_1^2R_2}.
$$

The claim is that $\mathcal S(k)+\mathcal K(k)>-8/27$ for every such $n,k$, and that $-8/27$ is the greatest lower bound of the set $V$ of all these values as $n$ and $k$ vary. This is proved.

The source defines $\mathcal S$ and $\mathcal K$ as the third-to-first and fourth-to-second scaled current-cumulant ratios (`main.tex` lines 53–54). Substitution of its winding-number cumulants at lines 772–775 and waiting-time cumulants at lines 787–790 gives the displayed expressions. These are the reused Lean definitions `UnicyclicSkewnessMinimum.skewness` and `UnicyclicKurtosisLowerBound.kurtosis`; they are not standardized central moments. See [the literature note](../Library/StatisticalMechanics/ptaszynski2022skewness.md).

## Motivation

A sharp bound on the sum constrains the joint values of two current-cumulant ratios for the same rate vector. A value at or below $-8/27$ excludes every finite positive unidirectional cycle covered by the claim. The source uses higher current cumulants to infer properties of transport networks; this settlement supplies the lower endpoint for the sum, including optimality over all state counts.

## Gap

The bounded literature check recorded in #25636 reports:

- arXiv v4 retains the numerical extremal-topology conjecture;
- the search author read the latest versions of the Semantic Scholar citing works arXiv:2305.09759, arXiv:2411.19643 and arXiv:2610.12652 and found no bound on $\mathcal S+\mathcal K$;
- OpenAlex listed five citing works, of which two could not be identified because of HTTP 429/403 responses;
- repository and issue searches found the distinct skewness-minimum settlement #22468, kurtosis-lower-bound settlement #25526 and heat-current question #22747, without a settlement of the lower bound on the sum.

The citing-work readings, citation counts and absence searches are reports from #25636, not independently reproduced here. The v4 conjecture and endpoint are checked against the source TeX. `not-found-in-searched-scope`.

## Route

All unqualified lemma names below belong to `UnicyclicSkewnessPlusKurtosisLowerBound`; its proof helpers are private.

1. **Normalize the common rate vector.** For every natural $n$ and every real rate vector $k:\mathrm{Fin}\,n\to\mathbb R$, define $x_i=k_i^{-1}/R_1$ and $p=\sum_i x_i^2$, $q=\sum_i x_i^3$, $r=\sum_i x_i^4$. With no positivity hypothesis, `normalized_sum` proves the total-real-arithmetic identity $\mathcal S(k)+\mathcal K(k)=18p^2-22q+6r/p$, using `UnicyclicKurtosisLowerBound.normalized`, which also has no positivity or size hypothesis. For $n\ge2$ and every $k_i>0$, $R_1>0$ and every $x_i>0$.
2. **Control the moments.** For $n\ge2$ and every $k_i>0$, `normalized_moments` proves $p>0$, $q\ge0$, $q^2\le pr$ and $r<p^2$. It uses `UnicyclicKurtosisLowerBound.moments`, whose hypotheses are $n\ge2$ and strict positivity of every coordinate of its real vector $x$. The latter uses Cauchy–Schwarz and `HermiteMomentBounds.sum_sq_lt_sq_sum`; that lemma requires at least two coordinates and strict positivity of every coordinate and is applied to $i\mapsto x_i^2$. Set $t=q/p$, $e=r/p-t^2$ and $d=p-t^2$. The four moment inequalities give $t\ge0$, $e\ge0$ and $d>0$, since $q^2\le pr<p^3$.
3. **Use two positive certificates.** For real $p,q,r,t,e$ with $p\ne0$, $q=pt$ and $r=p(t^2+e)$, `reduced_form` rewrites the gap above $-8/27$ as $18p^2-22pt+6t^2+6e+8/27$. For all real $p,t,e$, `low_certificate_identity` identifies it with

   $$6e+18\bigl(p-\tfrac{11}{18}t\bigr)^2+\tfrac{13}{18}\bigl((\tfrac{11}{18})^2-t^2\bigr)+\tfrac{155}{5832}.$$

   For real $p,t,e$ with $e\ge0$ and $0\le t\le11/18$, `low_certificate` proves this expression strictly positive. For real $p,t,e,d$ with $d=p-t^2$, `high_certificate_identity` gives the alternative expression

   $$6e+d(18d+36t^2-22t)+(t-\tfrac23)^2(18t^2+2t+\tfrac23).$$

   For real $t,e,d$ with $e\ge0$, $d>0$ and $t\ge11/18$, `high_certificate` proves it strictly positive: $36t^2-22t=2t(18t-11)\ge0$, making the middle term positive, and the last term is nonnegative. For $n\ge2$ and every $k_i>0$, `strict_lower_bound` combines these cases with the normalized identity.
4. **Approach the endpoint.** For every natural $m\ge1$, `sourceRates m` has $m+1$ entries, $k_0=(2m)^{-1}$ and $k_i=1$ for $i\ne0$. Under exactly $m\ge1$, `source_rates_positive` proves positivity, `source_power_sum` gives $R_j=(2m)^j+m$ for every natural $j$, and `source_value` proves

   $$\mathcal S(k)+\mathcal K(k)+\frac8{27}=\frac{2(60m^2-8m+1)}{27m^2(4m+1)}.$$

   Under $m\ge1$, `source_value_asymptotic` rewrites this as $h(1/m)$, where $h(u)=2(60u-8u^2+u^3)/(27(4+u))$. Continuity at zero and $h(0)=0$ give `source_limit`: the sums for `sourceRates (m + 1)`, indexed by all natural $m$ and having $m+2$ positive rates, tend to `lowerBound`.
5. **Identify the greatest lower bound.** `greatest_lower_bound` combines the universal strict bound with that sequence of members of $V$. Every lower bound of $V$ is below every value of the sequence, hence below its limit $-8/27$. The sequence also witnesses nonemptiness of $V$. Finally `result : claim` joins the strict bound and the greatest-lower-bound statement.

## Falsifier

A positive real rate vector with $n\ge2$ and $\mathcal S(k)+\mathcal K(k)\le-8/27$ would contradict the strict clause. A lower bound of all of $V$ strictly greater than $-8/27$ would contradict the greatest-lower-bound clause.

The interpretation would miss the source question if the module used different cumulant ratios or omitted positive rate vectors. The definitions above match the source's inverse-rate expressions and the claim quantifies over every strictly positive real rate vector with at least two entries. The stochastic process and the renewal identities linking it to these rational expressions are not themselves formalized. The source's asymptotic minimum is read as a greatest lower bound over all sizes; no assertion about a finite-size minimizing topology is needed.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound.lean.json`.

Declaration statements:

- `result`: `sha256:385122505e4a3c94b17771a188428dc51828cdccfcc2ef1c3e2d6fccf2329694`;
- `claim`: `sha256:bb5ae3c1320acad0834b3aa8ef09e5b52cf91072b028b2670e171410da9177e5`.

## Triage

Tier 1 bound of a 2022 paper resting on a numerically conjectured extremal topology, preregistered in issue #25636 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n\ge2$ and every real rate vector $k:\mathrm{Fin}\,n\to\mathbb R$ whose entries are all strictly positive, $\mathcal S(k)+\mathcal K(k)>-8/27$; the same $-8/27$ is the greatest lower bound of the set of all these sums over all such $n$ and $k$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Decisive mechanism and scope.* The joint moments of the same normalized inverse-rate vector give exactly the conditions $p>0$, $q\ge0$, $q^2\le pr$ and $r<p^2$ used in the route. They imply $t\ge0$, $e\ge0$ and $d>0$; the low certificate is positive because of its constant term, while the high certificate is positive because $d(18d+36t^2-22t)>0$ for $t\ge11/18$. Thus the estimate does not depend on assuming any extremal topology. The same algebra applies to real moment triples satisfying all four conditions; it supplies no conclusion for triples lacking them.
- *Sharpness and limiting geometry.* For the positive family `sourceRates m` with natural $m\ge1$, normalization gives $x_0=2/3$ and $x_i=1/(3m)$ for $i\ne0$. Hence for every natural $j\ge2$, $\sum_i x_i^j=(2/3)^j+3^{-j}m^{1-j}$, which tends to $(2/3)^j$. Consequently $p\to4/9$, $q\to8/27$, $r\to16/81$, $t\to2/3$ and $e,d\to0$. This explains how strict positivity at every finite size is compatible with the sharp limiting endpoint certified by `source_limit`. With $N=m+1$ and $a=1/(2m)$, $Na=(m+1)/(2m)\to1/2$, matching the source's limiting parameter. The formula does not identify the minimizer for any fixed $N$.
- *Symmetries and an adjacent family.* For $n\ge2$, positive rates and any $c>0$, replacing $k_i$ by $ck_i$ multiplies $R_j$ by $c^{-j}$, which cancels in every term of both ratios. Permutations also preserve every power sum. These operations preserve the values and give corresponding approximating families. Equal positive rates instead give $R_j=n k^{-j}$, hence $\mathcal S=\mathcal K=1/n^2$ and $\mathcal S+\mathcal K=2/n^2>0$; that family cannot approach the negative endpoint.
- *Effect on the paper and neighbouring questions.* The settlement establishes the lower side of the source's sum interval for positive unidirectional cycles without its extremal-topology assumption. Its strict inequality excludes finite positive-cycle attainment of that endpoint. The finite-$N$ optimizer and curves in Fig. 7, the upper endpoint of the sum, the bounds on the difference and product, and the bidirectional extension in Section III E 2 remain outside this result. The source's inference of multicyclicity from violations of unicyclic bounds in Section IV B still needs a bound for bidirectional cycles when that class is allowed: exclusion of the unidirectional subclass alone does not exclude every unicyclic model. The separate heat-current question #22747 is unaddressed.

## ASSUMED-UNVERIFIED

The bounded literature check in #25636 does not establish exhaustive worldwide novelty or priority. The report that v4 is the latest version, the Semantic Scholar and OpenAlex citation listings, the search author's readings of arXiv:2305.09759, arXiv:2411.19643 and arXiv:2610.12652, and the repository and issue absence searches are not independently reproduced. The two unidentified OpenAlex citing works remain unread. The v4 conjecture, asymptotic endpoint and renewal formulas are checked against `main.tex`, md5 `5b72a7d5de1e5c34c76db21badb56492`.

The stochastic-process construction, the renewal identities as statements about that process, and the identification with a measured current-cumulant ratio are not formalized. The arguments in "Argued, not formalized" are not additional formal conclusions of `result`; the cited private lemmas have the hypotheses stated in the route. The finite-size optimizer, bidirectional extension, upper endpoint, difference and product questions listed above remain open here.
