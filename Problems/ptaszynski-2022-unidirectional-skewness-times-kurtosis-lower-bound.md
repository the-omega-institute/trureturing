---
slug: ptaszynski-2022-unidirectional-skewness-times-kurtosis-lower-bound
bibkey: ptaszynski2022skewness
doi: 10.1103/PhysRevE.106.024119
url: https://arxiv.org/abs/2204.08421v4
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/UnicyclicSkewnessTimesKurtosisLowerBound.result
---

# The sharp lower bound on skewness times kurtosis for unidirectional unicyclic currents

## Problem

K. Ptaszyński, *Bounds on skewness and kurtosis of steady-state currents*, Phys. Rev. E 106, 024119 (2022), arXiv:2204.08421v4, gives the following numerical conjecture in the Appendix (`main.tex`, line 792):

> it was numerically conjectured that the minimum and maximum values of $\mathcal{S}$, $\mathcal{K}$, $\mathcal{S}+\mathcal{K}$, $\mathcal{S}-\mathcal{K}$ and $\mathcal{S} \times \mathcal{K}$ are always obtained for a specific type of network topology, with all rates $k_{ij}$ equal to $k$ apart from one (here $k_{21}$) equal to $ak$, with the parameter $a$ depending on the optimized quantity and the number of states $N$.

For the product's lower endpoint, the subsection “Unidirectional networks” gives (`main.tex`, line 445):

> $\min(\mathcal{S} \times \mathcal{K})=\min_A \frac{1-10A+22A^2-12A^3}{(1+A)^8}$.

Line 424 specifies the limit $N\to\infty$ with $a=A/N$; line 439 gives the approximate minimum $-0.054$ at $A\approx0.23$. The summary's Eq. `produni` states $\mathcal{K}\times\mathcal{S}\in[-0.054,1]$ (lines 129–137), explicitly treating decimals as approximate. These quotations were checked against the v4 source member `main.tex`, MD5 `5b72a7d5de1e5c34c76db21badb56492`.

Issue [#25992](https://github.com/the-omega-institute/trureturing/issues/25992) fixes the reading to the sharp lower endpoint for unidirectional cycles. Write $R_j=\sum_{i=1}^N k_i^{-j}$ for a strictly positive real rate vector $k:\mathrm{Fin}\,N\to\mathbb R$, and use the existing definitions

$\mathcal S(k)=3R_2^2/R_1^4-2R_3/R_1^3$,

$\mathcal K(k)=15R_2^2/R_1^4-20R_3/R_1^3+6R_4/(R_1^2R_2)$.

These are `UnicyclicSkewnessMinimum.skewness` and `UnicyclicKurtosisLowerBound.kurtosis`, respectively. They match the source's current-cumulant ratios (lines 53–54) upon substitution of its waiting-time formulas (Appendix, lines 772–790); they are not the usual standardized third and fourth moments of a probability distribution.

Define $E(A)=(1-10A+22A^2-12A^3)/(1+A)^8$ and $C=\inf\{E(A):A>0\}$, the module's `lowerBound`. The statement is that $\mathcal S(k)\mathcal K(k)>C$ for every $N\ge2$ and every strictly positive real rate vector, and that $C$ is the greatest lower bound of all these products, allowing $N$ to vary. Both factors use the same vector; repeated rates are allowed. This is proved.

## Motivation

The product bound constrains two current-cumulant ratios jointly. Separate bounds on skewness and kurtosis do not supply the sharp product endpoint, because their extremal values need not occur for the same rate vector. Ptaszyński uses violations of the unicyclic bounds to infer multicyclic Markovian dynamics (`main.tex`, line 598 and Conclusions, line 759). Establishing the unidirectional lower endpoint supplies this part of that comparison for the inverse-rate model, while keeping its stochastic interpretation explicit.

## Gap

The literature check recorded in #25992 before any Lean reports:

- the arXiv v4 source retains the numerically conjectured extremal topology;
- the search contributor reports OpenAlex's five citing works and OpenCitations' six records, and readings of arXiv:2305.09759, 2411.19643, 2208.11206 and 2404.00422 without an exact supplier of this product endpoint;
- the repository's sibling settlements concern skewness, kurtosis, their sum and the upper skewness-minus-kurtosis endpoint, with no prior issue or dossier for the product endpoint in the searches recorded there.

`not-found-in-searched-scope`. The citation counts and four external readings are contributor-reported in #25992, not independently reproduced here. The v4 conjecture and endpoint were independently read in the source.

## Route

All lemma names below refer to `UnicyclicSkewnessTimesKurtosisLowerBound` unless another module is named. Put $f(u)=u^5(3u-2)(15u^2-20u+6)$ and $H(z)=z(3z-2)(15z^2-20z+6)$.

1. **A genuine infimum.** `source_bddBelow` proves that $\{E(A):A>0\}$ is bounded below, using $-100$ as a lower bound. It is nonempty, as witnessed by $A=1$ in `constant_minimum`. For $A>0$, `source_le_lower_bound` gives $C\le E(A)$. For $0<u<1$, `source_expression_eq_f` gives $E((1-u)/u)=f(u)$, and `f_lower_bound` gives $C\le f(u)$. `lowerBound_lt_three_eighty` gives $C<-3/80<0$ by evaluating $E(1/4)$.
2. **Joint moments.** For $N\ge2$ and $k_i>0$, set $x_i=k_i^{-1}/R_1$, $p=\sum_i x_i^2$, $q=\sum_i x_i^3$ and $r=\sum_i x_i^4$. `UnicyclicSkewnessPlusKurtosisLowerBound.normalized_moments`, with precisely these hypotheses on $N$ and $k$, supplies $p>0$, $q\ge0$, $q^2\le pr$ and $r<p^2$. `second_sq_le_third` assumes a finite vector $x$ with $x_i\ge0$ and $\sum_i x_i=1$, and gives $p^2\le q$; the positive normalized inverse rates satisfy those assumptions. `normalized_product` is an identity for every natural $N$ and every real vector $k$, expressing the product as $SK$ with $S=3p^2-2q$ and $K=15p^2-20q+6r/p$. In `strict_lower_bound`, the skewness minimum from `UnicyclicSkewnessMinimum.result`, for $N\ge2$ and positive $k$, also supplies $S\ge-1/16$.
3. **Nonnegative product and negative skewness.** `product_nonnegative` assumes real $p,q,r$ and $SK\ge0$ and gives $SK>C$. `product_skew_negative` assumes $p>0$, $r<p^2$, $S<0$, $K>0$ and $S\ge-1/16$. Under all these assumptions it obtains $K<6p-15p^2\le3/5$, hence $SK>-3/80>C$.
4. **Negative kurtosis.** `product_kurtosis_negative` assumes real $p,q,r$ with $p>0$, $q^2\le pr$, $r<p^2$, $p^2\le q$, $S>0$ and $K<0$. Set $t=q/p$ and $z=p^2/q$. These hypotheses give $0<t<z<1$ and $K_0=15p^2-20q+6t^2\le K<0$, with $H(z)<0$. Thus $SK\ge SK_0=t^4H(z)>f(z)\ge C$. The strict step is `f_strict_scale`, whose complete hypotheses are $0<t$, $t<z$ and $H(z)<0$. Together the three sign cases give `strict_lower_bound` for every $N\ge2$ and strictly positive $k$.
5. **Sharpness.** For $0<u<1$ and natural $m\ge1$, `source_rates_positive` proves positivity of `sourceRates u m`, the $m+1$ rates with exceptional rate $(1-u)/(mu)$ and all other rates equal to $1$. With the same hypotheses, `source_value` gives their product from the normalized moments $u^j+(1-u)^j/m^{j-1}$ for $j=2,3,4$. `source_limit`, assuming $0<u<1$, proves that the products for `sourceRates u (m+1)` tend to $f(u)$ as natural $m\to\infty$; these cycles have $m+2$ states. `constant_minimum` proves the existence of $0<u<1$ with $f(u)=C$, using a minimum of the continuous polynomial on $[0,1]$, $f(0)=0$, $f(1)=1$ and $f(4/5)<0$. `greatest_lower_bound` passes any lower bound of the full product set to this limit, proving `IsGLB`. Finally, `result : claim` combines this assertion with the strict inequality.

## Falsifier

A proof confined to the one-exceptional-rate family would not establish a universal bound. Here `claim` quantifies over every strictly positive real vector on every $N\ge2$, and the special family supplies sharpness. The source's rounded $-0.054$ is replaced by the exact infimum $C$; neither equality at a finite cycle nor a finite-size optimizer is asserted.

The source's Appendix formulas identify the rational expressions with ratios of winding-current cumulants. The module reuses those expressions; it does not construct a Markov process or prove the renewal-cumulant correspondence. Its $N=2$ input is a two-stage oriented cycle with a marked winding crossing. No physical $N=1$ case, zero or negative rate, bidirectional extension or upper product endpoint is part of `claim`.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/UnicyclicSkewnessTimesKurtosisLowerBound.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/UnicyclicSkewnessTimesKurtosisLowerBound.lean.json`.

Declaration statements:

- `result`: `sha256:39ef5a9cafc720f78046f8a0e279441017b6786a64202fdcaa35f4dc660e4f7d`;
- `claim`: `sha256:ce7d5d1a8c04bcc7ad47b2b042f992d9b20d49ecf2241de4262425b6f5f44cfd`.

## Triage

Tier 1 numerical conjecture of a 2022 paper, preregistered in issue #25992 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $N\ge2$ and every strictly positive real rate vector $k:\mathrm{Fin}\,N\to\mathbb R$, $C<\mathcal S(k)\mathcal K(k)$, and $C$ is the greatest lower bound of the set of these products over all such $N$ and $k$, where $C=\inf\{E(A):A>0\}$.

**Computed, not formalized:** None.

**Argued, not formalized**.

- *Decisive mechanism.* The proof keeps the second, third and fourth moments of a common normalized inverse-rate vector together. In particular, under the full hypotheses $p>0$, $q^2\le pr$, $r<p^2$, $p^2\le q$, $S>0$ and $K<0$ of `product_kurtosis_negative`, it is the strict inequality $t<z$ and the sign $H(z)<0$ that turn a comparison with the limiting family into a strict finite-cycle bound. The other negative-product case, under $p>0$, $r<p^2$ and $-1/16\le S<0<K$ as required by `product_skew_negative`, stays above $-3/80$. Thus a sequence of positive finite cycles approaching the sharper negative endpoint must eventually lie in the positive-skewness, negative-kurtosis branch.
- *Scope and sharpness.* The greatest-lower-bound clause excludes every larger uniform lower bound: any proposed lower bound $b>C$ would contradict its maximality. The strict inequality excludes finite attainment for every positive vector with $N\ge2$. Whether the one-exceptional-rate family minimizes the product for each fixed $N$, and whether the fixed-size infima decrease monotonically, are not settled here.
- *Matching the source's scaling.* For fixed $A>0$ and $N\ge2$, the source's exceptional rate $A/N$ has normalized exceptional inverse rate $N/[N+A(N-1)]\to u=1/(1+A)$ as $N\to\infty$. Its other $N-1$ coordinates each equal $A/[N+A(N-1)]$, whose combined $j$th powers tend to zero for $j=2,3,4$. Thus their moments tend to $u^j$; since $u^2>0$, substitution in the displayed expressions gives the same limiting product $f(u)$. The module's family has exceptional rate $A/(N-1)$, as follows from `sourceRates` with $0<u<1$, natural $m=N-1\ge1$ and $A=(1-u)/u$. These are distinct finite families with the same asymptotic scaling.
- *Effect on the paper.* Conditional on the source's correspondence between cumulant ratios and positive inverse-rate expressions for a finite unidirectional cycle, a measured product at or below $C$ contradicts that model class. This supplies the lower-product part of the paper's diagnostic within that class. The broader multicyclicity inference in `main.tex`, line 598, also needs the bidirectional bound and the physical modeling assumptions, which `result` does not establish. The source's finite-size curves and state-number inference (line 499), upper endpoint (line 440) and numerical bidirectional extension (line 524) receive no additional proof from this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check in #25992 does not establish exhaustive worldwide novelty or priority. Its OpenAlex and OpenCitations counts, membership of those citation lists and readings of arXiv:2305.09759, 2411.19643, 2208.11206 and 2404.00422 were not independently reproduced. The journal body was not read; the source quotations and formulas were checked in arXiv:2204.08421v4. The numerical rate-vector sample and symbolic checks reported by other contributors in #25992 were not reproduced and are not used as proof.

The arguments under “Argued, not formalized” are not additional compiled conclusions of `result`. The stochastic construction, renewal asymptotics, empirical correspondence, bidirectional lower bound, upper product endpoint, fixed-size optimizer topology and monotonicity of fixed-size infima remain outside this formalization. The two-stage, marked-crossing interpretation at $N=2$ is not a stochastic-process theorem of the module; no physical $N=1$ assertion is made.
