---
slug: ptaszynski-2022-unicyclic-skewness-minimum
bibkey: ptaszynski2022skewness
doi: 10.1103/PhysRevE.106.024119
url: https://arxiv.org/abs/2204.08421v4
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.result
---

# The minimum skewness of a unidirectional unicyclic current

## Problem

K. Ptaszyński, *Bounds on skewness and kurtosis of steady state currents*, Phys. Rev. E 106, 024119 (2022), arXiv:2204.08421v4, Appendix, `main.tex` line 792:

> As discussed in Sec.~\ref{subsec:unmark}, it was numerically conjectured that the minimum and maximum values of $\mathcal{S}$, $\mathcal{K}$, $\mathcal{S}+\mathcal{K}$, $\mathcal{S}-\mathcal{K}$ and $\mathcal{S} \times \mathcal{K}$ are always obtained for a specific type of network topology, with all rates $k_{ij}$ equal to $k$ apart from one (here $k_{21}$) equal to $ak$, with the parameter $a$ depending on the optimized quantity and the number of states $N$.

The Appendix, `main.tex` line 804, specifies the skewness minimum:

> The minimum value $\min (\mathcal{S})$ is found for $a=1/(N-1)$; it is given by Eq.~\eqref{skewunidet}.

The reading fixed in issue [#22468](https://github.com/the-omega-institute/trureturing/issues/22468) concerns only the minimum skewness for unidirectional cycles. For every integer $N\ge2$ and positive clockwise rates $k_i$, put

$R_j=\sum_{i=0}^{N-1}k_i^{-j},\qquad \mathcal{S}(k)=3R_2^2/R_1^4-2R_3/R_1^3,\qquad g(N)=-\frac{8-8N+N^2}{16(N-1)^2}.$

The claim is that $g(N)$ is the least value of $\mathcal{S}(k)$ over all such positive rate vectors, including attainment. The source's candidate rates are $(1/(N-1),1,\ldots,1)$, up to an overall positive scale. This minimum claim is proved.

The source defines $\mathcal{S}$ as the third scaled current cumulant divided by the first, rather than the standardized third central moment. Its definition is at `main.tex` line 53; the Appendix's current and waiting-time cumulant formulas at lines 772–789 give the expression above. The finite-$N$ candidate is displayed in Section III E 1, lines 417–423. See [the literature note](../Library/StatisticalMechanics/ptaszynski2022skewness.md).

## Motivation

A sharp lower bound separates variation of positive rates within a unidirectional cycle from departure from that model: a smaller value cannot come from any rate vector covered by the claim. The dependence on $N$ constrains the possible state counts. The source uses current-cumulant bounds to diagnose transport networks; the present settlement supplies the unidirectional skewness-minimum component of that programme.

## Gap

Issue #22468 records the bounded literature check:

- The v4 source explicitly presents the extremal topology as numerically conjectured.
- The orchestrator's web search found the source and a different unicyclic conjecture, but no proof of this finite-$N$ minimum; its Zenodo search found no related record.
- The search author reports no proof in the four citing works identified in #22468, and no match in MathDB or formal-conjectures.
- The issue records no existing repository settlement.

`not-found-in-searched-scope`.

## Route

Write $F(x)=3(\sum_i x_i^2)^2-2\sum_i x_i^3$, the module's private `simplexFunctional`.

1. **Normalize inverse rates.** For a natural $N>0$, $k:\mathrm{Fin}\,N\to\mathbb{R}$ and $k_i>0$ for every $i$, `normalized_simplex` proves that $x_i=k_i^{-1}/R_1$ belongs to the closed standard simplex: $x_i\ge0$ and $\sum_i x_i=1$. For every natural $N$ and every real rate vector $k$, without positivity hypotheses, `skewness_normalized` proves the total-real-arithmetic identity $\operatorname{skewness}(k)=F(x)$; positivity is needed for the simplex interpretation.
2. **Control the moments.** For $N\ge2$ and any $x:\mathrm{Fin}\,N\to\mathbb{R}$ in that closed simplex, `simplex_lower_bound` chooses a largest coordinate $a=x_i$, and sets $r=N-1$, $b=(1-a)/r$, $p=\sum_jx_j^2$, $q=\sum_jx_j^3$. It obtains $r\ge1$, $a+rb=1$, $b\le a$ and $a\ge0$. Retaining the $i$th term in the nonnegative sum $\sum_j(x_j-b)^2$ gives $p\ge a^2+rb^2$; summing $(a-x_j)(x_j-b)^2\ge0$ gives $q\le(a+2b)p-2ab-b^2+(r+1)ab^2$.
3. **Complete squares.** For real $r,a,b,p,q$ satisfying all six conditions $r\ge1$, $a+rb=1$, $b\le a$, $a\ge0$, $p\ge a^2+rb^2$ and $q\le(a+2b)p-2ab-b^2+(r+1)ab^2$, `algebra_lower_bound` proves $3p^2-2q\ge-(r^2-6r+1)/(16r^2)$. Its proof separates $3a-1\ge0$ from $3a-1<0$, with the latter case forcing $r\ge2$, and controls the remaining correction by completing a square. Applying it to the moments in item 2 proves `simplex_lower_bound`: for $N\ge2$ and $x$ in the closed standard simplex, $F(x)\ge g(N)$.
4. **Attain and conclude.** For every natural $N\ge2$, `attaining_rates` proves the existence of a positive rate vector with $g(N)=\operatorname{skewness}(k)$. Its proof writes $N=m+1$ with $m>0$ and uses $k_0=m^{-1}$ and $k_i=1$ for $i\ne0$; the inverse-rate power sum of degree $j\in\mathbb{N}$ is $m^j+m$. For every $N\ge2$, `result` combines this membership witness with the normalized-simplex lower bound to prove `IsLeast` for the set of positive-rate skewness values.

## Falsifier

A positive rate vector with $N\ge2$ and $\mathcal{S}(k)<g(N)$, or failure of attainment for any such $N$, would contradict the claim. The interpretation would miss the source problem if the encoded quantity were a different normalization of skewness, or if the rate domain omitted positive vectors.

The module uses exactly the displayed inverse-rate expression and quantifies over every real vector indexed by $\mathrm{Fin}\,N$ with all entries strictly positive. The correspondence to current cumulants is substitution into the source formulas, not a formal construction of a stochastic process. The claim uses `IsLeast`, which includes membership as well as the lower bound; it does not rely on a possibly empty infimum. The restrictions to $N\ge2$ and unidirectional positive rates are essential to the stated scope.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.lean.json`.

Declaration statements:

- `result`: `sha256:8ff4a0e5d9228d44cdc8ae0404487b8f7fd337c60b21ee1570d9bdf006f8896a`;
- `claim`: `sha256:dc46429d5b4a694b8eb32121530ad4d4cb4fb7b6f3e122c7ae8c4df53ce40bd3`.

## Triage

Tier 1 numerically conjectured extremal structure of a 2022 paper, preregistered in issue #22468 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $N\ge2$, $g(N)$ belongs to the set of skewness values of strictly positive real rate vectors indexed by $\mathrm{Fin}\,N$ and is no larger than any member of that set. Thus the lower bound is sharp and attained for every such $N$.

**Computed, not formalized.**

- Exact rational evaluation of the constructed attaining family gives $\mathcal{S}=g(N)$ for every integer $2\le N\le128$.
- The orchestrator's numerical minimization recorded in #22468 reports values at $g(N)$ and no values below it for the tested positive-rate families with $N=2,\ldots,8$.

**Argued, not formalized.**

- *Mechanism and boundary.* For $N\ge2$ and nonnegative $x$ with $\sum_i x_i=1$, `simplex_lower_bound` uses a maximal coordinate and two nonnegative moment sums to obtain $F(x)\ge g(N)$, as detailed in the route. This includes zero coordinates. Such coordinates cannot arise from finite positive rates, because $k_i^{-1}/R_1>0$ for those rates; the closed-simplex extension therefore does not by itself enlarge the physical rate domain.
- *Symmetries and uniqueness.* For positive rates and $c>0$, rescaling $k_i$ to $ck_i$ multiplies $R_j$ by $c^{-j}$, which cancels in each term of $\mathcal{S}$. Permuting coordinates preserves every $R_j$. Thus positive rescalings and permutations of the attaining vector also attain the value. Whether these exhaust all minimizers is open here.
- *Uniform rates.* Equal positive rates give $R_j=N k^{-j}$ and hence $\mathcal{S}=1/N^2$. Expanding the difference gives $1/N^2-g(N)=(N-2)^4/[16N^2(N-1)^2]$. It vanishes at $N=2$ and is strictly positive for every integer $N>2$, so a homogeneous cycle is not minimizing in those larger dimensions.
- *Limit over state counts.* Adding $1/16$ to the displayed expression for $g(N)$ gives $(6N-7)/[16(N-1)^2]$, positive for $N\ge2$ and tending to zero as $N\to\infty$. The formal finite-$N$ bound therefore implies $\mathcal{S}>-1/16$ for every admissible finite cycle. Since each $g(N)$ is attained, these values approach $-1/16$, making it the infimum across all state counts, without finite-$N$ attainment of that infimum. These limit and infimum consequences are not separate Lean declarations.
- *Effect on the paper and neighbouring questions.* The settlement removes the conjectural topology assumption for the unidirectional skewness-minimum formula in Section III E 1 and its finite-state curve in Fig. 4. The preceding limit argument supplies the lower side of the source's state-independent skewness interval for unidirectional cycles. It supplies no proof of the upper side, the kurtosis or combined bounds, or the bidirectional extension in Section III E 2. Consequently the paper's broader deductions about bidirectional networks, near-equilibrium behaviour and multicyclicity do not acquire a proof from this settlement. Equality classification and extension of the moment argument to the other cumulant combinations remain open here.

## ASSUMED-UNVERIFIED

The bounded literature check in #22468 does not establish exhaustive worldwide novelty or priority. The orchestrator's web and Zenodo searches, the search author's four citing-work readings and MathDB/formal-conjectures checks, and the issue's repository-wide absence check are not independently reproduced. The v4 TeX quotations and formulas are checked against `main.tex`; the current-cumulant and renewal-process interpretation of the rate expression is not formalized.

The statements in "Computed, not formalized" and "Argued, not formalized" are not additional formal conclusions of `result`. The numerical optimization reported in #22468 is not independently reproduced, and finite computations imply nothing about untested cases. No classification of all minimizers, bidirectional minimum, skewness maximum, kurtosis bound or combined-cumulant bound is settled here.
