---
slug: szalay-toth-2025-entanglement-depth-generator-injectivity
bibkey: szalaytoth2025entanglementdepth
doi: 10.22331/q-2025-04-18-1718
url: https://arxiv.org/abs/2408.15350v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.result
---

# Noninteger parameters do not ensure injectivity of the Szalay–Tóth partition generators

## Problem

Sz. Szalay and G. Tóth, *Alternatives of entanglement depth and metrological entanglement criteria*, arXiv:2408.15350v3; Quantum 9, 1718 (2025), Section 4.7, state:

> On the other hand, for $q\not\in\field{N}$ the equation becomes transcendental, and we expect the injectivity of $s_q$.

> For the case $d\not\in\field{N}$, we expect the injectivity of $\Dim_d$,
> although the meaning of $\Dim_d$ is not established for noninteger $d$,
> which is just a parameter then.

These are verbatim TeX quotations from `depths.tex`, line 2437 and lines 2445–2447, respectively, in the v3 source archive (MD5 `bbacd570d915c7fdda31d547fe476fec`). The source macros `\field{N}` and `\Dim_d` denote $\mathbb N$ and $\operatorname{Dim}_d$.

An integer partition $\xi$ of $n$ is a multiset of positive integers summing to $n$ (`depths.tex`, lines 462–466). The source defines
$s_q(\xi)=\sum_{x\in\xi}x^q$ for real $q$ (Eq. `eq:sq`, lines 1903–1907), and
$\operatorname{Dim}_d(\xi)=\sum_{x\in\xi}d^x$ (Eq. `eq:Dimd`, lines 2306–2312). Repetitions contribute with their multiplicities. For the second expectation, $d\ge2$ remains a mathematical parameter; a noninteger value is not a Hilbert-space dimension.

Issue [#21841](https://github.com/the-omega-institute/trureturing/issues/21841) fixes `claim` as the disjunction of these two assertions:

- For every $n\in\mathbb N$ and every real $q$ unequal to every natural number, $s_q$ is injective on the partitions of $n$.
- For every $n\in\mathbb N$ and every real $d\ge2$ unequal to every natural number, $\operatorname{Dim}_d$ is injective on the partitions of $n$.

The theorem `result : ¬ claim` refutes both universal assertions.

## Motivation

These generators assign numerical labels to multipartite entanglement properties indexed by integer partitions. Injectivity would distinguish every partition and put their generator values in a total order, as discussed in Section 3.2 (`depths.tex`, lines 1166–1175). The expectations ask whether choosing a noninteger parameter removes the collisions noted for integer parameters. Their failure identifies information lost by these numerical labels, including by subsequent strictly monotone transformations.

## Gap

The bounded literature check recorded in #21841 reports:

- The orchestrator read the v3 TeX, searched for power-sum injectivity with noninteger exponents, searched Zenodo, and found no pre-existing repository entry or settlement in those searches.
- The search author reported that arXiv v1–v3 and the published PDF retain the expectations, that seven citing full texts contain no settlement, and that `google-deepmind/formal-conjectures` has no match.
- MathDB and OpenAlex requests were blocked with HTTP 403 and 429, respectively.

`not-found-in-searched-scope`. The v3 TeX quotations are independently checked; the remaining reported readings and searches are not independently reproduced.

## Route

1. **Partitions and distinctness.** `power_left` and `power_right` are the partitions $\{9,1,1,1\}$ and $\{4,4,4\}$ of $12$. `dimension_left` has two threes and twenty ones, and `dimension_right` has thirteen twos, both summing to $26$. The latter uses `GawronUlasFactorialSignConjecture.partition126 n y z h`, whose hypothesis is $2y+6z\le n$, at $(n,y,z)=(26,13,0)$. `Nat.Partition.ofSums` requires the stated sum and removes zero entries; all the displayed entries are positive. The fixed-witness lemmas `power_distinct` and `dimension_distinct` prove distinctness using membership of $9$ and $3$, respectively; neither lemma has additional hypotheses.
2. **Admissible parameters.** `BesselProductOrderLogConvexity.Result.half_noninteger` states, for every pair of integers $k,m$, that $(k:\mathbb R)+1/2\ne(m:\mathbb R)$, with no additional hypotheses. Its instances at $k=0$ and $k=2$, with natural numbers included into the integers, give `half_not_nat` and `five_halves_not_nat`. Rational arithmetic also gives $2\le5/2$.
3. **The power collision.** `StrictSpectralPolyaRefutation.rpow_square_half` states $(a^2)^{p/2}=|a|^p$ for all real $a,p$, with no additional hypotheses. At $(a,p)=(3,1)$ and $(2,1)$, positivity of $3$ and $2$ gives $9^{1/2}=3$ and $4^{1/2}=2$. The fixed-witness lemma `power_values` proves $s_{1/2}(\{9,1,1,1\})=6$ and $s_{1/2}(\{4,4,4\})=6$; it has no additional hypotheses.
4. **The dimension collision.** The fixed-witness lemma `dimension_values`, with no additional hypotheses, proves both values are $325/4$ at $d=5/2$: $2(5/2)^3+20(5/2)=13(5/2)^2=325/4$.
5. **Negation of the disjunction.** In `result`, the first alternative of `claim`, specialized to $n=12,q=1/2$, contradicts `power_distinct` using `power_values`. The second alternative, specialized to $n=26,d=5/2$ with $2\le5/2$ and `five_halves_not_nat`, contradicts `dimension_distinct` using `dimension_values`.

## Falsifier

A collision would not refute these expectations if it compared different totals, used a forbidden parameter, counted repeated parts only once, or involved zero parts removed by the partition constructor. The module uses `Nat.Partition n`, real powers of the positive natural parts for `powerSum`, and natural powers of a real base for `entanglementDimension`. Both pairs have equal totals, positive parts and unequal multisets. The parameters $1/2$ and $5/2$ satisfy the exact nonintegrality conditions of `claim`, and $5/2\ge2$. The examples have positive $n$ and positive parameters, so they also lie within those restrictions on the source's domain.

## Evidence

The canonical source is `D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.lean` (100 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Combinatorics/Partitions/EntanglementDepthGeneratorInjectivityRefutation.lean.json`, statement `sha256:3fa70995691f6e33373b14ee25141fe895678b69dfd62cbc5bb2ba4755b6bd01`.

Declaration statements:

- `result`: `sha256:ec3eb69547da03d7ba5ed6cf30c483a1de73a67a73f72381a794c1db74b24b9a`;
- `claim`: `sha256:aa6402e57d04f423ecf4ee6c9378d218e85ad15ee7063b04449eb86553becc12`.

## Triage

Tier 1: two explicitly stated expectations in a 2025 journal article, preregistered in issue #21841 before any Lean.
`theorem`; resolution `refuted`.

The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the disjunction defining `claim` is false: neither injectivity of $s_q$ for every $n$ and every real $q$ outside the natural numbers, nor injectivity of $\operatorname{Dim}_d$ for every $n$ and every real $d\ge2$ outside the natural numbers, is true.

**Computed, not formalized** (exact Python integer and rational arithmetic):

- The difference of the dimension polynomials of the displayed pair is $P(t)=2t^3-13t^2+20t=t(2t-5)(t-4)$. Its value at $5/2$ and its derivative at $1$ are both zero.
- The source's projective dimension, $\operatorname{Dim}'_d(\xi)=\operatorname{Dim}_d(\xi)-|\xi|+1$ (Eq. `eq:Dimpd`, lines 2323–2326), takes the unequal values $241/4$ and $277/4$ on the dimension witnesses at $d=5/2$. Thus this tested pair is not a collision for that different function.

**Argued, not formalized.**

- *Power mechanism.* The source's $q=2,n=6$ example in Section 4.7 compares $\{3,1,1,1\}$ with $\{2,2,2\}$: both have sum $6$ and sum of squares $12$. Squaring each part therefore produces partitions of $12$ whose square-root sums are both $6$. A noninteger exponent does not force transcendental values on integer parts; perfect squares retain an exact arithmetic relation at exponent $1/2$.
- *Dimension mechanism and a sufficient repair.* For distinct partitions, let $c_j$ be the difference between the multiplicities of part $j$. Their dimension difference is the nonzero integer polynomial $P(t)=\sum_jc_jt^j$. Equal partition totals give $P'(1)=\sum_jjc_j=0$, but do not prevent $P$ from having a noninteger root at least $2$, as the computed factorization illustrates. Requiring $d\ge2$ to be transcendental is sufficient for injectivity: a collision would make this nonzero integer polynomial vanish at a transcendental number, contrary to its definition. For each fixed $n$, there are finitely many partition pairs and each nonzero difference polynomial has finitely many roots, so only finitely many bases can be exceptional. These are ordinary mathematical arguments, not declarations of this module.
- *Larger totals.* For any natural $r$, adding $r$ ones to both members of the power pair preserves distinctness and adds $r$ to both power sums. This gives a collision at $q=1/2$ for every total $12+r$. The same operation on the dimension pair preserves distinctness and adds $5r/2$ to both dimension sums, giving a collision at $d=5/2$ for every total $26+r$. Distinctness persists because only one member contains $9$, respectively $3$. These extensions are not statements of `result`.
- *Effect on the source's transformed generators.* If $f(\xi)=f(\upsilon)$, then $g(f(\xi))=g(f(\upsilon))$ for every function $g$ defined at that common value. At fixed $n,q$, the source's $N_q,T_q,R_q,P_q$ formulas depend only on $s_q$ (lines 1909–1915, 2080–2098 and 2143–2150). They inherit the power pair's collision at $n=12,q=1/2$, where their formulas are defined. Likewise $\operatorname{DoF}_d=\log_d\operatorname{Dim}_d$ (lines 2344–2350) inherits the dimension collision at $d=5/2$. This does not transfer to $\operatorname{Dim}'_d$, which also depends on the number of parts.
- *Effect on other conclusions.* The conditional total-order conclusion of Sections 3.2 and 4.7 still requires injectivity; nonintegrality cannot supply that premise at the displayed parameters. The general classification construction expressly permits noninjective generators (lines 943–946 and 1173–1175), so these collisions do not contradict that construction. Section 5.1's statement relating optimization over all generators to a bound using injective generators (lines 2818–2820) is not restricted to these two parameter families. Its validity and the paper's metrological inequalities are not settled by this refutation. The collision-free parameter ranges for $s_q$ and the full exceptional-base classification for $\operatorname{Dim}_d$ remain open here.

## ASSUMED-UNVERIFIED

The bounded literature check in #21841 does not establish exhaustive worldwide novelty or priority. Only the v3 TeX reading is independently reproduced. The v1–v2 and published-PDF readings, seven citing-full-text readings, web and Zenodo searches, formal-conjectures search, and report of no pre-existing repository record are attributed to the issue's authors and are not independently reproduced. MathDB and OpenAlex remain unverified because the reported requests were blocked.

The polynomial factorization, derivative, projective-dimension values, sufficient transcendental-base condition, finite-exception argument, padding extensions, consequences for transformed generators and analysis of the paper's other conclusions are not formalized in this module. No minimality of either witness size, classification of other parameters, quantum-state realization, or verification of the source's physical inequalities is claimed.
