---
slug: caro-graswald-2021-markovian-divisibility-maximal-index
bibkey: carograswald2021markovian
doi: 10.1063/5.0031760
url: https://arxiv.org/abs/2009.06666v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex.result
---

# The Caro–Graswald maximal index is $2d-5$ for $d\ge5$, with $h(3)=2$

## Problem

M. C. Caro and B. R. Graswald, *Necessary Criteria for Markovian Divisibility of Linear Maps*, Journal of Mathematical Physics 62, 042203 (2021), arXiv:2009.06666v3, Conjecture 4.19 (`CnjAMGMMatrices`), `main.tex` lines 728–738, state the following. The source macro `\IR` is expanded to $\mathbb{R}$.

> Let $p\in\mathbb{R}^d_{\geq 0}$ with $\sum\limits_{i=1}^d p_i = 1$. Define the matrices $a,g\in\mathbb{R}^{d\times d}$ via
>
> $a_{ij} = \frac{p_i + p_j}{2},\quad g_{ij}=\sqrt{p_i p_j}.$
>
> Denote by $a_k^\downarrow$ and $g_k^\downarrow$ the $k^{th}$ largest entry of $a$ and $g$, respectively. Define
>
> $A = \sum\limits_{k=1}^{h(d)} a_k^\downarrow,\quad G = \sum\limits_{k=1}^{h(d)} g_k^\downarrow.$
>
> We conjecture that the maximal integer $h(d)$ such that $A+G\leq d$ holds for any probability vector $p$ is given by $h(d) = 2d-5$.

For a nonnegative real probability vector $p$ of dimension $d$ and a natural index $m$, write $A_m(p)$ and $G_m(p)$ for the sums of the largest $\min(m,d^2)$ entries of $a$ and $g$, respectively. Each sum uses its own ordering, and repeated values at distinct ordered positions count separately. Put $S_d=\{m\in\mathbb{N}:\forall p\in\Delta_d,\ A_m(p)+G_m(p)\le d\}$, where $\Delta_d$ is the set of nonnegative vectors with coordinate sum one.

Issue [#22748](https://github.com/the-omega-institute/trureturing/issues/22748) fixes the statement: $2d-5$ is the greatest element of $S_d$ for every $d\ge5$, and $2$ is the greatest element of $S_3$. This statement is proved. The conjecture itself gives no additional dimension restriction; its printed formula gives $1$ at $d=3$, whereas the formal result gives $2$.

## Motivation

Caro and Graswald (2021), arXiv:2009.06666v3, relate infinitesimal Markovian divisibility of quantum channels to bounds on their determinant by products of their smallest singular values. Their Corollary `CrlQuDetVSProductSmallestSV`, `main.tex` lines 703–705, uses $\lfloor2d-2\sqrt{2d}+1\rfloor$ factors. The reduction at lines 719–740 identifies the probability-vector inequality as a sufficient step toward using $2d-5$ factors, approaching the example-based ceiling of $2d-2$ factors at lines 707–716. The source and its conjecture are also described in [the literature note](../Library/Eigenstructure/carograswald2021markovian.md).

## Gap

The bounded literature check recorded in #22748 reports:

- the conjecture remains in arXiv v3 and in the journal text reproduced in Caro's thesis;
- MathDB record 347947 lists the maximal-index conjecture as open, and the formal-conjectures repository has no matching entry;
- the three citing records listed by INSPIRE, namely Caro's thesis, arXiv:2201.12524 and arXiv:2109.03847, contain no settlement found by that check;
- the recorded repository searches found no existing settlement.

The v3 conjecture is verified directly from the source. The other reported literature readings are not independently reproduced here. The literature status is `not-found-in-searched-scope`.

## Route

All lemma names below refer to the canonical module, including its private helpers.

1. **Arithmetic coefficients.** For any dimension, real vector $p$ and finite set $S$ of ordered positions, `arithmetic_coefficients` writes $\sum_S a_{ij}=\sum_i c_i p_i$ with $c_i\le(|S|+1)/2$ and $c_i+c_j\le|S|/2+2$ for distinct $i,j$. For a probability vector, `probability_weighted_bound` applies whenever $c_i\le u$, $c_i+c_j\le v$ for distinct $i,j$, $v\le2u$, $t\ge1/2$ and $p_i\le t$ for every $i$; its conclusion is $\sum_i c_i p_i\le(2t-1)u+(1-t)v$.
2. **Geometric concentration.** For every probability vector, `geometric_square_sum` gives $\sum_{i,j}g_{ij}^2=1$, and `geometric_coarse_bound` bounds the sum on any finite position set $T$ by $\sqrt{|T|}$. For a probability vector, an index $i$ satisfying $p_j\le p_i$ for every $j$, and a nonempty finite position set $T$, `geometric_refined_bound` gives $\sum_Tg_{ij}\le p_i+\sqrt{|T|-1}\sqrt{1-p_i^2}$, with natural subtraction in $|T|-1$.
3. **Admissibility for $d\ge5$.** In `selected_mean_bound`, $p$ is a probability vector and the independently chosen sets $S,T$ both have cardinality $2d-5$. Put $t=\max_i p_i$, $u=d-2$ and $v=d-1/2$. If $t\le1/2$, the arithmetic sum is at most $d/2-1/4$ and the geometric sum at most $\sqrt{2d-5}\le d/2-1/4$. If $t>1/2$, their sum is at most $3/2+(d-5/2)t+\sqrt{2d-6}\sqrt{1-t^2}\le d$, by Cauchy–Schwarz and $0\le t\le1$. For $d\ge5$ and every probability vector $p$, `main_bound` applies this to sets attaining the two finite maxima and gives $A_{2d-5}(p)+G_{2d-5}(p)\le d$.
4. **Failure at the next index.** For every $d\ge5$, `failure_next` constructs a probability vector with $A_{2d-4}+G_{2d-4}>d$. Write $r=d-2$, $k=d-3$ and $N=r^2+k$. The vector has mass $r^2/N$ at coordinate $0$, mass $1/N$ at each coordinate $1,\ldots,d-3$, and zero at the two remaining coordinates. Let $C$ consist of $(0,0)$ and both cross positions between $0$ and $1,\ldots,d-3$. The arithmetic selection $C\cup\{(0,d-2)\}$ and geometric selection $C\cup\{(1,1)\}$ each have size $2d-4$; their sums total $d+(d-4)^2/(2N)>d$. They provide a lower bound on the two top sums, which suffices for the strict violation.
5. **Dimension three.** For any dimension and probability vector, `arithmetic_two_bound` bounds the arithmetic sum on any position set of cardinality two by $3/2$, and `geom_le_arith` bounds each geometric entry by the corresponding arithmetic entry. For every probability vector of dimension three, `three_bound` consequently gives $A_2+G_2\le3$. The existential statement `three_failure` uses $p=(4/5,1/5,0)$: on the three positions $(0,0),(0,1),(1,0)$, the selected arithmetic and geometric sums are $9/5$ and $8/5$, so $A_3+G_3\ge17/5>3$.
6. **Greatest elements.** For any pointwise nonnegative position function, `top_sum_mono` makes its top sums nondecreasing in the natural index, including beyond saturation. For any natural $d,m$, `greatest_of_bound_failure` requires both $m\in S_d$ and a probability vector violating the inequality at $m+1$; it concludes that $m$ is the greatest element of $S_d$. These hypotheses are supplied at $m=2d-5$ for $d\ge5$ and at $m=2$ for $d=3$.

## Falsifier

A mismatch in quantifiers, multiplicities or optimization would prevent the result from answering the source question. The definitions retain every nonnegative probability vector, including vectors with zero coordinates. `arith` and `geom` use `PowerMeanKernel.meanOne` and `meanZero`, which are exactly $(x+y)/2$ and $\sqrt{xy}$. `topSum` is the maximum over all position sets of cardinality $\min(m,d^2)$; the candidate family is finite and nonempty, with its nonemptiness supplied in the definition. It therefore selects the largest entries with multiplicity, permits different selections for the two matrices, includes the empty selection at $m=0$, and saturates at all $d^2$ positions. `IsGreatest` asserts membership and an upper bound on every admissible index, rather than merely naming a supremum.

The dimension restriction is material: the settlement includes the corrected value at $d=3$ and makes no greatest-element assertion for $d=0,1,2,4$.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex.lean`.

- **Proof.** It proves `result : (∀ d : ℕ, 5 ≤ d → IsGreatest (admissibleIndices d) (2 * d - 5)) ∧ IsGreatest (admissibleIndices 3) 2`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex.lean.json`.

Declaration statements:

- `result`: `sha256:ee2ade07fab8ec70a62aad80b5ae9386dbbc4160b0123bf7336ff3b761ac0bb8`.

## Triage

Tier 1 conjecture of a 2021 paper, preregistered in issue #22748 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural dimension $d\ge5$, $2d-5$ belongs to $S_d$ and every element of $S_d$ is at most $2d-5$; also, $2$ belongs to $S_3$ and every element of $S_3$ is at most $2$.

**Computed, not formalized:** random numerical search with local refinement in small dimensions, recorded by the orchestrator in #22748, found no value above the proposed exact optimum and no violation of the bound at $d=4$.

**Argued, not formalized.**

- *Decisive mechanism.* For a probability vector, `arithmetic_coefficients` bounds single coefficients and pairs of distinct coefficients for any selected arithmetic position set, while `geometric_refined_bound` controls a nonempty geometric selection using a coordinate maximizing that same probability vector. Under the hypotheses of `selected_mean_bound` ($d\ge5$, a probability vector and two position sets each of size $2d-5$), the shared concentration parameter $t$ couples these estimates: a large arithmetic contribution forces the refined geometric estimate to use the same $t$. This explains why separate worst-case bounds on the two sums lose useful information.
- *Index sharpness and value slack.* The greatest-element assertions settle the integer cutoff. For $d\ge5$ and every probability vector, the two cases in `selected_mean_bound`, with both selected sets of size $2d-5$, give the following unformalized quantitative bound $A_{2d-5}+G_{2d-5}\le B_d$, where $B_d=\max\{d-1/2,\ 3/2+\sqrt{d^2-3d+1/4}\}<d$. In the small-coordinate case, both sums are at most $d/2-1/4$. In the large-coordinate case, Cauchy–Schwarz gives the second term in $B_d$; its radicand is $(d-3/2)^2-2$, so that term is strictly below $d$. Thus integer sharpness does not require the value $d$ to be attained. The proposed exact optimum $(d+\sqrt{d^2-8})/2$ and a classification of maximizing vectors remain unverified here.
- *Effect on the source's criterion.* In Caro and Graswald's reduction (arXiv:2009.06666v3, `main.tex` lines 650–705 and 719–740), take a nonzero traceless Lindblad operator $\mathcal L$ and set $p_i=s_i(\mathcal L)^2/\|\mathcal L\|_F^2$. At $k=2d-5$ for $d\ge5$, the two tensor-product Ky Fan terms in their triangle estimate total $2\|\mathcal L\|_F^2(G_k(p)+A_k(p))\le2d\|\mathcal L\|_F^2$. The zero operator gives zero directly; their trace-centering step handles general Lindblad operators. Together with $\operatorname{Tr}(L+L^*)=-2d\|\mathcal L\|_F^2$ for the centered operator and the bound of a sum of negative eigenvalues by the Ky Fan norm, this supplies the generator inequality needed in their spectral-to-channel reduction. Applying that source reduction gives $0\le\det(T)\le\prod_{i=1}^{2d-5}s_i^\uparrow(T)$ for every infinitesimal Markovian divisible quantum channel $T$ on $d\times d$ matrices with $d\ge5$; this channel statement is not formalized by the module. The source's existing criterion remains valid. The matrix cutoff does not establish optimality of the channel criterion: failure of a split triangle upper estimate does not force failure of the unsplit generator inequality. The gap to the source's example-based ceiling $2d-2$, and its question of finding channels detected by the product criterion, are not settled by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check in #22748 does not establish exhaustive worldwide novelty or priority. Its readings of Caro's thesis, MathDB, formal-conjectures, the INSPIRE citation list and the citing works are not independently reproduced; the journal version is not independently read. The v3 TeX conjecture and its surrounding reduction are read directly. The bibliographic DOI is taken from the Library note's recorded Crossref reading, which is not independently reproduced.

The numerical searches attributed to the orchestrator are not rerun and do not establish their conclusions outside the tested families. The quantitative slack bound, the proposed exact optimum, the classification of maximizing vectors and the application to the source's determinant criterion are outside the formal result. The slack calculation and the spectral-to-channel application are arguments given above; the exact optimum and classification remain open here. The preregistration's stronger support-budget argument is not independently verified. Values in dimensions $1,2,4$, stronger channel criteria, examples detected by those criteria and sufficiency for Markovian divisibility are not settled by the module.
