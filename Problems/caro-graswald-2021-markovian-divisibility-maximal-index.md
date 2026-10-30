---
slug: caro-graswald-2021-markovian-divisibility-maximal-index
bibkey: carograswald2021markovian
doi: 10.1063/5.0031760
url: https://arxiv.org/abs/2009.06666v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex.result
---

# The Caro–Graswald maximal index is $2d-5$ for $d\ge5$, and $2$ for $d=3$

## Problem

M. C. Caro and B. R. Graswald, *Necessary criteria for Markovian divisibility of linear maps*, Journal of Mathematical Physics 62, 042203 (2021), arXiv:2009.06666v3, Conjecture 4.19 (`CnjAMGMMatrices`), `main.tex`, lines 729–737. The following quotation is checked against the v3 TeX; its macro `\IR` is expanded as defined in `commands.tex`:

> Let $p\in\mathbb{R}^d_{\geq 0}$ with $\sum\limits_{i=1}^d p_i = 1$. Define the matrices $a,g\in\mathbb{R}^{d\times d}$ via
>
> $a_{ij} = \frac{p_i + p_j}{2},\quad g_{ij}=\sqrt{p_i p_j}.$
>
> Denote by $a_k^\downarrow$ and $g_k^\downarrow$ the $k^{th}$ largest entry of $a$ and $g$, respectively. Define
>
> $A = \sum\limits_{k=1}^{h(d)} a_k^\downarrow,\quad G = \sum\limits_{k=1}^{h(d)} g_k^\downarrow.$
>
> We conjecture that the maximal integer $h(d)$ such that $A+G\leq d$ holds for any probability vector $p$ is given by $h(d) = 2d-5$.

For a natural index $m$, write $A_m(p)$ and $G_m(p)$ for the sums of the largest $\min(m,d^2)$ entries of the two matrices, sorted independently, counting both ordered positions and retaining equal values at distinct positions. Let $S_d=\{m\in\mathbb{N}:\forall p\in\mathbb{R}^d_{\ge0},\ \sum_i p_i=1\Rightarrow A_m(p)+G_m(p)\le d\}$. The module's `admissibleIndices d` is $S_d$.

Issue [#22748](https://github.com/the-omega-institute/trureturing/issues/22748) fixes the settlement as two greatest-element assertions: $\max S_d=2d-5$ for every $d\ge5$, and $\max S_3=2$. Thus the conjectured formula is proved in the specified range, while the three-dimensional value differs from the printed expression $2\cdot3-5=1$. The source states no dimension restriction; the settlement does not assert its formula in every dimension.

## Motivation

Caro and Graswald (2021, arXiv:2009.06666v3), Corollary `CrlQuDetVSProductSmallestSV` (`main.tex`, lines 703–705), give a necessary criterion for infinitesimal Markovian divisibility: for $T\in\overline{\mathcal I}_d$, $0\le\det T\le\prod_{i=1}^{\lfloor 2d-2\sqrt{2d}+1\rfloor}s_i^\uparrow(T)$. The remark at lines 719–740 reduces a possible increase in the number of factors to the probability-vector conjecture. Settling the integer cutoff determines how far that separate arithmetic/geometric estimate can take the source's method. The definitions and source locators are also in [the literature note](../Library/Eigenstructure/carograswald2021markovian.md).

## Gap

Issue #22748 records a bounded prior-settlement check by search-fj and the orchestrator: MathDB record 347947, the google-deepmind formal-conjectures repository, three citing records listed by INSPIRE, and repository searches. It reports no settlement within that scope. The cited-record readings, the journal conjecture reproduced in Caro's thesis, and the version-history reading are reported evidence, not independently reproduced here; the v3 conjecture itself is checked directly.

`not-found-in-searched-scope`.

## Route

All dimensions and indices below are natural numbers. A probability vector means nonnegative real coordinates with sum one, using `D5.S3.TotalVariation.CycleSingleCutMinimax.Probability` directly. The named helper lemmas are private declarations of the canonical module.

1. **Finite maxima.** For every dimension $d$, index $m$ and real function on the ordered positions, `top_sum_attained` supplies a maximizing set of exactly $\min(m,d^2)$ positions. The candidate family is nonempty, including at $m=0$. For every such function whose entries are all nonnegative, `top_sum_mono` makes its largest-entry sum nondecreasing in $m$.

2. **Arithmetic coefficients.** For any real vector $p$ and position set $s$, `arithmetic_coefficients` expresses its arithmetic sum as $\sum_i c_i p_i$, with $c_i\le(|s|+1)/2$ and $c_i+c_j\le|s|/2+2$ for distinct $i,j$. For a probability vector $p$, real coefficients $c$, and real $u,v,T$ satisfying $c_i\le u$ for every $i$, $c_i+c_j\le v$ for every distinct pair, $T\ge1/2$, $p_i\le T$ for every $i$, and $v\le2u$, `probability_weighted_bound` gives $\sum_i c_i p_i\le(2T-1)u+(1-T)v$.

3. **Geometric squared mass.** For a probability vector $p$, `geometric_square_sum` gives $\sum_{i,j}g_{ij}^2=1$. For that same hypothesis and any position set $s$, `geometric_coarse_bound` gives $\sum_s g_{ij}\le\sqrt{|s|}$. For a probability vector $p$, an index $i$ satisfying $p_j\le p_i$ for every $j$, and a nonempty position set $s$, `geometric_refined_bound` gives $\sum_s g_{ij}\le p_i+\sqrt{|s|-1}\sqrt{1-p_i^2}$, with natural subtraction in $|s|-1$.

4. **Admissibility.** For $d\ge5$, a probability vector $p$, and independently chosen position sets $s,t$ both of cardinality $2d-5$, `selected_mean_bound` bounds the arithmetic sum over $s$ plus the geometric sum over $t$ by $d$. With $T=\max_i p_i$, the coefficient parameters are $u=d-2$ and $v=d-1/2$. When $T\le1/2$, the respective bounds are $d/2-1/4$ and $\sqrt{2d-5}\le d/2-1/4$. When $T>1/2$, they are $3/2+(d-7/2)T$ and $T+\sqrt{2d-6}\sqrt{1-T^2}$; the combined expression is at most $d$ by Cauchy–Schwarz and $d\ge5$. For $d\ge5$ and every probability vector $p$, `main_bound` applies this estimate to two independently attained maxima, yielding $A_{2d-5}(p)+G_{2d-5}(p)\le d$.

5. **Failure at the next index.** For every $d\ge5$, `failure_next` constructs a probability vector with $A_{2d-4}(p)+G_{2d-4}(p)>d$. Its vector is $p=(r^2,1,\ldots,1,0,0)/N$, where $r=d-2$, there are $d-3$ entries equal to $1$ in the numerator, and $N=r^2+d-3$. The proof uses selected sums totaling $d+(d-4)^2/(2N)>d$ as lower bounds on the two largest-entry sums; it does not require identifying either maximizing set.

6. **Dimension three.** For any dimension, probability vector $p$, and position set $s$ of cardinality two, `arithmetic_two_bound` gives $\sum_s a_{ij}\le3/2$. For a probability vector and any ordered position, `geom_le_arith` gives $g_{ij}\le a_{ij}$ by Mathlib's `NNReal.sqrt_mul_le_half_add`. For every probability vector in dimension three, `three_bound` consequently gives $A_2+G_2\le3$. In dimension three, `three_failure` constructs a probability vector violating the inequality at index three: $p=(4/5,1/5,0)$, with three selected positions contributing arithmetic sum $9/5$ and geometric sum $8/5$.

7. **Greatest elements.** For natural $d,m$, assuming $m\in S_d$ and the existence of a probability vector with $A_{m+1}+G_{m+1}>d$, `greatest_of_bound_failure` concludes that $m$ is the greatest element of $S_d$. Nonnegativity of both mean matrices makes the violation persist at every larger index. Applying this lemma with the preceding bounds gives the two conjuncts of `result`.

## Falsifier

The proof would not settle the stated problem if the formal quantities restricted the simplex, omitted diagonal entries, collapsed equal values, or required the two maxima to use the same positions. The definitions retain zero coordinates, all $d^2$ ordered positions, and independent arithmetic and geometric selections. `arith` reuses `meanOne`, exactly $(p_i+p_j)/2$; `geom` reuses `meanZero`, exactly $\sqrt{p_i p_j}$.

`topSum` uses `Finset.sup'` over a nonempty finite family, with nonemptiness supplied in its definition. Its attainment lemma identifies an actual maximizing position set. Each greatest-element conclusion includes both admissibility and the upper-bound property for all admissible indices. The scope is exactly $d\ge5$ and $d=3$; dimensions zero, one, two and four are outside `result`.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex.lean`.

- **Proof.** It proves `result : (∀ d : ℕ, 5 ≤ d → IsGreatest (admissibleIndices d) (2 * d - 5)) ∧ IsGreatest (admissibleIndices 3) 2`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex.lean.json`.

Declaration statements:

- `result`: `sha256:ee2ade07fab8ec70a62aad80b5ae9386dbbc4160b0123bf7336ff3b761ac0bb8`.

## Triage

Tier 1 conjecture of a 2021 Journal of Mathematical Physics paper, preregistered in issue #22748 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural dimension $d\ge5$, $2d-5$ is the greatest natural index $m$ such that every nonnegative real vector $p$ of dimension $d$ with sum one satisfies $A_m(p)+G_m(p)\le d$; in dimension three, $2$ is the greatest such index.

**Computed, not formalized** (orchestrator, recorded in #22748): for the tested probability vectors in dimensions five through eight, a value of $A_{2d-5}+G_{2d-5}$ above $d$ was not observed.

**Argued, not formalized.**

- *Decisive mechanism and sharpness.* For $d\ge5$, a probability vector $p$, and independent position sets $s,t$ each of size $2d-5$, `selected_mean_bound` combines individual and distinct-pair coefficient constraints with normalized geometric squared mass to bound their total by $d$. The integer-cutoff mechanism is `greatest_of_bound_failure`: for natural $d,m$, membership $m\in S_d$ together with a probability vector violating the inequality at $m+1$ gives the greatest-element assertion at $m$. That statement imposes no equality condition on the real-valued bound at the admissible index. The sharper candidate maximum $(d+\sqrt{d^2-8})/2$ for $d\ge5$ is recorded in #22748; its universal upper bound and its asserted extremizers are not verified here and remain open in this dossier.
- *Homogeneous extension.* For nonnegative $x$ of dimension $d\ge5$, put $M=\sum_i x_i$. If $M=0$, every coordinate and both mean matrices vanish. If $M>0$, $p=x/M$ is a probability vector, and both mean matrices of $x$ are $M$ times those of $p$, since $\sqrt{M^2p_ip_j}=M\sqrt{p_ip_j}$. Every selected sum and hence its finite maximum scales by $M$. Thus the probability bound gives $A_{2d-5}(x)+G_{2d-5}(x)\le dM$. The same argument gives $A_2(x)+G_2(x)\le3M$ in dimension three. These scaling statements are mathematical consequences, not additional compiled declarations of this module.
- *Effect on the source's conditional consequence.* Caro and Graswald (2021, arXiv:2009.06666v3), `main.tex` line 740, identify the choice $f(d)=2d-5$ in their determinant criterion as a consequence of the conjecture. For $d\ge5$, the settled inequality supplies precisely the probability-vector input to their reduction at lines 719–727: for a nonzero Lindbladian $\mathcal L$, let $M=\|\mathcal L\|_F^2$ and $p_i=s_i(\mathcal L)^2/M$; the two Ky Fan terms in their triangle bound total $2M(G_{2d-5}+A_{2d-5})\le2dM$. The zero Lindbladian gives zero directly. Accepting the source's generator-to-channel passage, this gives $0\le\det T\le\prod_{i=1}^{2d-5}s_i^\uparrow(T)$ for its infinitesimally Markovian divisible channels $T\in\overline{\mathcal I}_d$, $d\ge5$. That passage and the channel statement are not formalized by `result`.
- *Neighbouring questions.* For $d\ge5$, the source's example at `main.tex` lines 707–716 obstructs a universal factor count strictly between $2d-2$ and $d^2$; the count $2d-5$ leaves three factors to that obstruction. A violation of the separate arithmetic/geometric estimate at $2d-4$ does not construct a channel violating a determinant criterion there, because the source's triangle bound is only an upper estimate. Optimal channel factor counts, detecting nondivisible channels with the criterion, and the sufficient-criterion question in the source's conclusion (lines 851–853) remain open here. The boundary $h(4)=4$ is a numerical candidate in #22748, not a conclusion of `result`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The MathDB, formal-conjectures and INSPIRE searches and the readings of the three listed citing records are search-seat reports in #22748 and were not independently reproduced. The journal conjecture as reproduced on page 132 of Caro's *Quantum Learning Theory* (2022), and the arXiv version-history reading, were not independently reproduced; the source text checked here is the v3 TeX. The DOI and bibliographic identity are checked against Crossref.

The orchestrator's numerical search in #22748 was not rerun. The statements under “Computed, not formalized” and “Argued, not formalized” are not compiled assertions of this module. In particular, the sharper real-valued maximum and extremizers, the homogeneous extension, the singular-value/Ky Fan and generator-to-channel bridges, and the determinant consequence are outside its formal statement. The exact maximum, the four-dimensional boundary and the neighbouring channel questions remain unresolved by this settlement.
