---
slug: oconnor-ramgoolam-2025-tensor-high-temperature-leading-classes
bibkey: oconnorramgoolam2025gaugedtensor
doi: 10.48550/arXiv.2506.18813
url: https://arxiv.org/abs/2506.18813v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.result
---

# Identity and transposition classes have the two largest tensor high-temperature degrees

## Problem

D. O'Connor and S. Ramgoolam, *Gauged permutation invariant tensor quantum mechanics, least common multiples and the inclusion-exclusion principle*, arXiv:2506.18813v2 (2025), Section 7.2, state:

> Computations with Mathematica and the analysis of special families give strong evidence that the leading contributions in the high temperature limit $ x \rightarrow 1 $ come from $ p = [ 1^N ] $ followed by $ p = [ 2,1^{ N-2} ] $.

Section 9 asks:

> It would be very interesting to find the proof of the general $s$ conjecture for the leading two terms.

These quotations are from lines 1068 and 1322 of the v2 e-print member `Perm-Invt-Tensor-Counting-Functions-Journal.tex`, md5 `202b33a8e55dec1592ee90b7e5fbd8d9`.

For a partition $p$ of $N$, let $A(p)$ be its set of distinct part values and $m_a$ the multiplicity of $a$. The module's rational-valued `degree` is the first sum in the source's equation (7.21), Section 7.2, TeX lines 1079–1087:

$$D_s(p)=\sum_{t:\mathrm{Fin}\,s\to A(p)}
\frac{\prod_{j\in\mathrm{Fin}\,s}t_jm_{t_j}}
{\operatorname{lcm}\{t_j:j\in\mathrm{Fin}\,s\}}.$$

Tuple entries may repeat. The part values, multiplicities and natural-number least common multiple are cast to the rationals for this expression.

Write $I_N=[1^N]$ and $T_N=[2,1^{N-2}]$. Issue [#24869](https://github.com/the-omega-institute/trureturing/issues/24869) fixes the reading: for every natural $N\ge2$ and $s\ge1$,

$$D_s(I_N)=N^s,\qquad D_s(T_N)=\frac{N^s+(N-2)^s}{2}<D_s(I_N),$$

and every partition $p$ of $N$ different from both $I_N$ and $T_N$ satisfies $D_s(p)<D_s(T_N)$. This assertion is proved. The subtraction $N-2$ is natural subtraction; it agrees with integer subtraction in the stated range.

## Motivation

The source ranks conjugacy-class contributions to the partition function by their pole orders at $x\to1$. Identifying the two largest degrees supplies the discrete ordering used in Section 7.2's analysis of the breakdown of the high-temperature expansion. The source gives the two displayed classes' explicit contributions; the missing comparison is with every other class at general rank.

## Gap

Issue #24869 records the bounded literature check before any Lean:

- The v2 source retains both the conjecture and the request for a proof; the quoted passages are verified above.
- The source credits Appendix B of O'Connor and Ramgoolam, *Permutation invariant matrix quantum thermodynamics and negative specific heat capacities in large N systems* (2024), arXiv:2405.13150, with the $s=2$ proof.
- The issue reports inspection of four INSPIRE-listed citing works, arXiv:2602.04845v1, 2603.29610v2, 2606.09521v2 and 2610.10745v1, with no general-rank settlement found.
- The issue reports title and conjecture-phrase searches, two Zenodo queries and repository searches with no existing settlement found.

`not-found-in-searched-scope`.

## Route

Let $p:\mathrm{Nat.Partition}\,N$ and $f=m_1$. The lemma names below are the module's private helpers.

1. **Total weight.** For every natural $s,N$ and every partition $p$ of $N$, `total_weight` gives $\sum_t\prod_jt_jm_{t_j}=N^s$, by expanding $(\sum_{a\in A(p)}am_a)^s$.
2. **Half-weight bound.** For $s\ge1$ and any partition $p$ of $N$, `one_weight` gives total weight $f^s$ for the all-ones tuples, including zero when $1$ is absent. With those same hypotheses, `degree_le_from_one_count` proves $D_s(p)\le(N^s+f^s)/2$. All-ones tuples have denominator $1$; any other tuple contains a positive part at least $2$, which divides its positive least common multiple, so its denominator is at least $2$. All weights are nonnegative.
3. **The two exact values.** For $N\ge2$ and $s\ge1$, `identity_degree` and `transposition_degree` give the displayed formulas, and `transposition_lt_identity` gives their strict comparison. In `transposition_degree`, under these hypotheses every tuple that is not all ones contains $2$ and has least common multiple exactly $2$. At $N=2$ the all-ones group is empty and contributes $0^s=0$.
4. **Every other partition.** For $N\ge2$ and $p\ne I_N$, `one_count_le_two_sub` gives $f\le N-2$. For $N\ge2$ and every partition $p$ of $N$, `one_count_eq_two_sub_iff` gives $f=N-2$ if and only if $p=T_N$: the parts different from $1$ must sum to $2$, hence consist of a single $2$. Thus, with $N\ge2$, $s\ge1$, $p\ne I_N$ and $p\ne T_N$, `other_degree_lt` combines $f<N-2$ with the half-weight bound and strict monotonicity of a positive natural power to obtain $D_s(p)<D_s(T_N)$.

## Falsifier

The formalization would miss the conjecture if it changed the tuple indexing or the two partitions. It uses `Nat.Partition N`, sums over functions into `p.parts.toFinset` with multiplicities `p.parts.count`, and takes the least common multiple of the image of each tuple. Thus it uses distinct part values as indices while allowing repeated choices, exactly as the first sum of (7.21) does.

`onesPartition N` has precisely $N$ ones. For $N\ge2$, `transposition_parts` identifies `transpositionClass N` with one $2$ and $N-2$ ones. The constructor's total extension below $N=2$ is outside `claim`. The assertion compares degrees at fixed $N$; it does not assert an ordering of all coefficients of a high-temperature series or a uniform large-$N$ estimate.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.lean`.

- **Proof.** It proves `result : claim`, with `claim : Prop` the four-clause assertion above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.lean.json`.

Declaration statements:

- `result`: `sha256:6c5c27f4b5510de21e695d16963ab6dc8d189ad532dc755809140d1b27f00142`;
- `claim`: `sha256:155d40ab04e0bfa24b9e1a4bac36d208927f78cceeddd1cea7aed5c40f520f34`.

## Triage

Tier 1 conjecture of a 2025 preprint with an explicit request for proof, preregistered in issue #24869 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $N\ge2$ and $s\ge1$, the identity degree is $N^s$, the transposition degree is $(N^s+(N-2)^s)/2$, the latter is strictly below the former, and every partition of $N$ unequal to both has degree strictly below the transposition degree.

**Computed, not formalized.** None.

**Argued, not formalized.**

- *Sharpness of the auxiliary bound.* For $s\ge1$ and any partition $p$ of $N$, equality in the bound of `degree_le_from_one_count` is equivalent to all parts belonging to $\{1,2\}$. If all parts are $1$ or $2$, the denominators are exactly $1$ for all-ones tuples and $2$ otherwise, making every termwise bound an equality. If a part $a\ge3$ occurs, the constant tuple with value $a$ has positive weight and denominator $a>2$, making its half-weight estimate strict; no other term exceeds its estimate. Thus the bound is sharp for a larger family than the transposition class, while the count of ones singles out that class among nonidentity partitions when $N\ge2$ by `one_count_le_two_sub` and `one_count_eq_two_sub_iff`.
- *The rank condition.* At $s=0$ there is exactly one empty tuple; its empty product and empty least common multiple are both $1$, so the defining sum gives degree $1$ for every partition. This explains why the strict ranking requires positive rank. `result` includes rank $1$ but makes no assertion at rank $0$.
- *Effect on the paper and remaining questions.* The comparison supplies the conjectured degree ordering used by O'Connor and Ramgoolam (2025), arXiv:2506.18813v2, Section 7.2, in their large-$N$ derivation of $x_c\sim\log N/(sN^{s-1})$ (TeX lines 1148–1159); the source explicitly excludes a transition at $s=1$ (line 1167). The coefficients and number of classes vary with $N$, so fixed-$N$ degree ordering alone supplies no uniform estimate for the omitted class sum at an $N$-dependent $x$. Such estimates, the claimed transition scale and the ordering of later classes remain outside `result` and open here.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The four citing-paper readings reported in #24869, the earlier $s=2$ Appendix B at arXiv:2405.13150v3 and the reported applicability assessment of arXiv:2112.03967 have not been independently verified here. The issue's INSPIRE census, WebSearch and Zenodo results and preregistration repository-search results have not been independently reproduced.

The statements under "Argued, not formalized" are outside the formal assertion of `result`. The module does not formalize the partition functions, the analytic identification of the degree sum with their pole orders, the inclusion-exclusion expression for (7.21), class weights, uniform asymptotics, the critical Boltzmann factor, refined tensor models or any ordering beyond the two leading classes.
