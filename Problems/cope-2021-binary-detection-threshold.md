---
slug: cope-2021-binary-detection-threshold
bibkey: cope2021binarydetection
doi: 10.1088/1367-2630/ac10a5
url: https://arxiv.org/abs/2005.03344v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.result
---

# Refutation of the symmetric binary-outcome detection-threshold conjecture

## Problem

T. Cope, *The Binary-Outcome Detection Loophole*, New Journal of Physics 23 (2021) 073032, DOI 10.1088/1367-2630/ac10a5, arXiv:2005.03344v3, Section 4.3, printed p. 6, states:

> In order to prove that our conjecture of $\eta^*=4/(m+4)$ for $m_{\mathrm{A}}=m_{\mathrm{B}}=m$ is correct, one would need to provide a extremal $\mathcal{NS}$ distribution $p^{\mathrm{NS}}$, and corresponding Bell inequality $s_{a'b'}^{xy}$, such that $\sum_{a',b',x,y}s_{a'b'}^{xy}p^{\mathrm{NS}}_{\eta}(a'b'|xy) \not \leq k,\; \forall \eta > \eta^*$.

The named conjecture asserts $\eta^*(m)=4/(m+4)$ for every $m\ge2$. Its definitions and the refutation criterion are fixed in [#15572](https://github.com/the-omega-institute/trureturing/issues/15572). The source definitions and locator are in [the Library note](../Library/QuantumBounds/cope2021binarydetection.md).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Two parties, $m$ inputs each, binary outputs | Two `Fin m` inputs and two `Bool` outputs in `IsNSBox` | Equal input counts; failure is an additional output only after loss. |
| Conditional probabilities and no signalling (Section 2) | Four conjuncts of `IsNSBox`: nonnegativity, normalization, and both input-independent marginals | Every input and output is quantified. |
| Independent equal-efficiency loss, equation (3) | All four branches of `lossy` | `some` denotes a detected bit and `none` denotes $F$; the two single-failure terms use the original marginals. |
| Convex hull of deterministic local responses | `IsLocal` | A finite weight for every pair of response functions, nonnegative weights, sum one, and pointwise reconstruction. |
| No-signalling threshold, minimum of extremal-box thresholds | `etaStar m`, the supremum of $\eta\in[0,1]$ making every no-signalling box local after loss | The all-box formulation below is the convention of #15572 and expresses the same threshold. |
| Symmetric conjecture $\eta^*=4/(m+4)$ | `claim` | Quantifies every natural $m\ge2$; division is in $\mathbb R$. |
| Proposed extremal-box Bell-inequality certificate above the conjectured threshold | No additional Lean hypothesis | This is the source's proposed way to establish tightness, not an assumption of its equality conjecture. The local construction above that conjectured value disproves the equality instead. |
| A counterexample to the universal equality | `result : ¬ claim` | The private `lower_bound` proves $6/25\le\eta^*(13)$, whereas the equality gives $4/17$. |

The threshold formulation follows from convexity. Every no-signalling box is a convex combination of extremal boxes. At a fixed efficiency, loss preserves normalized convex combinations and the local polytope is convex. Thus every box is local after loss if and only if every extremal box is. Further independent erasure preserves locality, so the admissible efficiencies of each extremal box form a downward interval. There are finitely many extremal boxes in this finite polytope; the supremum of efficiencies shared by all of them is the minimum of their thresholds. This is the mathematical interpretation of `etaStar`, not an additional Lean theorem in this module.

The efficiency interval $[0,1]$ is physical, and $m\ge2$ restricts the conjecture to its nontrivial input domain. Neither restricts the refuting instance $m=13$. Nonnegativity and normalization express a conditional probability distribution and are not extra assumptions about the conjecture.

## Motivation

The source's bound $2(m_A+m_B-8)/(m_Am_B-16)$ specializes to $4/(m+4)$ in the symmetric regime where the expression is defined. A three-input leader model improves that lower bound at $m\ge13$, despite having a smaller raw joint-success probability than a two-input leader. The quantity relevant to equal independent loss is the ratio of joint to single conclusive probability.

## Gap

The source optimizes the raw factor $n/(m2^{n-1})$. The loss model requires both joint and single conclusive probabilities to fit the same efficiency. Optimizing the raw factor alone does not maximize their ratio. At $m=13$, the three-input ratio is $6/25>4/17$.

## Route

The module first expresses the leader construction as a finite mixture of deterministic local strategies. Its private `qModel_eq_lossy` establishes the counting identity for every parity matrix $G$ at $m=13$; private `parityBox_local` uses the nonnegative normalized weights. A layer decomposition and a product distribution reconstruct every binary no-signalling box as a mixture of locally mapped parity boxes. Local maps and normalized mixtures commute with loss and preserve locality. Private `universal_local` and `lower_bound` give the threshold bound, and public `result` contradicts `claim`.

Finite output maps use `CycleSingleCutMinimax.push`; both party marginals use `ChainRule.marginal`. Paired response indicators use `FiberwiseEqualDistanceLift.labelKernel`, and the parity-bit product law uses `GreenClassWindowEntropy.windowLaw` with complemented `ScoreBridge.bernoulliMass` bits. These declarations and pinned Mathlib supply the finite-table operations. The repository's `RelaxedHardyNoSignallingOptimum.IsNSBox` concerns binary inputs and $d$ outputs for $N$ parties, rather than the present $m$ inputs and binary outputs for two parties; it is not on this module's dependency path.

## Falsifier

At $m=13$, the conjecture gives $\eta^*(13)=4/17$. The module gives $\eta^*(13)\ge6/25$, and

$$
\frac6{25}-\frac4{17}=\frac2{425}>0.
$$

The counterexample changes neither the no-signalling conditions nor the independent equal-efficiency loss convention.

## Evidence

`D5/S3/Quantum/Entanglement/BinaryDetectionThresholdRefutation.lean` has five public definitions (`IsNSBox`, `lossy`, `IsLocal`, `etaStar`, `claim`) and one public theorem, `result`. Every supporting declaration is private. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). There are no other new public theorems in this delivery. [#15774](https://github.com/the-omega-institute/trureturing/issues/15774) is the unfinished-audit issue for any additional public theorem requiring registration; this delivery makes no claim of registration completion for such a theorem. The delivered-head DTR reading is reported in the PR's verification data.

## Triage

### What the settlement shows

1. **Kernel-checked, $m=13$: the conjecture is false.** Public `result` proves the negation of the source equality. Its private `qModel_eq_lossy`, `parityBox_local`, `universal_local`, and `lower_bound` establish the exact local reconstruction at $6/25$ and its extension to every no-signalling box. The leader keeps three inputs. Private `rawA_count` counts the response branches symbolically for every $G$; two of the eight leader bit patterns make the follower conclusive. The calibration below explains why the efficiency is $c/d$, rather than raw joint success. The ratio explanation is a derivation from the displayed probabilities, not a separately named Lean theorem.

2. **Proved in prose, the family:** $\eta^*(m)\ge6/(m+12)>4/(m+4)$ for every $m\ge13$, with equality of the two lower bounds at $m=12$. The general counting and extension argument is below. Only its $m=13$ instance is kernel-checked in this module; the unbounded family is not an experimental conclusion.

3. **Computed, finite readings:** the pinned experiment entry below verifies the complete parity-box identity for six matrices at $m=13$, and two random matrices each at $m=14,16,20$. It verifies the strict gap for $13\le m\le200$ and equality at $m=12$. It does not test the universal no-signalling extension or determine the exact threshold.

4. **Open:** the exact value of $\eta^*(m)$ and whether larger leader sets improve $6/(m+12)$ further. The value of this constructed lower bound at $m=12$ is $1/4$; this is not a proof that the exact threshold is $1/4$ there. The source's established lower bound survives. Its conjectured tightness and any conclusion requiring that tightness fail for $m\ge13$; no other source theorem is contradicted by this refutation.

### General counting identity and calibration (proved in prose)

For $m\ge3$, write $p_G(ab\mid xy)=\tfrac12[a\mathbin\oplus b=G(x,y)]$. Choose the leader orientation uniformly, a uniform three-element subset of its inputs, and three uniform leader bits. The leader detects a fixed input with probability $3/m$. The follower detects any fixed input with probability $2/8=1/4$. Therefore the active model has joint conclusive probability and equal single conclusive probability

$$
c=\frac3{4m},\qquad d=\frac12\left(\frac3m+\frac14\right)=\frac{m+12}{8m}.
$$

Each successful parity has two equally probable output pairs, so the active model's detected-pair entries are $c\,p_G$. Each single-failure entry is $(d-c)/2$ and its double-failure entry is $1-2d+c$. These expressions hold for every Boolean matrix $G$ without enumerating matrices. In the ordered-triple representation, the total number of distinct triples is $m(m-1)(m-2)$, a fixed input belongs to $3(m-1)(m-2)$ triples, and misses $(m-1)(m-2)(m-3)$ triples.

Set

$$
\eta=\frac cd=\frac6{m+12},\qquad
t=\frac{\eta}{d}=\frac{48m}{(m+12)^2},\qquad
\beta=1-t=\frac{(m-12)^2}{(m+12)^2}.
$$

The active model has weight $t$ and the all-failure strategy has weight $\beta$. These weights are nonnegative and sum to one. Since $tc=\eta^2$ and $td=\eta$, their mixture satisfies the four loss branches:

$$
q(a,b\mid x,y)=\eta^2p_G(a,b\mid x,y),\quad
q(a,F\mid x,y)=q(F,b\mid x,y)=\frac{\eta(1-\eta)}2,\quad
q(F,F\mid x,y)=(1-\eta)^2.
$$

Here the equality between the two single-failure entries uses the uniform parity-box marginals. At $m=13$, this gives $t=624/625$, $\beta=1/625$, joint entries $18/625$ on each prescribed parity pair, single-failure entries $57/625$, and double-failure entry $361/625$.

For completeness the universal extension has a construction valid for every finite $m$. At each input choose a minority output with probability $r_x\le1/2$ for Alice and $s_y\le1/2$ for Bob. A common uniform variable $U\in[0,1]$ activates their inputs when $U\le2r_x$ and $U\le2s_y$. Joint activation has probability $2\min(r_x,s_y)$. Put $h_{xy}=p(\text{minority}_x,\text{minority}_y\mid x,y)$ and select parity $G(x,y)=0$ with probability $h_{xy}/\min(r_x,s_y)$, independently for each pair. When the denominator is zero, choose probability zero; nonnegativity and the marginals force $h_{xy}=0$. The ratio belongs to $[0,1]$. Active local output maps XOR the uniform parity output with the minority bit; inactive maps overwrite it with the majority bit. The resulting minority joint entry is $2\min(r_x,s_y)\cdot\tfrac12\cdot h_{xy}/\min(r_x,s_y)=h_{xy}$, and the marginals are $r_x,s_y$. Normalization determines the other three entries. Integrating $U$ gives a finite mixture of activation patterns, and the product law on parity matrices gives a finite mixture of mapped parity boxes. Thus every no-signalling box has this representation. Output maps extended by $F\mapsto F$ commute with independent loss and preserve locality; convex mixtures do likewise. This proves the stated general lower bound.

Finally,

$$
\frac6{m+12}-\frac4{m+4}
=\frac{2(m-12)}{(m+12)(m+4)}.
$$

The denominator is positive for natural $m$; the difference is positive for $m\ge13$ and zero at $m=12$.

### Experiment entry

[Exact rational check](https://github.com/the-omega-institute/trureturing-experiments/tree/0bb6887ea3e9d0004b179bf95c63754c6612c1a7/docs/reports/cope-2021-binary-detection-threshold), file `check.py`. Command: `python3 check.py`; exit code 0; script SHA-256 `793b133df525d68310b6e258860582d2732702c71f43cdf1cd9b5a822af12513`; final reading `bad= 0`. The tested scope is exactly the finite scope in item 3. At $m=13$, it enumerates $2\binom{13}{3}\cdot8=4576$ active atoms and the all-failure atom for each of the six matrices. It supplies no test of the vertex description and no upper bound on $\eta^*(m)$.

## ASSUMED-UNVERIFIED

The preregistration records the source and literature screen, including the source versions, citing works, later Cope papers, and earlier detection-loophole models. Those publication-status readings are attributed to their producers in #15572. This delivery does not assert an exhaustive search of all literature. The threshold interpretation and general-$m$ argument above are mathematical prose, not additional kernel-checked statements. The exact threshold and improvements using larger leader sets remain open.
