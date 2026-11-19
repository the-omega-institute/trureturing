---
slug: lee-hhan-cho-kwon-2025-chromatic-index-tail
bibkey: leehhanchokwon2025chromatictail
doi: 10.48550/arXiv.2507.17871
url: https://arxiv.org/abs/2507.17871v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.result
---

# The chromatic-index failure-probability conjecture is false

## Problem

W. Lee, M. Hhan, G. Y. Cho and H. Kwon, *Shallow quantum circuit for generating extremely low-entangled approximate state designs*, arXiv:2507.17871v3, Supplemental Material §4, p. 18, conjecture after Eq. (87):

> We conjecture that in this regime, χ′(H) is upper bounded by O(t log t) with a failure probability smaller than ϵ.

The regime has $\log(1/\epsilon)$ scaling as $t^{1+c}$ for $c>0$, with $\beta>1+c$. The universal eventual probability bound is refuted by `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.result`. The preregistration is [#20030](https://github.com/the-omega-institute/trureturing/issues/20030).

### Statement echo

| Source clause | Lean counterpart | Fidelity and scope |
| --- | --- | --- |
| An $m$-uniform hypergraph on $k$ vertices, with $\alpha$ independent sampled edges | Tuples indexed by `Fin alpha`, with values in `Finset.univ.powersetCard m` on `Fin k` | Ordered independent uniform samples; equal sets keep distinct occurrence indices. |
| The chromatic index is the minimum depth of applying all gates | `chromaticIndex` | Least natural colour count separating every pair of distinct intersecting occurrences. |
| $k=3\log(t^2/\epsilon)$, $m=\log t$, $\alpha=\beta t\log(1/\epsilon)$ | `kParam`, the inline natural ceiling of the base-two logarithm, `alphaParam` | Base-two logarithms and natural ceilings are the binding conventions; the edge space and edge-size expression are inline Mathlib constructions. |
| $\log(1/\epsilon)$ scales as $t^{1+c}$ | `eps c t` | The particular member $\epsilon=2^{-t^{1+c}}$ suffices to refute the universal assertion. |
| $c>0$, $\beta>1+c$ | The two hypotheses inside `claim` | The refutation uses $c=1$, $\beta=3$, satisfying both hypotheses. |
| $O(t\log t)$ with failure smaller than $\epsilon$ | `claim` | For every admissible $c,\beta$ there exist real $C$ and natural $T$ such that every natural $t\ge T$ has strict tail probability below `eps c t`. |
| Negative answer | `result` | Negates the whole closed proposition `claim`. |

The real constant $C$ is unrestricted; a positive eventual big-O constant is included. Natural $t$ restricts the universal assertion to an integral subfamily. The constructed values exceed every natural threshold, so the inclusion of small or degenerate parameters does not cause the contradiction. The parameterized probability is a finite counting ratio; no asymptotic approximation replaces its strict inequality.

## Motivation

At very small failure levels, a rare prefix of intersecting edges can have probability larger than the requested failure budget. A typical-probability bound does not supply the much stronger failure estimate in the conjecture.

## Gap

The missing universal tail bound is false under independent sampling with repeated occurrences. The source's weaker probability $1-O(1/\log t)$ in Eq. (87) is outside the negated assertion. The exact binomial-strength prefix estimate and the pairwise-distinct-edge strengthening are not formalized here.

## Route

A prefix of $r$ copies of a fixed nonempty edge requires at least $r$ colours. For an edge-space size $N$, all $N^{\alpha-r}$ suffixes belong to the tail event whenever $x<r\le\alpha$. Thus its probability is at least $N^{-r}\ge k^{-mr}$, using the upper bound $N=\binom{k}{m}\le k^m$.

For any proposed $C,T$, put $L=\max(1,\lceil C\rceil_{\mathbb N})$, $s=\max(64,\max(T,32(L+1)))$, $q=2^s$, $t=2^q$, and $r=Ltq+1$. The parameters at $c=1,\beta=3$ satisfy $m=q$, $k=3t^2+6q$, $\alpha=3t^3$, $r\le\alpha$, and $Ct\log_2t<r$. The exponent comparison $(2q+3)qr<t^2$, together with $k\le2^{2q+3}$, gives

$$\epsilon(1,t)=2^{-t^2}<2^{-(2q+3)qr}\le k^{-qr}\le\Pr[\chi'(H)>Ct\log_2t].$$

These are the steps of the kernel-checked `result`, with the private counting lemmas `filter_card_ge_fixed_prefix`, `tailProb_ge_fixed_prefix_ratio` and `fixed_prefix_prob_lower`. The module has generality `I`, `utility: none`, and admission basis `open-problem-resolution (#20030; Refuted)`.

## Falsifier

The conjecture requires an eventual strict upper bound for every admissible $c,\beta$. Its specialization at $c=1,\beta=3$ contradicts the displayed lower bound for a parameter beyond each proposed threshold. Repeated edge occurrences are essential to this particular counting construction. A theorem for pairwise distinct edges would need a separate argument.

## Evidence

The settling GID is `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.result`. The Scribe renders its complete negated quantified proposition and acknowledges the source note `Library/FiniteGeometry/leehhanchokwon2025chromatictail.md`. All mathematical imports are pinned Mathlib; there are no D5 prerequisites, atoms, or cover operations.

The escape audit for the only public theorem, `D5.S3.Combinatorics.Hypergraphs.LeeHhanChoKwonChromaticIndexTail.result`, is unfinished: [#31150](https://github.com/the-omega-institute/trureturing/issues/31150). The symbolic refutation has `utility: none`, so this result has no utility-refutation exemption. No Reg mirror or validated registration is claimed. The missing evidence is a faithful enrolled-template application, source reconstruction, and its realization and sensitivity proofs.

### Finite experiment

The program is in [trureturing-experiments at 101c5f2b8339927f6af87696ca46f52e0d544088](https://github.com/the-omega-institute/trureturing-experiments/tree/101c5f2b8339927f6af87696ca46f52e0d544088/docs/reports/lee-hhan-cho-kwon-2025-chromatic-index-tail), path `docs/reports/lee-hhan-cho-kwon-2025-chromatic-index-tail/check.py`. Its immutable Git object was checked with `git cat-file -e`; the extracted program has SHA-256 `5800bc5cdf3838f94680993ccb2aacbb776d11ef7c3e8e1a8b47b0318ef9e6f1`. Command: `python3 /tmp/op-lhck2507/check.py`, exit 0, `ALL_CHECKS True`.

The exact enumerations of $\chi'$ are: $(k,m,\alpha)=(4,2,3)$ has counts $90,126$ at $2,3$; $(5,2,3)$ has $630,370$ at $2,3$; $(5,3,3)$ has $1000$ at $3$; $(6,2,3)$ has $90,2430,855$ at $1,2,3$. At each of these four triples, the experiment checks $\Pr[\chi'\ge r]\ge(m/k)^r$ for $r=1,2,3$ and Eq. (77), $\chi'\le m(\Delta-1)+1$, on every sample. It also checks $k\le2^{2q+3}$, $(2q+3)r<t^2$, and $r>Lt\log_2t$ for $L=1,2,3,4$ at $q=32(L+1)=64,96,128,160$. These finite checks do not establish a uniform theorem or the distinct-edge variant.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Scope and boundary |
| --- | --- | --- |
| Settlement | Proved, kernel-checked `result` | Refuted for the exact independent uniform occurrence model of #20030. |
| Failure mechanism | Proved, kernel-checked `filter_card_ge_fixed_prefix` and `fixed_prefix_prob_lower`, used by `result` | A repeated fixed nonempty edge forces a pairwise-intersecting prefix; the lower bound $k^{-mr}$ exceeds $\epsilon$ along the constructed unbounded dyadic family. |
| Surviving fixed-prefix scope | Proved, kernel-checked `fixed_prefix_prob_lower` | The fixed nonempty edge prefix gives the bound $k^{-mr}$. |
| Uniform binomial estimate and repaired conjectures | Open | The exact bound $(m/k)^r$ and repairs with additional hypotheses are not Lean theorems in this delivery. |
| Downstream implications | Proved in prose | Any implication using the universal conjecture must replace that false premise with a restriction or a weaker tail assertion. No repair is formalized. |
| Vertex-congestion estimate and necessary colour-cap scale from the preregistration | Open as uniform formal statements | The stronger estimate $(m/k)^r=\exp(-r\log(k/m))$ and the resulting necessary scale involving $D\log(k/m)$ require separate formalization; the finite experiment checks only the four triples above. |
| Pairwise distinct hyperedges | Open | The proof's repeated-edge event does not establish this strengthening. |
| Source Eq. (87) | Open here; source literature statement | Its failure probability $O(1/\log t)$ is not refuted by the much smaller failure-level comparison. No Lean proof of Eq. (87) is delivered. |
| Exact finite distributions and Lemma 1 checks | Computed | The experiment entry checks exactly the four triples, $r=1,2,3$, with the distributions stated there. Uniform extension remains open in Lean. |
| Source Eq. (77) checks | Computed | The experiment verifies the greedy bound on every sample of those four enumerations; a general Lean theorem is not delivered. |
| Finite parameter-family inequalities | Computed | The experiment checks $L=1,2,3,4$ at $q=32(L+1)$; these are finite instances of the stronger source argument, distinct from the doubly dyadic family used by `result`. |
| Literature status | Literature reading; completeness ASSUMED-UNVERIFIED | The preregistration records that v3 retains the conjecture, with greedy colouring, Chernoff bounds and the Kurauskas–Rybarczyk theorem as context. A complete correction/priority screen and the final journal supplement are unverified. |

## ASSUMED-UNVERIFIED

Literature completeness, worldwide priority and the final journal supplement's status are unverified. The checked source is arXiv:2507.17871v3. The exact binomial-strength theorem, the distinct-edge strengthening, the necessary colour-cap scale and repaired conjectures remain open in Lean; the completed settlement is the negation proved by `result` under the stated sampling and rounding conventions. The escape audit remains unfinished under #31150.
