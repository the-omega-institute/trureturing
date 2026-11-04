---
slug: bhoria-eyyunni-santra-2026-overpartition-threshold-identity
bibkey: bhoria2026missing
doi: 10.48550/arXiv.2604.12557
url: https://arxiv.org/abs/2604.12557v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/OverpartitionThreshold.result
---

# The overpartition threshold identity

## Problem

Bhoria, Eyyunni and Santra, *On the number of missing integers in partitions*, arXiv:2604.12557v1, Section 4, Question 3, asks:

> Is there an overpartition analogue of Theorem 2.9, namely, a concise identity for the number of integers less than or equal to the largest part that appear less than k times in all overpartitions of n.

Let $\mathcal O_n$ contain every partition of $n$ together with an arbitrary subset of its distinct positive part sizes. A chosen size has its first occurrence overlined. Write $m_r(o)$ for its total multiplicity, $S(o)$ for the chosen subset, and $L(o)$ for its largest part, with $L(o)=0$ for the empty partition. Define

$$
U_k(n)=\sum_{o\in\mathcal O_n}\#\{r:1\le r\le L(o),\ m_r(o)<k\},
\qquad
T(n)=\sum_{o\in\mathcal O_n}\#\operatorname{parts}(o),
$$

$$
N_j(n)=\sum_{o\in\mathcal O_n}\bigl(m_j(o)-\mathbf1_{j\in S(o)}\bigr).
$$

Thus $U_k(n)$ includes absent sizes, $T(n)$ includes every occurrence, and $N_j(n)$ counts actual nonoverlined occurrences. The answer is the finite identity

$$
\boxed{U_k(n)=T(n)-2\sum_{j=k}^{n}(-1)^{j-k}N_j(n)}
\qquad(k>0,\ n\ge0).
$$

The equality is in the integers. Every legal marking pattern is retained, including marking every distinct size. For $k>n$ the sum is empty. The case $n=0$ is a harmless extension supplied here, not a quotation from the paper. The source asks for an analogue; it does not propose the displayed formula as a conjecture.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| All overpartitions of $n$ | `Overpartition n` | A native `Nat.Partition n` and any subset of its support. |
| Integers at most the largest part | `largest`, `U` | The closed positive interval $[1,L(o)]$. |
| Appearing fewer than $k$ times | `multiplicity`, `U` | Total multiplicity includes the overlined occurrence; absent sizes have multiplicity zero. |
| A concise identity for every threshold | `result` | Every natural $k>0$ and every natural $n$, with no bounded enumeration or extra restriction. |
| Counts on the right side | `T`, `N` | All occurrences and actual nonoverlined occurrences, respectively. |

## Motivation

The ordinary-partition identity in Theorem 2.9 motivates this overpartition analogue. Aniceto and Ballantine, arXiv:2608.00278v1, Conclusion, also retain the analogue as an open question. The single theorem `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.result` answers the entire stated Question 3. Its admission basis is `open-problem-resolution (#21566; Proved)`, not an independent novelty claim for its counting ingredients.

## Gap

Ordinary conjugation alone does not preserve a chosen subset of part sizes. The proof needs the equality of support cardinalities under conjugation, the actual change in available marks when copies of a size disappear, and the relation to nonoverlined frequencies for every positive threshold.

Bal and Bhatnagar, arXiv:2102.03486v2, Section 6, already provide the ordinary/distinct decomposition of overpartitions, nonoverlined frequency counts, and threshold-one and threshold-three ingredients. Those ingredients retain their earlier attribution. The two later source versions identify the requested general analogue; they do not establish worldwide absence of an equivalent result. Literature completeness remains unverified.

## Route

All unqualified declaration names here belong to `D5.S3.Combinatorics.Partitions.OverpartitionThreshold`. Summing over marks gives weight $2^{|\operatorname{support}(p)|}$ to an ordinary partition $p$. The support-corner equivalence `cornerEquiv` proves that native Ferrers conjugation preserves the support cardinality. Consequently `sum_largest` exchanges the weighted largest-part sum with the total part count. Its `corner_inverse` directly reuses the exposed original theorem `D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.height_mem_iff`.

The native copy-removal equivalence `shiftEquiv` and its support and weight laws account for disappearance of a marked size. Toggling the optional mark and removing nonoverlined occurrences give `N_step` and `N_B`. Finite summation then proves `A_step`: $A_k(n)+A_{k+1}(n)=2N_k(n)$, where $A_k(n)$ counts positive sizes occurring at least $k$ times across all overpartitions. The complementary count `complement` gives $U_k(n)+A_k(n)=T(n)$. Since `A_large` vanishes for $k>n$, descending induction in `A_alternating` yields the finite alternating sum, and `result` combines the two equalities.

These are consumed components of the one proof, not separately claimed resolutions or additional public theorems. The carrier is the actual marked partition, rather than a replacement family defined to satisfy the identity.

## Falsifier

A positive threshold $k$ and an integer $n\ge0$ for which the displayed finite counts differ would refute this answer. Omitting absent sizes, excluding fully marked partitions, or replacing nonoverlined occurrences by total multiplicities would change the question or its answer. The theorem covers the empty partition and thresholds above $n$ without a finite cutoff on the quantified inputs.

## Evidence

The formal source is [OverpartitionThreshold.lean](../D5/S3/Combinatorics/Partitions/OverpartitionThreshold.lean), with its [Blueprint](../Blueprint/D5/S3/Combinatorics/Partitions/OverpartitionThreshold.md). The public theorem is `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.result`. Its kernel axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. The module has `generality: G` and `utility: none`; the proof is symbolic and unbounded.

The complete authored declaration set has one public endpoint, its six public carrier/statistic declarations, and consumed private helpers. The original per-declaration admission distinguishes the content steps `N_B`, `A_step`, `A_alternating` and `result` from bind-only components. Only the whole endpoint uses the external-open-problem settlement basis. No helper receives an independent escape, novelty or resolution claim.

The source-equivalence registrations for `result` and the exposed provider theorem are retained in their respective `Reg/D5` mirrors. Both include the full original telescope, source reconstruction, lawful readout, variation, sensitivity and observational-dependence evidence. Their continuation is unknown; this is an unknown residual, not a proof of undecidability.

Source passages and locators are in [Bhoria–Eyyunni–Santra](../Library/RecurrenceComposition/bhoria2026missing.md), [Aniceto–Ballantine](../Library/RecurrenceComposition/aniceto2026identities.md), and [Bal–Bhatnagar](../Library/RecurrenceComposition/bal2021stanley.md). The registered original question is [#21566](https://github.com/the-omega-institute/trureturing/issues/21566).

## Triage

### What the settlement shows

| Item | Evidence and conclusion | Boundary |
| --- | --- | --- |
| Full original Question 3 | Proved: `D5/S3/Combinatorics/Partitions/OverpartitionThreshold.result` gives one finite formula for every $k>0$ and every $n\ge0$. | The zero-size input is an explicit extension. |
| Empty input, full marking, and $k>n$ | Included in the same carrier and quantified theorem. | No restricted marking family or bounded range is substituted. |
| Mechanism of the identity | Proved on the live proof path: support-cardinality preservation, copy-removal and mark-disappearance laws, actual nonoverlined frequency, finite summation and descending cancellation. | The earlier decomposition and frequency ingredients remain attributed to Bal–Bhatnagar. |
| Other questions in the source | Open here: the separate congruence and asymptotic questions. | No implication settling them is asserted. |
| Later paper's conclusion | The requested overpartition analogue is supplied by `result`. | Its separate request for combinatorial congruence proofs remains open here. |
| Stronger or alternative formulations | Open here: additional refinements beyond the stated identity. | No new theorem or originality claim follows from a suggested refinement. |

## ASSUMED-UNVERIFIED

Exhaustive literature absence, worldwide priority and originality are unverified. The formal theorem answers the quoted request for an identity under its explicit overpartition interpretation. It does not settle the source's neighboring congruence or asymptotic problems. An unknown audit continuation does not assert undecidability.
