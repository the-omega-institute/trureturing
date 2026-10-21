---
slug: lemos-moura-ribas-silva-2024-consecutive-davenport-conjecture-3-4
bibkey: lemos2024consecutivedavenport
doi: 10.48550/arXiv.2404.11312
url: https://arxiv.org/abs/2404.11312v1
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.result
---

# Lemos–Moura–Ribas–Silva Conjecture 3.4

## Problem

A. Lemos, A. O. Moura, S. Ribas and A. T. Silva, “A note on weighted consecutive Davenport constant,” arXiv:2404.11312v1, Conjecture 3.4, p. 3, asks whether $C(G)=|G|$ for every finite group $G$. The settlement is **Proved** under the literal conventions preregistered in [#19765](https://github.com/the-omega-institute/trureturing/issues/19765).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Ordered sequences over $G$ | `List G` | The ordered product is `List.prod` in list order. |
| Ordered subsequences $g_i\cdots g_j$ with $1\le i\le j$ | `T ≠ [] ∧ T <:+: S` | Nonempty contiguous infix is literal. |
| Consecutive product-one condition for $A=\{1\}$ | `HasConsecutiveProductOne S` | `T.prod = 1` keeps the unweighted convention. |
| Smallest positive threshold | `C G` | `sInf` of the positive natural thresholds with the stated property. |
| Every finite group has $C(G)=|G|$ | `claim` and `result` | `result` proves the complete quantified proposition. |

## Motivation

The settling declaration is `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.result`, with admission basis `open-problem-resolution (#19765; Proved)`. The source note is `Library/FiniteGroups/lemos2024consecutivedavenport.md`. The preregistration supplies the source statement, Lean conventions, experiment and literature screen.

## Gap

The source proves the finite abelian and metacyclic cases and leaves the universal finite-group assertion as Conjecture 3.4. The delivered theorem covers arbitrary finite groups, including nonabelian groups, without adding a commutativity or metacyclic hypothesis.

The escape audit for `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.result` is unfinished under [#19869](https://github.com/the-omega-institute/trureturing/issues/19869). No Reg mirror or `declared_validated` registration is claimed.

## Route

For a word of length at least $|G|$, the $|G|+1$ prefix products contain a repeated value. The intervening nonempty block has product one, giving the upper threshold bound. For the lower bound, enumerate $G$ as $e(0),\ldots,e(n-1)$ and use successive letters $e(i)^{-1}e(i+1)$. Prefix products are $e(0)^{-1}e(i)$ and are pairwise distinct, so the word of length $n-1$ has no nonempty product-one block. The two bounds identify the least positive threshold.

The imported frozen declaration `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterBlockConstruction.actual_finite_identity_interval` supplies the finite prefix-product interval. The remaining list identities and quotient-word argument use the pinned Mathlib import closure.

## Falsifier

A finite group and sequence of length at least its order with no nonempty contiguous product-one block would contradict the upper bound. A product-one-free sequence of length one less than the group order would contradict the lower bound. A mismatch between the source's ordered, unweighted conventions and the Lean definitions would invalidate the settlement.

## Evidence

`D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.result` proves the complete `claim` in Lean. The public surface consists of `HasConsecutiveProductOne`, `C`, `claim` and `result`; private helpers are consumed on the result's proof path. The module has `generality: I` and `utility: none`. Its Scribe carries one Proved `OpenProblemResolutionClaim` on `result`.

The experiment entry is [the pinned check directory](https://github.com/the-omega-institute/trureturing-experiments/tree/a8bf7b81/docs/reports/lemos-moura-ribas-silva-2024-consecutive-davenport-conjecture-3-4). Command: `python3 /Users/auric/trureturing-experiments/docs/reports/lemos-moura-ribas-silva-2024-consecutive-davenport-conjecture-3-4/check.py`; exit code 0. Script SHA-256: `64ed0caaa7658c94d8615e88a428bee33b43b771bafa9e4dde70f288f83d347b`. It checks $C(G)=|G|$ for all words of lengths $|G|-1$ and $|G|$ in $C_2\times C_2$, $C_6$, $S_3$, $D_4$ and $Q_8$, counts exactly $(|G|-1)!$ product-one-free words at length $|G|-1$, and checks the prefix-quotient construction for $A_4$, $S_4$ and the nonabelian group of order $21$. These finite readings do not establish the universal theorem.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Conjecture 3.4 for every finite group | Proved; kernel-checked | `D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.result` proves `claim`. |
| Prefix-product mechanism | Proved; kernel-checked | The result's upper-bound and quotient-word proof establishes repeated-prefix and distinct-prefix directions. |
| Finite abelian, metacyclic and indicated direct-product cases | Proved; logical consequence | They are instances of the universal result; no companion theorem is added. |
| Inverse characterization of extremal words | Open | The equivalence between product-one-free words of length $|G|-1$ and enumerations of $G$ is not separately formalized. |
| Extremal count $(|G|-1)!$ | Open | No counting declaration is delivered. |
| Weighted $A$ versions | Open | Larger weight sets from Section 4 are outside the settled statement. |
| Novel proof-technique or bibliographic-priority claim | Open; literature reading | No new technique or priority claim is asserted. |
| Finite experiment | Computed | The pinned experiment entry above gives the exact groups, lengths and construction checks. |

## ASSUMED-UNVERIFIED

The literature screen recorded in preregistration #19765 covers arXiv:2404.11312v1, the cited cyclic work, later related papers and repository and issue searches. No universal nonabelian settlement was located in that searched scope. Literature completeness and publication priority remain `ASSUMED-UNVERIFIED`. The inverse characterization, factorial count and weighted extensions remain outside the kernel-checked result. The escape audit remains unfinished under #19869.
