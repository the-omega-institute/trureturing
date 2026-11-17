---
slug: op-martinez2307
bibkey: martinez2024pielements
doi: 10.1002/mana.202300338
url: https://arxiv.org/abs/2307.09868v3
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.result
---

# The largest order prime does not bound the fixed-element commuting fraction

## Problem

Juan Martínez, *On the commuting probability of π-elements in finite groups*, arXiv:2307.09868v3, §4, printed page 16, immediately after Theorem 4.7, asks:

> As we mentioned in the Introduction, it remains as an open question whether Theorem A holds with $\leq 1/q$, where $q$ is the largest prime dividing $o(x)$.

Theorem A assumes a finite group $G$, a nonempty set of primes $\pi$ and $x\in G_\pi\setminus O_\pi(G)$, and bounds $|C_G(x)_\pi|/|G_\pi|$ by the reciprocal of the smallest prime in $\pi$. The question replaces that prime by the largest prime divisor of $o(x)$. The [Library note](../Library/FiniteGroups/martinez2024pielements.md) records the source quotations; [#24851](https://github.com/the-omega-institute/trureturing/issues/24851) fixes the full assertion and literal Lean conventions.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every finite group | `claim` quantifies over `G : Type` with `Group G` and `Finite G` | Actual finite groups, with no solvability or center restriction. |
| A nonempty set of primes | Arbitrary `π : Set ℕ`, primality of its members and `π.Nonempty` | No finiteness assumption on the prime set. |
| A π-element | `piElements` requires every prime divisor of `orderOf x` to belong to π | The identity is included. |
| Outside the normal π-core | `piCore` is the supremum of normal `isPiSubgroup` subgroups; `claim` assumes nonmembership | These are the literal preregistered standard conventions, not quotations of separate source definitions. |
| Largest prime dividing the element order | An existential prime divisor dominating every prime divisor of `orderOf x` | Existence is explicit; radical nonmembership excludes the identity. |
| Fixed-element fraction | `commutingFraction` counts π-elements in the singleton centralizer and divides by all π-elements, in ℚ | Both cardinalities are cast to ℚ; the denominator includes the identity. |
| The proposed reciprocal bound | The last conjunct of `claim` | The source's fixed-element observable, without replacing it by pair probability. |
| Negative answer | `result : ¬ claim` | Refutes the complete universal claim. |

## Motivation

A prime dividing the order of an element can come from its coordinate inside a normal π-subgroup, while a different coordinate keeps the element outside the product π-core. The largest order prime therefore need not control this fixed-element fraction.

## Gap

The bounded literature screen in #24851 found no exact answer in the inspected arXiv revision, accessible citing works and author papers, formalization catalogs and repository sources. Detomi–Senise–Shumyatsky, arXiv:2605.22955v1, Example 3.3, already uses direct products of odd-prime dihedral groups for a different averaged observable. Neither the dihedral construction nor the generic product mechanism is claimed new. The source's journal text was inaccessible, and literature completeness remains `ASSUMED-UNVERIFIED`.

## Route

The module `D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation` has `generality: G` and `admission_basis: open-problem-resolution (#24851; Refuted)`. Every theorem is classified `bind-only` after expansion of same-delivery helpers. The private helpers are consumed in the settling proof. The certified-instance utility refutes `claim` through `result`. All imports are pinned Mathlib; there are no D5 prerequisites.

For each prime $q\ge5$, take $G_q=\operatorname{DihedralGroup}(3)\times\operatorname{DihedralGroup}(q)$, $\pi_q=\{2,q\}$ and $x_q=(\operatorname{sr}(0),\operatorname{r}(1))$. Here `DihedralGroup n` has order $2n$. The private `family_core` identifies $O_{\pi_q}(G_q)=1\times\operatorname{DihedralGroup}(q)$. The private `family_pi_card` and `family_centralizing_card` prove the counts $8q$ and $2q$. The private `family_counterexample` combines membership, radical nonmembership, order $2q$ and fraction $1/4$. The public `result` specializes to $q=5$.

## Falsifier

At $q=5$, the element has order $10$, whose largest prime divisor is $5$. Its fixed-element fraction is $10/40=1/4>1/5$. The group and its π-core are actual finite groups and subgroups, rather than abstract cardinal data. The first-coordinate reflection is nonidentity, so the element lies outside the identified π-core.

## Evidence

The kernel-checked settling declaration is `D5.S3.FiniteGroups.Frobenius.MartinezLargestOrderPrimeCommutingRefutation.result`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The Scribe shows every public definition's body and the full negated claim for the result.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The exact experiment is [martinez-largest-order-prime-commuting at commit a7fc2e0a94fb37115555794184d7d7934db2b8a3](https://github.com/the-omega-institute/trureturing-experiments/tree/a7fc2e0a94fb37115555794184d7d7934db2b8a3/docs/reports/martinez-largest-order-prime-commuting). The immutable `check.py` was verified with `git cat-file -e` and retrieved unchanged. Command: `python3 -u /Users/auric/.op-scratch/op/op-martinez2307/stageb/check.py`, exit 0; SHA-256 `f36fd2bde944e7b3e106b9852df5bc8240ff66a9b5ad68e74fe002495abaeba4`. Its final result is `ALL_CHECKS_OK`.

The tested primes are exactly $5,7,11,13,17,19,23,29,31$. For each, the checker obtains $|G_q|=12q$, $o(x_q)=2q$, $|(G_q)_{\pi_q}|=8q$, $|C_{G_q}(x_q)\cap(G_q)_{\pi_q}|=2q$, $|O_{\pi_q}(G_q)|=2q$, $|\langle x_q^{G_q}\rangle|=6q$, $|Z(G_q)|=1$, and fraction $1/4>1/q$. It independently checks the source's Theorem A bound for every eligible element of these nine groups. Its fidelity examples give $\operatorname{Pr}_5(\operatorname{PSL}(2,5))=145/625=29/125$ and the $S_3$ transposition fraction $1/2$ for $\pi=\{2\}$. These are computation evidence within that exact scope.

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| The largest-prime universal bound is false. | proved | Kernel-checked `result`, using $q=5$. |
| A second-factor π-core element supplies the order prime $q$, while the first-coordinate reflection keeps the product outside its π-core; the fraction is constantly $1/4$. | proved | Kernel-checked private `family_core`, `family_order`, `family_pi_card`, `family_centralizing_card`, `family_fraction` and `family_counterexample`. |
| The counterexamples form a family for every prime $q\ge5$, rather than only $q=5$. | proved | Kernel-checked private `family_counterexample` has this full parameter range; `result` proves the largest-prime contradiction at $q=5$. |
| For the nine checker primes the center is trivial, the π-core has order $2q$, and the normal closure of $x_q$ has order $6q$. Nontrivial center is therefore unnecessary for these checked counterexamples. | computed | The immutable exact experiment in Evidence, exit 0 and the SHA-256 above; no uniform Lean theorem about centers or normal closures is asserted. |
| Theorem B under the hypothesis that $F^*(G)$ is a π-prime-complement group. | open | Literature reading: an established restricted source result; its formalization and testing its hypothesis on this family are outside this settlement. |
| The smallest-prime-dividing-$o(x)$ replacement, and other restrictions eliminating radical prime padding. | open | Neither `result` nor the checker settles these assertions. The source's Theorem A with $\min\pi$ is not refuted. |
| Downstream consequences of an affirmative answer. | open | Literature reading: the source presents a question; no dependent theorem was identified in the bounded screen. No downstream theorem is shown invalid. |

### What the settlement shows

**Proved in this module:** private `family_counterexample` gives the constant fraction $1/4$ for every prime $q\ge5$, with order $2q$ and radical nonmembership. The normal-core identification and the two element counts explain how the second factor changes the element order without reducing that fraction. The public `result` turns the $q=5$ instance into the exact source refutation.

**Computed:** the nine tested groups are centerless and have the normal-closure and π-core orders recorded above. Extending these additional checks to a uniform theorem is open here.

**Literature reading:** Theorem A with the smallest prime of $\pi$ and the restricted Theorem B retain their stated scope. The assertion refuted here is explicitly a question, so no source theorem is invalidated by the negative answer. The separate smallest-prime-dividing-order question remains open here.

## ASSUMED-UNVERIFIED

Literature completeness and priority are `ASSUMED-UNVERIFIED`. The journal version and the full texts of DOI 10.1016/j.jcta.2024.105954 and DOI 10.4171/RSMUP/130 were unread in the recorded screen. Global arXiv full-text search was unavailable; citation and web services imposed rate limits, access blocks or unusable responses. Freshness and coverage of the supplied AFTD and CoPEER snapshots were not certified. The inspected papers do not constitute a proof-by-proof audit of all related literature. No finite computation is treated as a proof of an unbounded claim.
