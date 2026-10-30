---
slug: aliabadi-zerbib-2022-matroid-matching-question-2-7
bibkey: aliabadizerbib2024matroidmatching
doi: 10.1007/s10801-024-01308-z
url: https://arxiv.org/abs/2202.07719v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.result
---

# Aliabadi–Zerbib Question 2.7 has a negative answer

## Problem

M. Aliabadi and S. Zerbib, “Matchings in matroids over abelian groups”, arXiv:2202.07719v3, published in *Journal of Algebraic Combinatorics* (2024), Question 2.7, ask:

> Let $G$ be an abelian torsion-free group. Let $M$ be a matroid over $G$ and $N$ be a sparse paving matroid over $G$, both of the same rank $n$, so that $|E(M)| = |E(N)| - 1$ or $|E(M)| = |E(N)|$. If $0 \notin E(N)$, is $M$ matched to $N$?

The [source note](../Library/GraphInvariants/aliabadizerbib2024matroidmatching.md) records the DOI and arXiv locator. The preregistration is [#19681](https://github.com/the-omega-institute/trureturing/issues/19681). The answer is **Refuted** by the settling declaration `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.result`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Abelian torsion-free group | `G`, `[AddCommGroup G]`, `[IsAddTorsionFree G]` in `claim` | The group is arbitrary within the stated class |
| Finite loopless matroids | `M.Finite`, `N.Finite`, `M.Loopless`, `N.Loopless` | The source standing convention is explicit in the proposition |
| Same positive rank | `0 < M.eRank`, `M.eRank = N.eRank` | Rank is Mathlib's extended natural rank |
| Sparse paving target | `IsSparsePaving N` | Both the matroid and its dual are paving |
| Ground-size alternatives | `M.E.ncard + 1 = N.E.ncard ∨ M.E.ncard = N.E.ncard` | Both alternatives are retained |
| Exclusion of zero | `(0 : G) ∉ N.E` | The source's zero condition is literal |
| Matching of ordered bases | `BasesMatched` and `IsMatchedTo` | Injective `Fin n` enumerations and Mathlib bases are used |
| Negative answer | `result : ¬ claim` | The proposition is refuted by an exact integer witness |

## Motivation

A rank-$n$ family on the interval $E = \{1,\ldots,n+s\} \subset \mathbb Z$ can omit one circuit-hyperplane $H = \{s+1,\ldots,s+n\}$. The resulting matroid and its dual remain paving. The initial basis $\{1,\ldots,n\}$ forces every admissible matching target into $H$, so an injective target enumeration has a range that is not a basis.

## Gap

The literature screen recorded in #19681 covers arXiv v3, the accessed journal text, the sequels arXiv:2412.04516v4 and arXiv:2509.14339v2, screened citing works, repository owners and indexed searches. No located publication settles Question 2.7 or Theorem 2.1 in that scope. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

For $n,s \ge 2$, `punctured` constructs the rank-$n$ matroid whose bases are the $n$-subsets of $E$ other than $H$. `allowed_exchange` proves basis exchange, `extend_avoiding` extends every smaller independent set to an allowed base, and the dual base characterization gives the dual paving property. `initial_base` supplies the source basis, `forced_target` puts each admissible target in $H$, and `no_matching_basis` uses injectivity and cardinality saturation to contradict the omitted base. `family_not_matched`, `family_loopless`, `family_rank`, `family_sparse_paving` and `family_zero` provide the hypotheses used by `result` at $n=s=2$.

The symbolic family has `utility: none`. The four-slot escape audit for `result` is unfinished under [#20096](https://github.com/the-omega-institute/trureturing/issues/20096); its source realization, enrolled readout, variation/sensitivity evidence and continuation record are missing.

## Falsifier

The witness takes $G=\mathbb Z$ and $M=N$ from the $n=s=2$ member of the family. The source basis $\{1,2\}$ is a base, while every target compatible with the sum-exclusion condition lies in $H=\{3,4\}$; injectivity forces the target range to be $H$, which is explicitly not a base. This breaks the equal-cardinality branch of Question 2.7. The construction also refutes the quoted self-matching Theorem 2.1 and the equal-cardinality case of Question 2.2. It does not address strict cardinality-gap cases.

## Evidence

Source note: [Aliabadi–Zerbib matroid matching](../Library/GraphInvariants/aliabadizerbib2024matroidmatching.md).

`Library/Combinatorics`, whose domain covers matchings, is at its 96-entry capacity. The note therefore sits in the combinatorics bucket `Library/GraphInvariants`. A Library note's bucket follows its source rather than the module path, as `Library/Asymptotics/zhangzhao2024speyer.md` does for `D5/S3/Combinatorics/Matroids`.

The settling module is `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.lean`; its Scribe displays the complete `claim` proposition under `result`. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

The `result` declaration has `statement_id` `sha256:08172161640aab569dd7cc5be8f2d63f95a2c9b71e810ef46d1678fc3434f726`. The unfinished escape audit for `result` is tracked in [#20096](https://github.com/the-omega-institute/trureturing/issues/20096). The public source definitions are outside the public-theorem registration obligation; no `declared_validated` registration is claimed.

The numerical check is in [trureturing-experiments at commit `56762ab830384d7f7a544ce67ded2b72aade5a91`](https://github.com/the-omega-institute/trureturing-experiments/tree/56762ab830384d7f7a544ce67ded2b72aade5a91/docs/reports/aliabadi-zerbib-2022-matroid-matching-question-2-7). The command `python3 docs/reports/aliabadi-zerbib-2022-matroid-matching-question-2-7/check.py` exits 0 with `RESULT PASS`; `check.py` has SHA-256 `18a050f9225799ff9606b2fb1de54c0098915803d9c6b95c38fc0abc7d7a5aee`. Its exact tested scope is $(n,s) \in \{2,3,4,5\}^2$: the basis axioms, looplessness, sparse paving, and failure of matching for the initial basis in both the uniform source and the punctured target. It also checks the Lemma 3.14 instance $A=B=\{1,2,3\}$ and $X=\{1,\ldots,6\}$, where $6 < 7$.

### Declaration classification

The module has `admission_basis: open-problem-resolution (#19681; Refuted)` and `utility: none`. Its live escape content is the one-deleted-base construction through `allowed_exchange` and `extend_avoiding`, together with the all-parameter theorem `family_sparse_paving`. Registration is a separate obligation: `result` has an unfinished four-slot audit under #20096.

| module | declaration | proof_shape | escape_witness | consumers | direct frozen dependencies | registration status |
| --- | --- | --- | --- | --- | --- | --- |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.IsPaving | bind-only | none (binding/normalization) | IsSparsePaving, family_sparse_paving | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.IsSparsePaving | bind-only | none (binding/normalization) | claim | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.BasesMatched | bind-only | none (binding/normalization) | IsMatchedTo, family_not_matched, no_matching_basis | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.IsMatchedTo | bind-only | none (binding/normalization) | claim, family_not_matched, result | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.claim | bind-only | none (binding/normalization) | result | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.allowed_exchange | content | allowed_exchange: the n-subsets other than H satisfy basis exchange | punctured | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.extend_avoiding | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | punctured, punctured_dual_small_indep, punctured_small_indep | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured | content | allowed_exchange and extend_avoiding: construction of the one-deleted-base matroid | family_finite, family_not_matched, family_sparse_paving, family_zero, initial_base, no_matching_basis, punctured_base, punctured_dual_base, punctured_dual_paving, punctured_dual_rank, punctured_dual_small_indep, punctured_ground, punctured_loopless, punctured_paving, punctured_rank, punctured_small_indep, result | none | not a theorem |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_ground | bind-only | none (binding/normalization) | family_zero, punctured_dual_base | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_base | bind-only | none (binding/normalization) | family_base, punctured_dual_base, punctured_rank | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_small_indep | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | punctured_loopless, punctured_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_rank | bind-only | none (binding/normalization) | family_rank, punctured_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_paving | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | family_sparse_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_dual_base | bind-only | none (binding/normalization) | punctured_dual_rank, punctured_dual_small_indep | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_dual_small_indep | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | punctured_dual_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_dual_rank | bind-only | none (binding/normalization) | punctured_dual_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_dual_paving | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | family_sparse_paving | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.punctured_loopless | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | family_loopless | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.ground_card | bind-only | none (binding/normalization) | family_base, family_finite, family_loopless, family_not_matched, family_rank, family_sparse_paving, family_zero, initial_base, no_matching_basis | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.hole_card | bind-only | none (binding/normalization) | family_base, family_finite, family_loopless, family_not_matched, family_rank, family_sparse_paving, family_zero, initial_base, no_matching_basis, result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.hole_subset | bind-only | none (binding/normalization) | family_base, family_finite, family_loopless, family_not_matched, family_rank, family_sparse_paving, family_zero, initial_base, no_matching_basis, result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_base | bind-only | none (binding/normalization) | initial_base, no_matching_basis | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_finite | bind-only | none (binding/normalization) | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_loopless | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_rank | bind-only | none (binding/normalization) | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_sparse_paving | content | extend_avoiding: every smaller ground subset extends to an allowed n-base | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.initial_injective | bind-only | none (binding/normalization) | family_not_matched | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.initial_range | bind-only | none (binding/normalization) | initial_base, no_matching_basis | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.initial_base | bind-only | none (binding/normalization) | family_not_matched | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.forced_target | bind-only | none (binding/normalization) | no_matching_basis | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.no_matching_basis | bind-only | none (binding/normalization) | family_not_matched | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_not_matched | bind-only | none (binding/normalization) | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.family_zero | bind-only | none (binding/normalization) | result | none | private; outside public-theorem audit |
| D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching | D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching.result | content | allowed_exchange and extend_avoiding in punctured, together with family_sparse_paving for all n,s >= 2 | settlement | none | unfinished #20096 |

## Triage

| Item | Status and evidence |
| --- | --- |
| Settlement of Question 2.7 | **Proved (kernel-checked refutation):** `result : ¬ claim` supplies the negative answer for the quoted proposition |
| Full $n,s \ge 2$ family | **Proved (kernel-checked):** `punctured`, `family_loopless`, `family_rank`, `family_sparse_paving`, `family_not_matched` and `family_zero` establish the loopless sparse-paving family and obstruction; `forced_target` and cardinality-saturation helpers are bind-only with the consumers listed below |
| Wider effect on Theorem 2.1 and Question 2.2 | **Proved in prose:** `family_not_matched` supplies a self-matching counterexample; the hypotheses of the quoted Theorem 2.1 and equal-cardinality case of Question 2.2 are satisfied by this same pair |
| Lemma 3.14 counterexample | **Computed:** the experiment checks $A=B=\{1,2,3\}$, $X=\{1,\ldots,6\}$ with hypotheses true and $6 < 7$; this is outside the Lean claim |
| Uniform-source specialization | **Open:** no separate uniform-source declaration is delivered |
| Finite-cyclic-group specialization | **Open:** no finite-cyclic-group result is delivered |
| Strict cardinality-gap cases | **Open:** the settlement uses equality of ground cardinalities and makes no claim about $\lvert E(M)\rvert=\lvert E(N)\rvert-1$ |
| Mechanism and Rado obstruction | **Proved in prose:** the derivation below shows that the admissible targets lie in $H$ and have union $H$ of rank $n-1$; `forced_target` and `no_matching_basis` prove the target-containment and no-basis statements in Lean |
| Sequel III, Lemma 2.8 and Claim 3.3 | **Open:** #19681 records the search seat's attribution; those proofs are outside this settlement |
| Surviving statements | **Proved in prose (scope only):** Corollary 2.5 assumes $\lvert E(M)\rvert<\lvert E(N)\rvert-1$, whereas the witness has equal ground sets; sequel II, Theorem 3.2 assumes $\lvert E\rvert=n+1$, whereas this family has $\lvert E\rvert=n+s\ge n+2$ |
| Literature completeness | **Literature reading:** the checked screen found no settlement; completeness remains `ASSUMED-UNVERIFIED` |

### Mechanism

Let $T=\{1,\ldots,n\}$. If $a\in T$ and $b\in E$ have $a+b\notin E$, positivity gives $a+b>n+s$, hence $b\ge n+s+1-a\ge s+1$. Thus all admissible targets lie in $H$. Conversely, with $a=n$, every $b\in H$ is admissible, so their union is $H$. Every $(n-1)$-subset of $H$ is independent by `punctured_small_indep`, while $H$ is not a base by `family_base`. An independent $n$-element subset of a rank-$n$ matroid would be a base. Therefore $H$ has rank $n-1$, below $|T|=n$, which is the stated Rado obstruction. This rank calculation is a prose argument; the delivered Lean statements prove containment and the no-matched-basis conclusion.

### What the settlement shows

**Proved (kernel-checked):** the interval family is an actual loopless sparse-paving matroid family, and the initial basis has no matched basis in the punctured target. The failure mechanism is the forced target interval $H$, whose cardinality equals the rank while $H$ is the deleted base.

**Proved in prose from the kernel-checked family:** setting $M=N$ yields a counterexample to the quoted Theorem 2.1 and to the equal-cardinality branch of Question 2.2. The construction does not settle the strict cardinality-gap cases or the source's separate uniform and finite-cyclic specializations.

**Computed:** the experiment confirms the finite grid $(n,s) \in \{2,3,4,5\}^2$ and the Lemma 3.14 instance described in `Evidence`; it does not establish a uniform extension beyond that tested scope.

## ASSUMED-UNVERIFIED

Literature completeness and reconciliation of every publisher-version detail are unverified. The numerical readings are restricted to $(n,s) \in \{2,3,4,5\}^2$. No separate uniform-source theorem, finite-cyclic-group specialization, or strict cardinality-gap conclusion is asserted.
