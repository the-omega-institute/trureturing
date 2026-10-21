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

The [source note](../Library/Geometry/aliabadizerbib2024matroidmatching.md) records the DOI and arXiv locator. The preregistration is [#19681](https://github.com/the-omega-institute/trureturing/issues/19681). The answer is **Refuted** by the settling declaration `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.result`.

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

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Falsifier

The witness takes $G=\mathbb Z$ and $M=N$ from the $n=s=2$ member of the family. The source basis $\{1,2\}$ is a base, while every target compatible with the sum-exclusion condition lies in $H=\{3,4\}$; injectivity forces the target range to be $H$, which is explicitly not a base. This breaks the equal-cardinality branch of Question 2.7. The construction also refutes the quoted self-matching Theorem 2.1 and the equal-cardinality case of Question 2.2. It does not address strict cardinality-gap cases.

## Evidence

The settling module is `D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching.lean`; its Scribe displays the complete `claim` proposition under `result`. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`. The module's public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration.

The unfinished escape audit for the public declarations is tracked in [#20096](https://github.com/the-omega-institute/trureturing/issues/20096); no `declared_validated` registration is claimed.

The numerical check is in [trureturing-experiments at commit `56762ab830384d7f7a544ce67ded2b72aade5a91`](https://github.com/the-omega-institute/trureturing-experiments/tree/56762ab830384d7f7a544ce67ded2b72aade5a91/docs/reports/aliabadi-zerbib-2022-matroid-matching-question-2-7). The command `python3 docs/reports/aliabadi-zerbib-2022-matroid-matching-question-2-7/check.py` exits 0 with `RESULT PASS`; `check.py` has SHA-256 `18a050f9225799ff9606b2fb1de54c0098915803d9c6b95c38fc0abc7d7a5aee`. Its exact tested scope is $(n,s) \in \{2,3,4,5\}^2$: the basis axioms, looplessness, sparse paving, and failure of matching for the initial basis in both the uniform source and the punctured target. It also checks the Lemma 3.14 instance $A=B=\{1,2,3\}$ and $X=\{1,\ldots,6\}$, where $6 < 7$.

## Triage

| Item | Status and evidence |
| --- | --- |
| Settlement of Question 2.7 | **Proved (kernel-checked refutation):** `result : ¬ claim` supplies the negative answer for the quoted proposition |
| Full $n,s \ge 2$ family | **Proved (kernel-checked):** `punctured`, `family_loopless`, `family_rank`, `family_sparse_paving`, `family_not_matched` and `family_zero` establish the loopless sparse-paving family and obstruction; `forced_target` and cardinality-saturation helpers are bind-only and consumed |
| Wider effect on Theorem 2.1 and Question 2.2 | **Proved (kernel-checked application):** the same family is not matched to itself, so the quoted self-matching theorem and equal-cardinality case fail |
| Lemma 3.14 counterexample | **Computed:** the experiment checks $A=B=\{1,2,3\}$, $X=\{1,\ldots,6\}$ with hypotheses true and $6 < 7$; this is outside the Lean claim |
| Uniform-source specialization | **Open:** no separate uniform-source declaration is delivered |
| Finite-cyclic-group specialization | **Open:** no finite-cyclic-group result is delivered |
| Strict cardinality-gap cases | **Open:** the settlement uses equality of ground cardinalities and makes no claim about $|E(M)|=|E(N)|-1$ |
| Literature completeness | **Literature reading:** the checked screen found no settlement; completeness remains `ASSUMED-UNVERIFIED` |

### What the settlement shows

**Proved (kernel-checked):** the interval family is an actual loopless sparse-paving matroid family, and the initial basis has no matched basis in the punctured target. The failure mechanism is the forced target interval $H$, whose cardinality equals the rank while $H$ is the deleted base.

**Proved (kernel-checked application):** setting $M=N$ yields a counterexample to the quoted Theorem 2.1 and to the equal-cardinality branch of Question 2.2. The construction does not settle the strict cardinality-gap cases or the source's separate uniform and finite-cyclic specializations.

**Computed:** the experiment confirms the finite grid $(n,s) \in \{2,3,4,5\}^2$ and the Lemma 3.14 instance described in `Evidence`; it does not establish a uniform extension beyond that tested scope.

## ASSUMED-UNVERIFIED

Literature completeness and reconciliation of every publisher-version detail are unverified. The numerical readings are restricted to $(n,s) \in \{2,3,4,5\}^2$. No separate uniform-source theorem, finite-cyclic-group specialization, or strict cardinality-gap conclusion is asserted.
