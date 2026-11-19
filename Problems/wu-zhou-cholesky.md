---
slug: wu-zhou-cholesky
bibkey: wuzhou2026singularcholesky
doi: null
url: https://arxiv.org/abs/2609.00533v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/FrobeniusCholeskyResult.result
---

# Frobenius-equivariant rank-preserving Cholesky bijections

## Problem

Hongfeng Wu and Kai Zhou, *Singular Cholesky Fibers over Finite Fields*, arXiv:2609.00533v1, Section 8(iv), p. 43, ask:

> Over $\mathbb F_{2^e}$, find a version of the rank-preserving bijection that is Frobenius equivariant and avoids the RREF–lexicographic choice. This would strengthen the present flag-compatible construction without changing its rank behavior.

For every $e\geq1$ and $n\geq0$, the answer supplies a single matrix $p_n$ of finite arithmetic decision expressions. Over every field $F$ of cardinality $2^e$, its evaluation gives a bijection

$$
\Phi_n:B(F,n)\longrightarrow C(F,n),\qquad
B(F,n)=\{X:X\text{ upper triangular},\ X^2=0\},\quad
C(F,n)=\{U:U\text{ upper triangular},\ U^TU=0\}.
$$

For every $X\in B(F,n)$, it satisfies

$$
\operatorname{rank}\Phi_n(X)=\operatorname{rank}X,\qquad
\Phi_n(X^{[2]})=\Phi_n(X)^{[2]},
$$

where $[2]$ squares entries. The empty matrix is included. Recipes use input entries, zero, one, addition, multiplication, inversion and zero tests; they contain no field-element ordering or enumeration primitive. Standard coordinate indices remain part of the construction.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Upper triangular square-zero fiber | `FrobeniusCholeskyRecipes.B` | Literal set-builder condition |
| Upper triangular zero Gram fiber | `FrobeniusCholeskyRecipes.C` | Literal transpose-product condition |
| Every $e\geq1$, every $n\geq0$, every field of size $2^e$ | `FrobeniusCholeskyResult.claim` | Natural-number binders, field instances and cardinality hypothesis |
| Explicit replacement of RREF–lexicographic choice | One matrix of `Recipe n`, before the field binder | Finite arithmetic syntax with zero tests, uniform over field presentations |
| Bijection and rank preservation | `Set.BijOn` and rank conjuncts of `claim` | Entire source fibers, all source inputs |
| Frobenius equivariance | Final conjunct of `claim` | Entrywise `frobenius F 2` |

The Lean instances express the field operations, finiteness, decidable equality and characteristic two. They do not impose a choice of field-element order. The finite arithmetic syntax strengthens the requested explicitness; it does not restrict the input matrices. Generality is G and utility is none.

## Motivation

The source's RREF–lexicographic rule selects field vectors using a chosen order. Zero and nonzero minors instead select coordinate frames in a way compatible with injective field homomorphisms. The construction addresses the singular zero Gram fiber, where a nonsingular Cholesky theorem does not supply the required correspondence.

## Gap

The named external question is preregistered in issue #23137. Its bounded literature screen reports no settlement in the inspected sources. It distinguishes related regular-LPM Cholesky work and binary counting or bijection results from this Frobenius-equivariant singular-fiber question. Literature completeness is ASSUMED-UNVERIFIED.

## Route

Select independent image columns and a nonzero minor. Solve the selected minor to obtain free-coordinate kernel vectors. Extend the image columns to kernel frames, and transport coordinates between the two adapted frames. This gives a bijection between the kernels that carries the old image onto the old image.

For the bordered input $\left[\begin{smallmatrix}X&v\\0&0\end{smallmatrix}\right]$, transport $v$ to $w$ and set $c=\sum_iw_i$. In characteristic two,

$$
c^2=\left(\sum_iw_i\right)^2=\sum_iw_i^2.
$$

The off-diagonal Gram equations follow from kernel membership. The final equation follows from this identity. If another diagonal entry satisfies it, its difference from $c$ has square zero and is therefore zero in a field. Image membership determines the rank increment on both sides. Dimension induction produces the uniform arithmetic recipes.

## Falsifier

A failure of any bijection, rank or Frobenius conjunct on an upper triangular square-zero input would contradict the settling claim. The experiments independently enumerate both fibers and check both inverse identities in their stated finite ranges; finite computation alone does not prove the unbounded theorem. Arbitrary coordinate-change naturality, twisted Gram forms and Hermitian analogues are outside the proved statement.

## Evidence

`D5/S3/QuadraticForms/FrobeniusCholeskyResult.result` proves the complete `claim`; its module has admission basis `open-problem-resolution (#23137; Proved)`. The supporting closed sources are `FrobeniusCholeskyRecipes`, `FrobeniusCholeskyLinear` and `FrobeniusCholeskyRecursion`. They carry `escape-witness` admission bases. The existing `MinimumCostRoleBasis` supplies the reused greedy scan and linear-matroid facts used by these sources.

The source note is [wuzhou2026singularcholesky](../Library/QuadraticForms/wuzhou2026singularcholesky.md). The four-slot escape audit for every public theorem remains unfinished under [issue #24291](https://github.com/the-omega-institute/trureturing/issues/24291). A faithful dependent-family reconstruction, bridge and variation evidence are missing; no `declared_validated` registration is claimed.

### Exact finite computation

The program is pinned in [trureturing-experiments at 457a4d7696fa12c2679662aff692b8e2a0feefd2](https://github.com/the-omega-institute/trureturing-experiments/tree/457a4d7696fa12c2679662aff692b8e2a0feefd2/docs/reports/frobenius-cholesky-bijection), path `docs/reports/frobenius-cholesky-bijection/check.py`. Its SHA-256 is `f96fe74b81d5d1779dc07b29f1737123a0e3018cf1336fd96ab09b8a3340b638`. Running the exact pinned bytes with `python3 /Users/auric/.sshx/0e108031e76986bc7788cafe/attempt-1/check-experiment.py` exits 0 and reports `ALL_CHECKS_OK`.

The tested ranges are GF(2) for $0\leq n\leq5$, GF(4) for $0\leq n\leq4$, and GF(8) for $0\leq n\leq3$. The program exhaustively enumerates both fibers and checks inverse identities, upper triangularity, zero Gram, rank, Frobenius and truncation. At the largest sizes the rank distributions are $(1,49,142)$, $(1,171,324)$ and $(1,119)$ respectively. Both GF(4) to GF(16) embeddings, with generator images 6 and 7 in the program's binary labels, commute on all 496 size-4 square-zero inputs. These are computed finite readings, not a uniform proof of the additional compatibilities.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Recipes commute with arbitrary field embeddings; Frobenius needs no field enumeration | Proved, kernel-checked: private `FrobeniusCholeskyRecipes.recipe_eval_map` and public `recipe_map_frobenius` | Exact recipe evaluation and matrix evaluation |
| Rank-preserving bijections exist over every characteristic-two field, without finiteness or perfectness | Proved, kernel-checked: private `FrobeniusCholeskyResult.uniform_rank_recipe` | Every dimension and every characteristic-two field |
| Final diagonal is the coordinate sum; the square identity gives Gram and uniqueness | Proved, kernel-checked: private `FrobeniusCholeskyRecursion.sum_square`, `last_diagonal_unique`, and public `recursiveStep_bijOn` | The bordered recursive construction |
| Exhaustive finite checks and both GF(4) to GF(16) embeddings | Computed: the pinned experiment entry above, exit 0 and stated SHA-256 | GF(2) through size 5, GF(4) through size 4, GF(8) through size 3; both embeddings on 496 size-4 inputs |
| Full family theorem for arbitrary field embeddings and leading-principal truncation | Open as a separately assembled formal theorem | Recipe-level embedding compatibility is kernel-checked; truncation in the stated ranges is computed |
| Naturality under arbitrary coordinate changes | Open | Standard coordinate-index choices remain; no coordinate-free naturality theorem is asserted |

### What the settlement shows

The proved mechanism is uniform kernel-frame transport combined with the characteristic-two sum-of-squares identity. The private `uniform_rank_recipe` theorem removes field finiteness and perfectness from the bijection and rank construction. The public `result` adds Frobenius compatibility through recipe evaluation.

The source's item (iv) receives an affirmative answer. Its earlier rank-preserving binary construction and its counting results retain their statements; this result supplies a compatible replacement construction. The separate coordinate-independent naturality question in Remark 5.4 remains open. No theorem for twisted or Hermitian Gram forms follows from the delivered statement.

## ASSUMED-UNVERIFIED

The literature screen recorded in #23137 is bounded. OpenAlex and Semantic Scholar citing-work inventories were unavailable, the broad full-text searches were not exhaustive, and the Ekhad–Zeilberger and Kirillov full contents were not reliably read. The absence of a screened settlement is not a proof of priority. Completeness remains ASSUMED-UNVERIFIED.
