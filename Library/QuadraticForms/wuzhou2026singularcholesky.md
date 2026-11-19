---
bibkey: wuzhou2026singularcholesky
authors: Hongfeng Wu; Kai Zhou
year: 2026
title: Singular Cholesky Fibers over Finite Fields
doi: null
url: https://arxiv.org/abs/2609.00533v1
claim: "Section 8(iv) asks for a Frobenius-equivariant rank-preserving bijection over characteristic-two finite fields that avoids the RREF--lexicographic choice."
strata_touched:
  - D5/S3/QuadraticForms/FrobeniusCholeskyRecipes
  - D5/S3/QuadraticForms/FrobeniusCholeskyLinear
  - D5/S3/QuadraticForms/FrobeniusCholeskyRecursion
  - D5/S3/QuadraticForms/FrobeniusCholeskyResult
license: citation-only
triage: anchor
---

# Singular Cholesky Fibers over Finite Fields

## Verified locator

Source: https://arxiv.org/abs/2609.00533v1

Primary text: https://arxiv.org/html/2609.00533v1

Section 8, item (iv), p. 43:

> Over $\mathbb F_{2^e}$, find a version of the rank-preserving bijection that is Frobenius equivariant and avoids the RREF–lexicographic choice. This would strengthen the present flag-compatible construction without changing its rank behavior.

Section 6, p. 31: “Let $q=2^e$. Recall the definitions”. The two zero fibers are:

$$
B_{n,q}=\{X\in\mathcal T_n(\mathbb F_q):X^2=0\},\qquad
C_{n,q}=\{U\in\mathcal T_n(\mathbb F_q):U^TU=0\}.
$$

The source uses upper triangular matrices, ordinary matrix rank, and entrywise Frobenius $x\mapsto x^2$. The empty matrix is included. The Lean proposition requires one matrix of finite arithmetic recipes at each size, uniform over every presentation of a field of cardinality $2^e$. A recipe uses entries, zero, one, addition, multiplication, inverse, and zero tests. It therefore contains no field-element enumeration or ordering primitive.

## Construction and scope

Nonzero minors select independent columns and coordinate rows. Free-coordinate kernel vectors are obtained by solving the selected invertible minor. Extending independent image columns by these kernel vectors produces two adapted frames. Their coordinate transport maps one kernel bijectively onto the other and preserves membership in the corresponding image. The bordered recursion sends the new column through this transport and sets the final diagonal to the sum of its coordinates. In characteristic two, the square of that sum is the sum of the coordinate squares.

The constructed recipes use standard coordinate indices. Compatibility with arbitrary coordinate changes is a separate question. The full theorem about leading-principal truncations and arbitrary field embeddings is not separately assembled; recipe evaluation compatibility and the construction over arbitrary characteristic-two fields are the supporting mathematical claims.

## Computation

The preregistration cites the private experiments repository https://github.com/the-omega-institute/trureturing-experiments at commit `457a4d7696fa12c2679662aff692b8e2a0feefd2`, program `docs/reports/frobenius-cholesky-bijection/check.py`, SHA-256 `f96fe74b81d5d1779dc07b29f1737123a0e3018cf1336fd96ab09b8a3340b638`. Its reported command is `python3 docs/reports/frobenius-cholesky-bijection/check.py`, exit 0, final line `ALL_CHECKS_OK`. These are cited experiment readings, not a new execution in this delivery.

## Literature boundary

The bounded literature screen in issue #23137 found no settlement of Section 8(iv) among the inspected sources. Completeness is ASSUMED-UNVERIFIED: it is not a proof of priority or an exhaustive exclusion of earlier work. The unread Kirillov full text and incomplete citation inventories remain outside that screen.
