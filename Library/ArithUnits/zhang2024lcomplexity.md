---
bibkey: zhang2024lcomplexity
authors: Pengcheng Zhang
year: 2024
title: The 2-complexity of even positive integers
doi: 10.48550/arXiv.2411.19364
url: https://arxiv.org/abs/2411.19364v1
claim: "Question 3 asks whether every positive multiple n of every l > 1 has some l^{m₀} n in A_l."
strata_touched:
  - D5/S3/Arith/Congruence/ZhangLComplexityEventualStability
license: citation-only
triage: anchor
---

<!-- GID: D5/L/ArithUnits/zhang2024lcomplexity -->

# Eventual stability of l-complexity

## Verified locator

DOI: 10.48550/arXiv.2411.19364

Source: https://arxiv.org/abs/2411.19364v1

Published version: Integers 24 (2024), #A109,
https://math.colgate.edu/~integers/y109/y109.pdf.

## Definition and question

Page 2:

> Given a positive integer n ∈ lZ⁺, define the l-complexity of n, denoted as ‖n‖_l, as the minimal number of l’s that are needed to express n in terms of l using only addition and multiplication (and parentheses).

Question 3, page 10:

> Let l > 1 and define A_l := {n ∈ lZ⁺ : ‖l^m · n‖_l = m + ‖n‖_l for all m ≥ 0}.

> Can one say anything about the set A_l? For example, is it true that for every n ∈ lZ⁺, there exists m₀ ≥ 0 such that l^{m₀} · n ∈ A_l?

## Mathematical correspondence

The expression type and leaf count are
`D5.S3.Arith.Congruence.KumarPengTranModularComplexity.Expr` and
`Expr.leaves`. The natural-number evaluation assigns l to each leaf and uses
addition and multiplication at the internal nodes. Complexity is the natural
infimum of the leaf counts of expressions with the required value. A positive
multiple of l has such an expression, so this infimum is attained. The natural
evaluation and infimum are the public functions `value` and `complexity`;
the formula defining A uses `complexity l`.
At modulus zero, the existing `Expr.eval` takes values in `ZMod 0 = ℤ`.
Casting the natural evaluation to ℤ gives this evaluator, and injectivity of
the natural-number cast identifies the two sets of attainable leaf counts.
The proof therefore uses `KumarPengTranModularComplexity.complexity` at modulus
zero, linked to the natural formula by a private membership equivalence.

The predicate defining A_l is the conjunction of positivity, divisibility by l,
and the displayed equality for every natural m. The formal claim quantifies
over natural l > 1 and positive natural multiples n of l, with a natural m₀.
It answers the explicit every-orbit assertion of Question 3.

The repository proof uses the discrete-defect stabilization method credited in
the source to Altman–Zelinsky: the defect ‖l^m n‖_l − m is nonincreasing and
bounded below by one. The latter follows by induction from the bound that an
expression with s leaves has value at most l^s. The antitone chain condition
gives a constant tail, hence the desired equality at a translate of n.

## Literature boundary

Issue #19862 records the source and published-version screen, related
ordinary-integer-complexity results, and the later-paper screen. No dominating
l-complexity settlement was found in that scope. Literature completeness is
ASSUMED-UNVERIFIED; the author's 2026 thesis was not accessed. A fuller
description of A_l and a bound on the first stable index remain open here.
