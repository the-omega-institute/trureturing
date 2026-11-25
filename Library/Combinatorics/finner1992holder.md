---
bibkey: finner1992holder
authors: Helmut Finner
year: 1992
title: A Generalization of Holder's Inequality and Some Probability Inequalities
doi: 10.1214/aop/1176989534
claim: Finner's product-measure inequality bounds products of coordinate-supported factors by their marginal norms under fractional incidence constraints.
strata_touched:
  - D5/S3/Combinatorics/Hypergraphs/FinnerProductMeasure
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Combinatorics/finner1992holder -->
# Finner's product-measure inequality

The original article is in *The Annals of Probability* 20(4), 1893–1901.
Its bibliographic metadata identifies the classical source. The original full text
has not been read: the publisher presents an access challenge.

## Verified locator

DOI: 10.1214/aop/1176989534

Directly read restatement: https://arxiv.org/html/2610.29041v1#S1.SS1

## Verified mathematical scope

Jonathan Bennett and Sewook Oh, *Stability for the adjoint Finner inequality
and improved lower bounds on the k-plane transform*, arXiv:2610.29041v1,
Section 1.1, equations (1.4) and (1.5), restate the product-measure inequality.
For coordinate supports S_j and finite exponents q_j at least one, the incidence
constraint is the balanced equality: the sum of 1/q_j over supports containing
each coordinate is one. The nonnegative factors belong to the corresponding
finite L^{q_j} spaces. The integral of their product after coordinate projection
is bounded above by the product of these norms.

## Formal representation and boundary

`FinnerProductMeasure.finner_product_measure` uses a finite dependent product of
arbitrary measurable probability spaces, the actual `Measure.pi` of the coordinate
measures, and `DependsOn` for coordinate support. Its functions take values in
ENNReal and its nonnegative weights are real. Each coordinate's incidence sum
need only be at most one. The conclusion compares the integral of the product of
the powered factors with the product of their full-product-law integrals raised
to the same powers.

The balanced finite-norm restatement supplies mathematical context; it is not
used as a Lean premise. Weak budgets, empty index sets, empty supports, zero
weights, and zero or infinite factor values are included in the proved ENNReal
statement. In the proof, a unit factor absorbs the slack in a coordinate's budget.
Measurable constant extraction applies even when the extracted constant is
infinite. Marginal integration then removes coordinates one at a time without
changing the underlying product law.

The Lean suppliers are Mathlib's `ENNReal.lintegral_mul_prod_norm_pow_le`,
the measurable ENNReal real-power instance, `lintegral_mul_const`, and the
`lmarginal` composition and measurability theorems. The local-to-global
coordinate induction is supplied by the formalization. This is a formal proof
of a classical inequality; no mathematical originality is claimed. No source
code or substantial article text is reproduced.
