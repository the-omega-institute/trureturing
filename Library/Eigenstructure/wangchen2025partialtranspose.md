---
bibkey: wangchen2025partialtranspose
authors: N. Wang; L. Chen
year: 2025
title: "Equality condition for a matrix inequality by partial transpose"
doi: 10.1142/S1230161226500071
url: https://arxiv.org/abs/2508.18644v1
claim: "Theorem 6 bounds partial-transpose rank by Schmidt rank times the original rank; Section VI asks for the equality condition at Schmidt rank two in arbitrary dimensions."
strata_touched:
  - D5/S3/Quantum/Entanglement/PartialTransposeSaturation
license: citation-only
triage: anchor
---

# Rank saturation under partial transpose

## Locator

URL: https://arxiv.org/abs/2508.18644v1

DOI: 10.1142/S1230161226500071

N. Wang, L. Chen, *Equality condition for a matrix inequality by partial
transpose*, arXiv:2508.18644v1, Theorem 6 and Section VI. These bibliographic
details and the quotations below are supplied in issue #30687 and the task
brief. This implementation does not assert a fresh retrieval of the paper.

## Source statements

FromLiterature: Theorem 6 gives

$$
\operatorname{rank}\!\left(\sum_{j=1}^K R_j^T\otimes S_j\right)
\le K\operatorname{rank}\!\left(\sum_{j=1}^K R_j\otimes S_j\right).
$$

Section VI states:

> An open problem arising from this paper is to find out the condition saturating the inequality for Schmidt-rank-two matrices with any dimensions.

The tensor-sum and first-factor partial-transpose definitions reproduce
these conventions, including rectangular input and output dimensions.
These definitions and the displayed inequality are literature statements.
The inequality is cited here and is not silently assumed as a new axiom.

## Classification and scope

FromRepo: the complete criterion and the proof below are supplied by this implementation.
For a coefficient pair A write h(A) for horizontal concatenation rank and
v(A) for vertical concatenation rank. The classification proves that equality holds
exactly when both pairs satisfy v=2h, or both satisfy h=2v, assuming both
coefficient pairs are linearly independent. The general sufficient
direction is obtained by independent control of the two coefficient
images. The converse uses a complete constructive matrix-pair decomposition
and an additive strict defect calculation.

Classical Kronecker matrix-pencil theory is a precedent for decomposition
into right singular, left singular and regular summands. The
shortest-kernel-chain construction is an internal proof of that
decomposition, not a claim that the classical decomposition is new.
No claim about Schmidt rank at least three, or a complete classification
of equality of the two unscaled ranks, is made here.

## Known special cases

FromLiterature: arXiv:2508.18644v1, Sections IV–V (Theorem 12, Lemma 14,
and Theorem 17), proves saturation conditions for column-vector,
row-vector, and two-by-two first-factor coefficient matrices. Section VI
opens with:

> We have shown that matrix inequality rank(Σ A_j^T ⊗ B_j) ≤ K · rank(Σ A_j ⊗ B_j) can be saturated when A_i's are column or row vectors, or two-by-two matrices.

At Schmidt rank two, these are known special cases of this delivery's
terminal theorem `Classification.result`, under its two coefficient-pair
linear independence hypotheses. The general classification in arbitrary
rectangular dimensions remains FromRepo; the three special cases are
attributed to Wang and Chen.
