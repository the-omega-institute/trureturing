# Weighted symmetric sign models

## Abstract

Compactness of weighted symmetric sign models.

**Definition 1.1 (Two joint defects).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/Compactness.modelDefect`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/Compactness.modelDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nonnegative probability vector p and a real symmetric matrix S determine two nonnegative quantities. The first is the sum of p(a)p(b)(S(a,b)^2-1)^2 over pairs of nodes. The second is the sum of p(a)(sum_b S(a,b)p(b)-c)^2 over nodes. Their sum measures simultaneous failure of the sign and constant weighted row-sum constraints, using the same matrix and the same weights.

**Theorem 1.2 (A positive defect gap).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/Compactness.exists_model_defect_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/Compactness.exists_model_defect_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite order R, an entry bound M, and a nonsquare natural number k. There is a positive lower bound for the joint defect at c=1/sqrt(k) among all nonnegative weights of sum one and all symmetric R by R matrices with entries of absolute value at most M. If the lower bound failed, a convergent subsequence in the product of finite closed boxes would give a zero-defect limit. Nonnegative terms then vanish separately. On the positive-weight support the limiting entries are minus one or one, and all weighted row sums equal c. Reindexing this support gives a symmetric rational matrix and weights of sum one, contradicting the nonsquare row-sum obstruction. Zero weights are permitted throughout and removed only from the limiting model.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/Compactness.exists_model_defect_gap`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/Compactness.modelDefect`
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/RationalRowSum](RationalRowSum.md)
