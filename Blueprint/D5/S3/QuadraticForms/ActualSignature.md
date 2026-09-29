# Symmetric Matrix Signature by Polynomial Pivots

## Abstract

Polynomial pivots characterize the actual signature of every finite real symmetric matrix.

**Theorem 1.1 (Exact signature characterization).**

$$Realizes(n,A,z) \iff sigPos(Q)-sigNeg(Q)=z$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ActualSignature.realizes_iff_signature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural dimension n, every real symmetric matrix A indexed by Fin n, and every integer z, the recursive relation Realizes(n,A,z) holds exactly when z is the positive index minus the negative index of the quadratic form Q(x) = sum over i,j of x(i) A(i,j) x(j). The indices are the maximal dimensions of positive-definite and negative-definite subspaces.

Dimension zero and the zero matrix have signature zero. A positive diagonal pivot reduces the target integer by one; a negative diagonal pivot increases it by one. If the diagonal vanishes but an off-diagonal entry is nonzero, a two-coordinate hyperbolic pivot leaves the target unchanged.

The residual entries are polynomial expressions. For a diagonal pivot a = A(i,i), the residual entry at retained indices r,s is a squared times A(r,s) minus a times A(i,r) A(i,s). For a zero-diagonal pivot b = A(i,k), it is b squared times A(r,s) minus b times the sum A(i,r) A(k,s) + A(k,r) A(i,s). The retained coordinates are reindexed by deleting the pivot coordinates.

Invertible coordinate changes identify each pivot with a product of its scalar or hyperbolic form and the residual form. Product signatures add, scalar signatures have the scalar's sign, and hyperbolic signatures vanish. Strong induction gives both directions of the equivalence. Residual symmetry and exhaustive pivot existence preserve the conclusion for singular matrices and for zero-diagonal matrices with nonzero off-diagonal entries.

## References

- Truth anchor: `D5/S3/QuadraticForms/ActualSignature.realizes_iff_signature`
