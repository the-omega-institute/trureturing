# The Whole Selfadjoint Ideal

## Abstract

Whole selfadjoint restriction with the original Jordan and commutator operations.

**Theorem 1.1 (Closed ideal and exact original operations).**

$$(\operatorname{IsClosed}(I)) \land (\forall (a: X), \forall (r: I), \operatorname{S}(a, r)\in I) \land (\forall (r: I), \forall (s: I), \operatorname{D}(r, s)\in I) \land (\forall (r: I), \forall (t: U), \operatorname{j}(r, t)=\operatorname{r}(\operatorname{inc}(t))) \land (\forall (r: I), \forall (s: I), \operatorname{j}(\operatorname{S}(r, s))=\operatorname{Jordan}(\operatorname{j}(r), \operatorname{j}(s))) \land (\forall (r: I), \forall (s: I), \operatorname{j}(\operatorname{D}(r, s))=\operatorname{Oriented}(\operatorname{j}(r), \operatorname{j}(s)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/C128IdealJordan.whole_selfadjoint_ideal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same Y, U, operator-norm matrix algebra M and whole C0 algebra A. X is the whole selfadjoint part of C(Y,M), and I is the real submodule consisting of every selfadjoint field in the whole zero-off-U ideal J. The map j is the real linear isometry equivalence from I onto the whole selfadjoint part of A. Its inverse is zero extension; j itself is restriction.

S(a,b)=(ab+ba)/2 is the original real Jordan product and D(a,b)=i(ab-ba)/2 is the original oriented commutator. I is closed in X and S(X,I) is contained in I. For every r,s in I, D(r,s) belongs to I. The displayed Jordan and Oriented operations on A have precisely these same formulas, and j preserves both formulas on every pair. No completeness claim is made for a polynomial-plus-ideal original domain.

The inverse restriction and exact norm of the whole complex extension produce the real linear isometry equivalence. Its selfadjointness follows from star preservation. The ideal laws follow pointwise from zero outside U. Subsequent local-section arguments use the onto map j to detect ambient Jordan annihilation.

## References

- Truth anchor: `D5/S3/ContinuousObservables/C128IdealJordan.whole_selfadjoint_ideal`
- Dependency: [D5/S3/ContinuousObservables/C128ZeroExtension](C128ZeroExtension.md)
