# Unit Jordan Drift

## Abstract

A unit Jordan block accumulates its fixed coordinate as exact linear drift.

**Theorem 1.1 (Unit Jordan iterates have exact linear drift).**

$$\forall A,\ [\operatorname{AddMonoid}(A)],\ \forall x, y\in A,\ \forall n\in \mathbb{N},\ J^{[n]}(x, y) = (x+n \cdot y, y).$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/UnitJordanDrift.unit_jordan_iterate_eq_linear_drift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J act on a pair by J(x,y)=(x+y,y). For every additive monoid and every natural n, its nth iterate fixes y and sends the first coordinate to x+n y. Thus the generalized coordinate contributes a secular term that is exactly linear in n.

Repository and pinned-Mathlib searches found no packaged unit-Jordan iterate formula. The proof reuses Function.iterate_succ_apply' and succ_nsmul, so only the one-step recursion is proved by induction.

This closes only the source atom's statement that a nontrivial Jordan block at eigenvalue one produces secular drift. The logarithmic-clock decomposition, winding-number quantization, resonance interpretation, and every numerical certificate in appendix E.16 remain outside the theorem.

## References

- Truth anchor: `D5/S1/Eigenstructure/UnitJordanDrift.unit_jordan_iterate_eq_linear_drift`
