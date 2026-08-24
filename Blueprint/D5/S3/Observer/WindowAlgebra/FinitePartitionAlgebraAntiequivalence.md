# Finite Partition Algebra Antiequivalence

## Abstract

Finite real partition algebras and their relations reconstruct each other.

**Theorem 1.1 (Relations and real partition algebras reconstruct each other).**

$$\forall X, R, A,\ \operatorname{Finite}(X) \land \operatorname{Equivalence}(R) \land\ A \in \operatorname{Subalgebra}(\mathbb{R}, X \to \mathbb{R}) \Rightarrow\ R_{A_{R}} = R \land A_{R_{A}} = A.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WindowAlgebra/FinitePartitionAlgebraAntiequivalence.finite_partition_algebra_antiequivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be finite and R an equivalence relation. The algebra associated to R is constructed as the real functions constant on every R-class. Its agreement relation recovers R because an indicator of either class separates every nonrelated pair.

Conversely, let A be a real function subalgebra. Agreement under all members of A defines a relation independently of the target algebra. Finite products of normalized separating functions put each relation-class indicator in A; a finite quotient expansion then expresses every relation-constant function as a member of A.

Repository and pinned-Mathlib searches found no exact theorem on the real carrier. The nearby observable-algebra theorem uses complex star subalgebras, so only its finite indicator proof pattern is adapted here; no complex-carrier statement is used as coverage.

## References

- Truth anchor: `D5/S3/Observer/WindowAlgebra/FinitePartitionAlgebraAntiequivalence.finite_partition_algebra_antiequivalence`
