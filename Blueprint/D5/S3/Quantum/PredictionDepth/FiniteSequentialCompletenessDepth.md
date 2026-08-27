# Finite Sequential Completeness Depth

## Abstract

Complete finite sequential word spans reach the full Hermitian carrier at bounded depth.

**Theorem 1.1 (Finite-word completeness has a bounded-depth witness).**

$$\forall d: \operatorname{Nat}, \operatorname{NeZero}(d),\\{}A: \operatorname{Type},\\{}J: A \to \operatorname{LinearMap}(\mathbb{R}, \operatorname{HermitianSpace}(d), \operatorname{HermitianSpace}(d)),\\{}\operatorname{span}(\mathbb{R}, \{\operatorname{sequentialWordEffect}(J, w): w: \operatorname{List}(A)\}) = \operatorname{HermitianSpace}(d) \Rightarrow\\{}\exists n: \operatorname{Nat}, n \leq d^{2}-1 \land\\{}\operatorname{span}(\mathbb{R}, \{e: \operatorname{HermitianSpace}(d) \mid \exists w: \operatorname{List}(A), \operatorname{length}(w) \leq n \land e = \operatorname{sequentialWordEffect}(J, w)\}) = \operatorname{HermitianSpace}(d).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/FiniteSequentialCompletenessDepth.finite_sequential_completeness_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each finite word acts on the identity Hermitian effect through the canonical sequentialWordEffect construction on the full real Hermitian carrier.

Canonical trace removal transfers full-span completeness to the real trace-zero carrier, where the frozen finite-word certificate gives the depth bound. Adding back the identity component returns the bounded span to the source's full Hermitian carrier.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/FiniteSequentialCompletenessDepth.finite_sequential_completeness_depth`
- Dependency: [D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate](FiniteSequentialWordCertificate.md)
