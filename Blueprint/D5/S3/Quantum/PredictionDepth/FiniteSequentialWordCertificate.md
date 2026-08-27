# Finite Sequential Word Certificate

## Abstract

Complete centered sequential word effects admit dimension-bounded finite certificates.

**Theorem 1.1 (Complete finite words have dimension-bounded certificates).**

$$\forall d: \operatorname{Nat}, \operatorname{NeZero}(d),\\{}A: \operatorname{Type},\\{}J: A \to \operatorname{LinearMap}(\mathbb{R}, \operatorname{HermitianSpace}(d), \operatorname{HermitianSpace}(d)),\\{}\operatorname{span}(\mathbb{R}, \{\operatorname{centeredHermitianMap}(d, \operatorname{sequentialWordEffect}(J, w)): w: \operatorname{List}(A)\}) = \operatorname{traceZeroHermitian}(d) \Rightarrow\\{}(\exists W: \operatorname{Finset}(\operatorname{List}(A)), \operatorname{card}(W) \leq d^{2}-1 \land\\{}\operatorname{span}(\mathbb{R}, \{\operatorname{centeredHermitianMap}(d, \operatorname{sequentialWordEffect}(J, w)): w\in W\}) = \operatorname{traceZeroHermitian}(d)) \land\\{}(\exists n: \operatorname{Nat}, n \leq d^{2}-1 \land\\{}\operatorname{span}(\mathbb{R}, \{e: \operatorname{traceZeroHermitian}(d) \mid \exists w: \operatorname{List}(A), \operatorname{length}(w) \leq n \land e = \operatorname{centeredHermitianMap}(d, \operatorname{sequentialWordEffect}(J, w))\}) = \operatorname{traceZeroHermitian}(d)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate.finite_sequential_word_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each word acts on the identity Hermitian effect through the imported sequentialWordEffect construction. The imported centeredEffect operation removes its scalar trace component on the exact real trace-zero Hermitian carrier.

If the centered effects of all finite words span that carrier, finite-dimensional basis extraction selects a concrete finite word set with at most d squared minus one members and the same span.

For the depth clause, the uncentered bounded-word spans start with the identity line. Once two consecutive stages agree, prefix closure under every instrument generator makes that equality permanent. Their rank can therefore grow strictly at most d squared minus one times, after which canonical centering gives the full bounded centered span.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate.finite_sequential_word_certificate`
- Dependency: [D5/S3/Quantum/Completion/SequentialWordObservationResidual](../Completion/SequentialWordObservationResidual.md)
- Dependency: [D5/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence](../Fibers/TraceZeroReadoutOrthogonalEquivalence.md)
