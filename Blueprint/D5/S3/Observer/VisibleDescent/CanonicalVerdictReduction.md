# Canonical Verdict Reduction

## Abstract

Verdict tables descend canonically, reduce by column representatives, and remain relative to the implementation population.

**Theorem 1.1 (The true verdict source is its population-relative double quotient).**

$$\begin{aligned}\forall Implementation, Test: \operatorname{Type},\\r: Implementation \to \left(Test \to \operatorname{Bool}\right),\\\operatorname{let} implementationKernel := \operatorname{ker}\left(\lambda i: Implementation, \lambda t: Test, r\left(i, t\right)\right),\\testKernel := \operatorname{ker}\left(\lambda t: Test, \lambda i: Implementation, r\left(i, t\right)\right),\\canonicalVerdict : \operatorname{Quotient}\left(implementationKernel\right) \to \left(\operatorname{Quotient}\left(testKernel\right) \to \operatorname{Bool}\right) := \operatorname{QuotientLift2}\left(r, implementationKernel, testKernel\right) \operatorname{in}\\(\forall i: Implementation, j: Implementation, t: Test, u: Test, implementationKernel\left(i, j\right) \land testKernel\left(t, u\right) \Rightarrow r\left(i, t\right) = r\left(j, u\right)) \land\\(\forall i: Implementation, t: Test, canonicalVerdict\left(\operatorname{class}\left(i\right), \operatorname{class}\left(t\right)\right) = r\left(i, t\right)) \land\\(\forall f: \operatorname{Quotient}\left(implementationKernel\right) \to \left(\operatorname{Quotient}\left(testKernel\right) \to \operatorname{Bool}\right), (\forall i: Implementation, t: Test, f\left(\operatorname{class}\left(i\right), \operatorname{class}\left(t\right)\right) = r\left(i, t\right)) \Rightarrow f = canonicalVerdict) \land\\(\forall kept: \operatorname{Set}\left(Test\right), ((\forall t: Test, \exists q, q \in kept \land testKernel\left(q, t\right)) \land (\forall candidate: \operatorname{Set}\left(Test\right), candidate \subseteq kept \land (\forall t: Test, \exists q, q \in candidate \land testKernel\left(q, t\right)) \Rightarrow kept \subseteq candidate)) \iff (\forall t: Test, \exists! q, q \in kept \land testKernel\left(q, t\right))) \land\\(\forall t: Test, u: Test, t \neq u \land testKernel\left(t, u\right) \Rightarrow \exists rPrime: \operatorname{Option}\left(Implementation\right) \to \left(Test \to \operatorname{Bool}\right), (\forall i: Implementation, rPrime\left(\operatorname{some}\left(i\right)\right) = r\left(i\right)) \land rPrime\left(none, t\right) \neq rPrime\left(none, u\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/VisibleDescent/CanonicalVerdictReduction.canonical_verdict_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The implementation kernel is equality of complete verdict rows, and the test kernel is equality of complete verdict columns. Mathlib's two-quotient lift gives the displayed canonical verdict map; its representative computation rule determines that map uniquely.

A retained test subset is lossless when every original test has a retained test with the same column. Such a subset is inclusion-minimal among lossless subsets exactly when it contains one representative of every column class.

Two distinct tests can agree on every current implementation and cease to agree after one implementation is adjoined. Redundancy is therefore indexed by the chosen implementation population.

The canonical descent and extension witness are imported from their frozen D5 owners. Repository and pinned-Mathlib searches found no existing minimal-lossless-subset characterization with this verdict-column shape.

## References

- Truth anchor: `D5/S3/Observer/VisibleDescent/CanonicalVerdictReduction.canonical_verdict_reduction`
- Dependency: [D5/S0/Naming/VerdictColumnSeparation](../../../S0/Naming/VerdictColumnSeparation.md)
- Dependency: [D5/S3/Observer/Refinement/DoubleExtensionalEvaluationDescent](../Refinement/DoubleExtensionalEvaluationDescent.md)
