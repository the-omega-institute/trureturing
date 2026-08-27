# Canonical Admissible Fiber Decomposition

## Abstract

A readout canonically decomposes all states and admissible states into dependent fibers.

**Definition 1.1 (Admissible concept fiber).**

$$\forall X, B: \operatorname{Type}, q: X \to B, Adm: X \to \operatorname{Prop}, b: B, \operatorname{AdmissibleConceptFiber}\left(q, Adm, b\right) = \sum_{x: X} {Adm(x) \land q(x) = b}.$$

*Formalization.* `D5/S3/ConceptDynamics/Fibers/CanonicalAdmissibleFiberDecomposition.AdmissibleConceptFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The admissible fiber over b contains a state x, evidence that x is admissible, and an equality q(x) = b.

**Theorem 1.2 (Ordinary and admissible states decompose into canonical fibers).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}q: X \to B, Adm: X \to \operatorname{Prop},\\{}{\exists! e: X \equiv \sum_{b: B} \operatorname{ConceptFiber}\left(q, b\right), {\forall x: X, e(x) = \langle q(x), \langle x, refl \rangle \rangle} \land {\forall b: B, x: X, p: q(x) = b, e^{-1}(\langle b, \langle x, p \rangle \rangle) = x}} \land\\{}{\exists! e_{Adm}: \sum_{x: X} Adm(x) \equiv \sum_{b: B} \operatorname{AdmissibleConceptFiber}\left(q, Adm, b\right), {\forall x: X, h: Adm(x), e_{Adm}(\langle x, h \rangle) = \langle q(x), \langle x, h, refl \rangle \rangle} \land {\forall b: B, x: X, h: Adm(x), p: q(x) = b, e_{Adm}^{-1}(\langle b, \langle x, h, p \rangle \rangle) = \langle x, h \rangle}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/CanonicalAdmissibleFiberDecomposition.canonical_admissible_fiber_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary readout q and admissibility predicate Adm, the public statement exposes both dependent-sum equivalences and their forward and inverse computation rules.

The ordinary equivalence is the frozen family source of truth. The second equivalence sends an admissible state to its readout, its state, its admissibility evidence, and the reflexive fiber witness.

Each equivalence is unique among equivalences satisfying those computation rules. No surjectivity, section, quotient, or choice is assumed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/CanonicalAdmissibleFiberDecomposition.AdmissibleConceptFiber`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/CanonicalAdmissibleFiberDecomposition.canonical_admissible_fiber_decomposition`
- Dependency: [D5/S3/ConceptDynamics/Fibers/CanonicalDependentFiberEquivalence](CanonicalDependentFiberEquivalence.md)
