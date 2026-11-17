# Dependency emptiness depends on the accepted proofs

## Abstract

Equal provable images with shared proof readouts do not determine dependency emptiness.

A kernel specifies acceptance, finite axiom and reference readouts, a permitted axiom set, negation and model semantics. Proved means that some accepted proof uses only permitted axioms. SourceLaws requires soundness in every model of the permitted axioms, a finite closed acyclic certificate for every proved proposition, and consistency between each proposition and its negation.

**Definition 1.1 (Qualified proofs).**

$$\operatorname{Qualified}\left(k, pi, p\right) \iff \operatorname{accept}\left(k, pi, p\right) = true \land (\forall a \in \operatorname{axioms}\left(k, pi\right), a \in \operatorname{permitted}\left(k\right))$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.Qualified` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Qualification checks the particular proof, including every axiom in its readout. It does not select a unique proof of the conclusion.

**Definition 1.2 (Dependency emptiness).**

$$\operatorname{DependencyEmpty}\left(k, p\right) \iff \forall pi, \operatorname{Qualified}\left(k, pi, p\right) \implies (\operatorname{refs}\left(k, pi\right) \neq \emptyset \lor \operatorname{axioms}\left(k, pi\right) \neq \emptyset)$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.DependencyEmpty` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every qualified proof must have a nonempty reference readout or a nonempty axiom readout. This is a universal property of all qualified proofs, rather than a property of one selected certificate. With no qualified proofs it holds vacuously; the separating proposition below is proved in both kernels.

**Definition 1.3 (The common interface).**

$$\operatorname{SharedData}\left(k1, k2\right) \iff \operatorname{axioms}\left(k1\right) = \operatorname{axioms}\left(k2\right) \land \operatorname{refs}\left(k1\right) = \operatorname{refs}\left(k2\right) \land \operatorname{permitted}\left(k1\right) = \operatorname{permitted}\left(k2\right) \land \operatorname{neg}\left(k1\right) = \operatorname{neg}\left(k2\right) \land \operatorname{models}\left(k1\right) = \operatorname{models}\left(k2\right) \land \operatorname{holds}\left(k1\right) = \operatorname{holds}\left(k2\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.SharedData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both kernels already have the same proposition, proof, axiom and model types. SharedData equates their entire axiom and reference functions, permitted sets, negations, model predicates and evaluation predicates. Only acceptance may differ.

**Definition 1.4 (Determination by the common data and the provable image).**

$$claim \iff (\forall A, Proof, Ax, Model: Type, \forall k1, k2: \operatorname{KernelData}\left(A, Proof, Ax, Model\right), \operatorname{SharedData}\left(k1, k2\right) \implies \operatorname{SourceLaws}\left(k1\right) \implies \operatorname{SourceLaws}\left(k2\right) \implies (\exists M, \operatorname{models}\left(k1, M, \operatorname{permitted}\left(k1\right)\right)) \implies (\forall p, \operatorname{Proved}\left(k1, p\right) \iff \operatorname{Proved}\left(k2, p\right)) \implies \forall p, \operatorname{Proved}\left(k1, p\right) \implies (\operatorname{DependencyEmpty}\left(k1, p\right) \iff \operatorname{DependencyEmpty}\left(k2, p\right)))$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposed principle quantifies over all four carrier types and both kernels. It assumes SharedData, both SourceLaws, an actual model of the common permitted axioms, and equality of the complete provable images. It concludes that every proposition proved in the first kernel has the same dependency-emptiness value in both. Thus the negation concerns determination of this property, and does not negate the existence of a separating pair.

**Definition 1.5 (The common proof alphabet).**

$$ProofSymbol = \{alpha, beta, delta\}$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.ProofSymbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are exactly three proof symbols, with decidable equality. The proposition type is the ordinary implication/falsity Formula syntax, with natural-number variables, syntactic negation and Boolean valuation semantics.

**Definition 1.6 (The first tautology).**

$$Q = (\neg p \implies \neg p)$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here p is variable zero. Disjunction A or B is represented by not A implies B; therefore Q is precisely the implication/falsity encoding of p or not p. The two negated occurrences expand to implication into falsity.

**Definition 1.7 (The second tautology).**

$$P = (p \implies p)$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same variable zero occurs on both sides. P and Q are syntactically distinct formulas, although both evaluate to true under every Boolean valuation.

**Definition 1.8 (The paired acceptance tables).**

$$k1 = \operatorname{kernel}\left(false\right), k2 = \operatorname{kernel}\left(true\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first kernel accepts exactly (alpha,Q) and (beta,P). The second accepts exactly those two pairs and (delta,P). Every other pair is rejected. In both kernels all axiom readouts and the permitted axiom set are empty. The reference readout of beta is {Q}; those of alpha and delta are empty. Models are all Boolean valuations of the variables, every valuation satisfies the permitted axioms, and a formula holds exactly when its Boolean evaluation is true.

**Theorem 1.9 (The common data do not determine dependency emptiness).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both complete provable images are exactly {Q,P}. The qualified proofs over P are exactly {beta} in the first kernel and {beta,delta} in the second. These different fibers have the same conclusion image. The first fiber contains only a proof referencing Q, whereas the second also contains delta with both readouts empty. Hence P is dependency empty in the first kernel and is not dependency empty in the second. These are statements about every qualified proof, not only about the witnesses chosen for the following certificates. For each kernel the singleton {Q}, with proof alpha, is a certificate for Q. The set {Q,P}, selecting alpha at Q and beta at P, is a certificate for P. Both selections are accepted, have permitted axiom readouts, and contain all their references. The singleton has no edge; the two-point certificate has only the edge from Q to P. Assign Q rank zero and P rank one. The reused strict dependency-coordinate theorem proves acyclicity of these actual selected edges. These certificates establish certificate completeness for every proved formula. Universal truth of P and Q establishes soundness. At the all-false valuation, no formula and its syntactic negation can both be true, which proves consistency. That valuation is also an explicit model, so model semantics is nonempty. Applying the proposed principle to this same pair would transfer dependency emptiness of P from the first kernel to the second, contradicting delta.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.DependencyEmpty`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.P`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.ProofSymbol`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.Q`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.Qualified`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.SharedData`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.claim`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.kernel`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.result`
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/FiniteSupportPatternRealization](FiniteSupportPatternRealization.md)
