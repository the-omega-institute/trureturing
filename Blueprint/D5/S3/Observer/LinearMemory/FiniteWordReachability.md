# Finite word reachability

## Abstract

Ordered endomorphism words reach the whole reachable seed span by its rank gap.

Let K be a division ring, E a left K-module with an additive commutative group, I any alphabet, A an I-indexed family of K-linear endomorphisms, and U a seed submodule. The three type universes are independent. The alphabet may be empty or infinite. For a list w, its action is the product of the list mapped through A. Multiplication of endomorphisms is composition: the head acts after the tail, and the empty word acts as identity.

**Definition 1.1 (Words through a finite horizon).**

$$\forall K, E, I: Type, [\operatorname{DivisionRing}(K)] [\operatorname{AddCommGroup}(E)] [\operatorname{Module}(K, E)] \forall A: I \to \operatorname{End}(K, E), U: \operatorname{Submodule}(K, E), \forall n: N, \operatorname{boundedSpan}(A, U, n) = \operatorname{span}(K, \{x \mid \exists w: \operatorname{List}(I), \operatorname{length}(w) \leq n \land \exists z \in U, x = \operatorname{apply}(\operatorname{prod}(\operatorname{map}(A, w)), z)\})$$

*Formalization.* `D5/S3/Observer/LinearMemory/FiniteWordReachability.boundedSpan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The length condition includes every shorter word and the empty word. The span permits arbitrary finite linear combinations of word images from U.

**Definition 1.2 (All finite words).**

$$\forall K, E, I: Type, [\operatorname{DivisionRing}(K)] [\operatorname{AddCommGroup}(E)] [\operatorname{Module}(K, E)] \forall A: I \to \operatorname{End}(K, E), U: \operatorname{Submodule}(K, E), \operatorname{reachableSpan}(A, U) = \operatorname{span}(K, \{x \mid \exists w: \operatorname{List}(I), \exists z \in U, x = \operatorname{apply}(\operatorname{prod}(\operatorname{map}(A, w)), z)\})$$

*Formalization.* `D5/S3/Observer/LinearMemory/FiniteWordReachability.reachableSpan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the smallest submodule containing U and invariant under every A(i). The ordered-word induction in the proof establishes the closure property used below.

**Theorem 1.3 (The reachable rank gap bounds the horizon).**

$$\forall K, E, I: Type, [\operatorname{DivisionRing}(K)] [\operatorname{AddCommGroup}(E)] [\operatorname{Module}(K, E)] [\operatorname{FiniteDimensional}(K, E)] \forall A: I \to \operatorname{End}(K, E), U: \operatorname{Submodule}(K, E), \operatorname{boundedSpan}(A, U, \operatorname{finrank}(K, \operatorname{reachableSpan}(A, U)) - \operatorname{finrank}(K, U)) = \operatorname{reachableSpan}(A, U)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/FiniteWordReachability.bounded_span_eq_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume E is finite dimensional. Write R for the full reachable span and b = dim(R) - dim(U). Then W(b) = R, so every ordered word image of every seed vector lies in W(b). This is stabilization by b; b need not be the first stable index. Neither commutation, positive seed rank, invariance, nor a pre-existing plateau is assumed. The zero seed and zero ambient space are included.

For F(S) = S + sup over i of A(i)S, induction identifies F iterated n times on U with W(n). These iterates increase inside R. The public bounded_monotone_has_equal_step theorem in FiniteSequentialWordCertificate supplies an equal-rank consecutive pair by b. Inclusion and equal finite rank turn that pair into an F-fixed submodule. Ordered-word induction puts every finite word image inside it, identifying it with R. Fixed-point iteration reaches the same space at b. Since R is contained in E, monotonicity also gives W(dim(E) - dim(U)) = R.

The application is the finite-horizon step of section 349.2, Lemma 349.1, equations 349.8 through 349.12 of RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY. Take the scalar field to be the complex numbers and E the coordinate space on Fin(d), with dimension d counting the full persistent carrier. Set A(i) = mulVecLin(K(i)) and U = range(tau), where tau is the positive initial operator. A finite Kraus family defines Phi(X) = sum over i of K(i) X K(i)*; the empty family and zero CP map are allowed. At an interior parameter with strictly positive branch weights, rescaling Kraus operators by their nonzero square-root weights preserves the word-image spans. This theorem supplies the horizon b for that algebraic span.

To infer that the positive sum of Phi iterated k times on tau, for k from zero through b, is faithful on R still requires the matrix-support identities for a Kraus image and for a positive sum, and the restriction-to-support faithfulness theorem. These downstream Lean interfaces remain unproved here; no D5 importer currently supplies this application. If tau is zero, the reachable carrier is zero. Every persistent classical register, retained seed, program counter, clock value, archive and returning environment belongs in the carrier dimension. The algebraic horizon asserts neither a preparation procedure, CP growth, physical resource savings nor literature novelty.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/FiniteWordReachability.boundedSpan`
- Truth anchor: `D5/S3/Observer/LinearMemory/FiniteWordReachability.bounded_span_eq_reachable`
- Truth anchor: `D5/S3/Observer/LinearMemory/FiniteWordReachability.reachableSpan`
- Dependency: [D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate](../../Quantum/PredictionDepth/FiniteSequentialWordCertificate.md)
