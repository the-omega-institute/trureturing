# AriWordProduct

## Abstract

Ordered primitive unshuffle and rational ari product

N includes zero. H is the rational concatenation-word algebra and Word its ordinary basis index type. Functions to Fin(n) assign each original position to one slot. Tuple words multiply componentwise by concatenation. Every assignment is summed separately; identical resulting tuples are not deduplicated. List products retain their displayed order. For a word, length and get mean the corresponding operations on its original toList. In orderedTerm, j ranges over Fin(length(B)); successor slots have indices j+1.

**Definition 1.1 (Ordered slot subsequences).**

$$\forall n:N,(\forall e:\operatorname{Fin}\left(0\right) \to \operatorname{Fin}\left(n\right),\forall j:\operatorname{Fin}\left(n\right),\operatorname{slot}\left(empty, e, j\right) = 1) \land (\forall a:N,\forall A:\operatorname{List}\left(N\right),\forall f:\operatorname{Fin}\left(\operatorname{length}\left(A\right) + 1\right) \to \operatorname{Fin}\left(n\right),\forall j:\operatorname{Fin}\left(n\right),\operatorname{slot}\left(\operatorname{cons}\left(a, A\right), f, j\right) = \operatorname{ifThenElse}\left(\operatorname{apply}\left(f, 0\right) = j, \operatorname{of}\left(a\right) \cdot \operatorname{slot}\left(A, \operatorname{tail}\left(f\right), j\right), \operatorname{slot}\left(A, \operatorname{tail}\left(f\right), j\right)\right))$$

*Formalization.* `D5/S1/Words/PostLie/AriWordProduct.slot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The empty and successor cases have their own function domains. For f:Fin(length(A))->Fin(n), slot j is the subsequence of A whose positions map to j. The tail of f sends i to f(succ(i)).

**Definition 1.2 (primitiveUnshuffle).**

$$\forall n:N,\operatorname{primitiveUnshuffle}\left(n\right) = \operatorname{FreeMonoidLift}\left(\operatorname{lambda}\left(a, \operatorname{sum}\left(\operatorname{Fin}\left(n\right), \operatorname{lambda}\left(j, \operatorname{single}\left(\operatorname{update}\left(\operatorname{constant}\left(1\right), j, \operatorname{of}\left(a\right)\right), 1\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordProduct.primitiveUnshuffle` (`✓ std3`).

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

This monoid homomorphism is the free-monoid lift of the primitive sum. Its target is MonoidAlgebra Q of the n-tuples of original words; the tuple with a single nonempty slot represents placement in that tensor factor.

**Theorem 1.3 (primitiveUnshuffle_assignments).**

$$\forall n:N,\forall A:\operatorname{List}\left(N\right),\operatorname{primitiveUnshuffle}\left(n, \operatorname{ofList}\left(A\right)\right) = \operatorname{sum}\left(\operatorname{Fin}\left(\operatorname{length}\left(A\right)\right) \to \operatorname{Fin}\left(n\right), \operatorname{lambda}\left(f, \operatorname{single}\left(\operatorname{lambda}\left(j, \operatorname{slot}\left(A, f, j\right)\right), 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordProduct.primitiveUnshuffle_assignments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

This proves the equality of the primitive multiplicative expansion with all ordered position assignments, including empty words and zero slots.

**Definition 1.4 (orderedTerm).**

$$\forall B:Word,\forall S:\operatorname{Fin}\left(\operatorname{length}\left(B\right) + 1\right) \to Word,\operatorname{orderedTerm}\left(B, S\right) = \operatorname{wordBasis}\left(\operatorname{apply}\left(S, 0\right)\right) \cdot \operatorname{listProd}\left(\operatorname{ofFn}\left(\operatorname{lambda}\left(j, \operatorname{letterAction}\left(\operatorname{apply}\left(S, \operatorname{succ}\left(j\right)\right), \operatorname{get}\left(B, j\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordProduct.orderedTerm` (`✓ std3`).

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

S has domain Fin(length(B)+1). Slot zero is concatenated with the list product of the actions of each successor slot on the corresponding original letter of B.

**Definition 1.5 (starWord).**

$$\forall A:Word,\forall B:Word,\operatorname{starWord}\left(A, B\right) = \operatorname{sum}\left(\operatorname{Fin}\left(\operatorname{length}\left(A\right)\right) \to \operatorname{Fin}\left(\operatorname{length}\left(B\right) + 1\right), \operatorname{lambda}\left(f, \operatorname{orderedTerm}\left(B, \operatorname{lambda}\left(j, \operatorname{slot}\left(\operatorname{toList}\left(A\right), f, j\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordProduct.starWord` (`✓ std3`).

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The summation domain is every position assignment, not the set of distinct slot tuples.

**Theorem 1.6 (starWord_unshuffle).**

$$\forall A:Word,\forall B:Word,\operatorname{starWord}\left(A, B\right) = \operatorname{apply}\left(\operatorname{basisConstrQ}\left(\operatorname{MonoidAlgebraBasis}\left(\operatorname{Fin}\left(\operatorname{length}\left(B\right) + 1\right) \to Word\right), \operatorname{orderedTerm}\left(B\right)\right), \operatorname{primitiveUnshuffle}\left(\operatorname{length}\left(B\right) + 1, A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordProduct.starWord_unshuffle` (`✓ std3`). ∎

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The linear extension of orderedTerm is applied to the actual primitive unshuffle. This is the finite source product presentation of Proposition 2.1.

**Definition 1.7 (star).**

$$\forall P:H,\forall Q:H,\operatorname{star}\left(P, Q\right) = \operatorname{sum}\left(\operatorname{support}\left(P\right), \operatorname{lambda}\left(A, \operatorname{sum}\left(\operatorname{support}\left(Q\right), \operatorname{lambda}\left(B, \operatorname{smulQ}\left(\operatorname{coeff}\left(P, A\right) \cdot \operatorname{coeff}\left(Q, B\right), \operatorname{starWord}\left(A, B\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordProduct.star` (`✓ std3`).

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

This is the rational bilinear extension of the ordered primitive-unshuffle construction. The displayed finite-support formula follows from its basis values.

**Theorem 1.8 (star_basis).**

$$\forall A:Word,\forall B:Word,\operatorname{star}\left(\operatorname{wordBasis}\left(A\right), \operatorname{wordBasis}\left(B\right)\right) = \operatorname{starWord}\left(A, B\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordProduct.star_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The bilinear primitive construction has exactly the assignment-defined basis values.

**Theorem 1.9 (starWord_homogeneous).**

$$\forall A:Word,\forall B:Word,\operatorname{starWord}\left(A, B\right) \in \operatorname{homogeneous}\left(\operatorname{weight}\left(A\right) + \operatorname{weight}\left(B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordProduct.starWord_homogeneous` (`✓ std3`). ∎

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Every nonzero supported term has the sum of the two original input weights. The unshuffle slots partition all input positions.

**Theorem 1.10 (starWord_above).**

$$\forall k:N,\forall A:Word,\forall B:Word,\operatorname{starWord}\left(A, B\right) \in \operatorname{above}\left(k, \operatorname{level}\left(k, B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordProduct.starWord_above` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Each non-k letter of B contributes at least one non-k letter in every supported output. Multiplication adds counts; summation and cancellation cannot create smaller-level support.

## References

- Truth anchor: `D5/S1/Words/PostLie/AriWordProduct.orderedTerm`
- Truth anchor: `D5/S1/Words/PostLie/AriWordProduct.primitiveUnshuffle`
- Truth anchor: `D5/S1/Words/PostLie/AriWordProduct.primitiveUnshuffle_assignments`
- Truth anchor: `D5/S1/Words/PostLie/AriWordProduct.slot`
- Truth anchor: `D5/S1/Words/PostLie/AriWordProduct.star`
- Truth anchor: `D5/S1/Words/PostLie/AriWordProduct.starWord`
- Truth anchor: `D5/S1/Words/PostLie/AriWordProduct.starWord_above`
- Truth anchor: `D5/S1/Words/PostLie/AriWordProduct.starWord_homogeneous`
- Truth anchor: `D5/S1/Words/PostLie/AriWordProduct.starWord_unshuffle`
- Truth anchor: `D5/S1/Words/PostLie/AriWordProduct.star_basis`
- Dependency: [D5/S1/Words/PostLie/AriProjection](AriProjection.md)
