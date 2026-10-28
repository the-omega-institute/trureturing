# AriWordOperations

## Abstract

Original rational ari letter actions and word support

H is the existing rational concatenation-word algebra on the whole natural alphabet. N denotes the naturals, including zero. All sums are finite, the empty word is 1, and all coefficients and scalar actions are rational. In supportSpace, p ranges over H and w over Word; the set variables in homogeneous and above range over Word. For a word A, length(A) and get(A,i) mean length and get of A.toList. Sum and prod with a Fin domain run over every coordinate. The source presentation is Proposition 4.19 with individual generator factors; it does not use the naive associative extension of Remark 4.16.

**Definition 1.1 (The original infinite-alphabet words).**

$$Word = \operatorname{FreeMonoid}\left(N\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.Word` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The empty word is the multiplicative unit, and multiplication is concatenation.

**Definition 1.2 (The existing rational word algebra).**

$$H = \operatorname{RationalWordPolynomial}\left(N\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Coefficients are rational and every polynomial has finite word support.

**Definition 1.3 (Ordinary word basis).**

$$\forall w:Word,\operatorname{wordBasis}\left(w\right) = \operatorname{single}\left(w, 1\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.wordBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The basis has coefficient one, with no divided powers or factorials.

**Definition 1.4 (Original generators including zero).**

$$\forall s:N,\operatorname{letter}\left(s\right) = \operatorname{wordBasis}\left(\operatorname{of}\left(s\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.letter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Every natural index is allowed.

**Definition 1.5 (Original letter weight).**

$$\forall s:N,\operatorname{gamma}\left(s\right) = \operatorname{ifThenElse}\left(s = 0, 1, s\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The zero-index letter has weight one.

**Definition 1.6 (Additive original weight).**

$$\forall w:Word,\operatorname{weight}\left(w\right) = \operatorname{sum}\left(\operatorname{map}\left(gamma, \operatorname{toList}\left(w\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.weight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The sum over an empty list is zero.

**Definition 1.7 (The full k-level count).**

$$\forall k:N,\forall w:Word,\operatorname{level}\left(k, w\right) = \operatorname{countP}\left(\operatorname{lambda}\left(i, i \ne k\right), \operatorname{toList}\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.level` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

This counts letters different from k, including k equal to zero.

**Definition 1.8 (Coordinate support submodule).**

$$\forall S:\operatorname{Set}\left(Word\right),\operatorname{supportSpace}\left(S\right) = \operatorname{set}\left(p, \forall w:Word,(\operatorname{coeff}\left(p, w\right) \ne 0) \implies w \in S\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.supportSpace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Finite sums and rational cancellation preserve this support restriction.

**Definition 1.9 (Homogeneous support submodule).**

$$\forall n:N,\operatorname{homogeneous}\left(n\right) = \operatorname{supportSpace}\left(\operatorname{set}\left(w, \operatorname{weight}\left(w\right) = n\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.homogeneous` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The zero polynomial belongs to every degree.

**Definition 1.10 (Lower level support submodule).**

$$\forall k:N,\forall n:N,\operatorname{above}\left(k, n\right) = \operatorname{supportSpace}\left(\operatorname{set}\left(w, n \leq \operatorname{level}\left(k, w\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.above` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Every supported word has level at least n.

**Definition 1.11 (Extended source binomial).**

$$\forall a:N,\forall l:N,(\operatorname{beta}\left(0, 0\right) = 1) \land ((\operatorname{beta}\left(0, l + 1\right) = 0) \land ((\operatorname{beta}\left(a + 1, 0\right) = 0) \land (\operatorname{beta}\left(a + 1, l + 1\right) = \operatorname{choose}\left(a, l\right))))$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.beta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Mixed zero pairs vanish. Positive-positive indices use the ordinary binomial coefficient.

**Definition 1.12 (All bounded index tuples).**

$$\forall A:Word,\operatorname{lowerIndices}\left(A\right) = \operatorname{piFinset}\left(\operatorname{lambda}\left(i, \operatorname{range}\left(\operatorname{get}\left(A, i\right) + 1\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.lowerIndices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The tuple domain is Fin(length(A)); piFinset enumerates every bounded function once.

**Definition 1.13 (Signed original multiplicity).**

$$\forall A:Word,\forall l:\operatorname{Fin}\left(\operatorname{length}\left(A\right)\right) \to N,\operatorname{multiplicity}\left(A, l\right) = (-1)^{\operatorname{sum}\left(\operatorname{Fin}\left(\operatorname{length}\left(A\right)\right), \operatorname{lambda}\left(i, \operatorname{get}\left(A, i\right)\right)\right) + \operatorname{sum}\left(\operatorname{Fin}\left(\operatorname{length}\left(A\right)\right), \operatorname{lambda}\left(i, \operatorname{apply}\left(l, i\right)\right)\right)} \cdot \operatorname{prod}\left(\operatorname{Fin}\left(\operatorname{length}\left(A\right)\right), \operatorname{lambda}\left(i, \operatorname{castQ}\left(\operatorname{beta}\left(\operatorname{get}\left(A, i\right), \operatorname{apply}\left(l, i\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.multiplicity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

For each l:Fin(length(A))->N, the sign exponent is the sum of the original and lower indices, and the beta factors are cast to Q.

**Definition 1.14 (Ordinary rational commutator).**

$$\forall p:H,\forall q:H,\operatorname{commutator}\left(p, q\right) = p \cdot q - q \cdot p$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.commutator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Both products are original concatenation products.

**Definition 1.15 (Left-nested ordinary brackets).**

$$\forall p:H,\forall l:N,\forall ls:\operatorname{List}\left(N\right),(\operatorname{nestedBracket}\left(p, empty\right) = p) \land (\operatorname{nestedBracket}\left(p, \operatorname{cons}\left(l, ls\right)\right) = \operatorname{nestedBracket}\left(\operatorname{commutator}\left(p, \operatorname{letter}\left(l\right)\right), ls\right))$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.nestedBracket` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The first list entry brackets the initial polynomial first, and the following entries continue on the left-nested result.

**Definition 1.16 (Finite original generator action).**

$$\forall A:Word,\forall s:N,\operatorname{letterAction}\left(A, s\right) = \operatorname{ifThenElse}\left(A = 1, \operatorname{letter}\left(s\right), \operatorname{ifThenElse}\left(s = 0, 0, \operatorname{sum}\left(\operatorname{lowerIndices}\left(A\right), \operatorname{lambda}\left(l, \operatorname{smulQ}\left(\operatorname{multiplicity}\left(A, l\right), \operatorname{nestedBracket}\left(\operatorname{letter}\left(s + \operatorname{sum}\left(\operatorname{Fin}\left(\operatorname{length}\left(A\right)\right), \operatorname{lambda}\left(i, \operatorname{get}\left(A, i\right) - \operatorname{apply}\left(l, i\right)\right)\right)\right), \operatorname{ofFn}\left(l\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.letterAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

This is the nested-bracket equality in the proof of Proposition 4.19, obtained from Lemma 4.10 and Definitions 4.8 and 1.9. It is the original enveloping action. The empty tuple has multiplicity one.

**Definition 1.17 (The concatenation algebra projection).**

$$\forall k:N,\forall s:N,\operatorname{pureProjection}\left(k, \operatorname{letter}\left(s\right)\right) = \operatorname{ifThenElse}\left(s = k, X, 0\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriWordOperations.pureProjection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

This is the Q-algebra homomorphism to Polynomial Q induced by the specified images of every generator, and sends the unit to one.

**Theorem 1.18 (weight one).**

$$\operatorname{weight}\left(1\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordOperations.weight_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The empty word has weight zero.

**Theorem 1.19 (weight mul).**

$$\forall u:Word,\forall v:Word,\operatorname{weight}\left(u \cdot v\right) = \operatorname{weight}\left(u\right) + \operatorname{weight}\left(v\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordOperations.weight_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Concatenation adds weights.

**Theorem 1.20 (weight of).**

$$\forall s:N,\operatorname{weight}\left(\operatorname{of}\left(s\right)\right) = \operatorname{gamma}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordOperations.weight_of` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

A generator has its original weight.

**Theorem 1.21 (level one).**

$$\forall k:N,\operatorname{level}\left(k, 1\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordOperations.level_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The empty word has level zero for every k.

**Theorem 1.22 (level mul).**

$$\forall k:N,\forall u:Word,\forall v:Word,\operatorname{level}\left(k, u \cdot v\right) = \operatorname{level}\left(k, u\right) + \operatorname{level}\left(k, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordOperations.level_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Concatenation adds levels.

**Theorem 1.23 (level of).**

$$\forall k:N,\forall s:N,\operatorname{level}\left(k, \operatorname{of}\left(s\right)\right) = \operatorname{ifThenElse}\left(s = k, 0, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordOperations.level_of` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

This includes the zero-index generator.

**Theorem 1.24 (homogeneous basis).**

$$\forall w:Word,\operatorname{wordBasis}\left(w\right) \in \operatorname{homogeneous}\left(\operatorname{weight}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordOperations.homogeneous_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

A basis monomial is homogeneous.

**Theorem 1.25 (above basis).**

$$\forall k:N,\forall w:Word,\operatorname{wordBasis}\left(w\right) \in \operatorname{above}\left(k, \operatorname{level}\left(k, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordOperations.above_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

A basis monomial has its exact level.

**Theorem 1.26 (homogeneous mul).**

$$\forall p:H,\forall q:H,\forall a:N,\forall b:N,((p \in \operatorname{homogeneous}\left(a\right)) \land (q \in \operatorname{homogeneous}\left(b\right))) \implies p \cdot q \in \operatorname{homogeneous}\left(a + b\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordOperations.homogeneous_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Homogeneous supports multiply in the sum degree.

**Theorem 1.27 (above mul).**

$$\forall k:N,\forall p:H,\forall q:H,\forall a:N,\forall b:N,((p \in \operatorname{above}\left(k, a\right)) \land (q \in \operatorname{above}\left(k, b\right))) \implies p \cdot q \in \operatorname{above}\left(k, a + b\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordOperations.above_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Lower level bounds add under concatenation.

**Theorem 1.28 (letterAction homogeneous).**

$$\forall A:Word,\forall s:N,\operatorname{letterAction}\left(A, s\right) \in \operatorname{homogeneous}\left(\operatorname{weight}\left(A\right) + \operatorname{gamma}\left(s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriWordOperations.letterAction_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Nonzero beta factors preserve zero positions; the shifted index is positive in the nonzero branch, so the total original weight is preserved.

## References

- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.H`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.Word`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.above`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.above_basis`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.above_mul`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.beta`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.commutator`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.gamma`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.homogeneous`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.homogeneous_basis`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.homogeneous_mul`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.letter`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.letterAction`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.letterAction_homogeneous`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.level`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.level_mul`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.level_of`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.level_one`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.lowerIndices`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.multiplicity`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.nestedBracket`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.pureProjection`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.supportSpace`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.weight`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.weight_mul`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.weight_of`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.weight_one`
- Truth anchor: `D5/S1/Words/PostLie/AriWordOperations.wordBasis`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra](../Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra.md)
