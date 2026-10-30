# AriProjection

## Abstract

Pure-word projection and original ari action support

N includes zero. Word is the free monoid on N and H is the finite rational word algebra. Coefficients use the ordinary concatenation basis. All k and s are unrestricted natural indices, including zero.

**Theorem 1.1 (pureProjection_coeff).**

$$\forall k:N,\forall d:N,\forall p:H,\operatorname{coeff}\left(\operatorname{pureProjection}\left(k, p\right), d\right) = \operatorname{coeff}\left(p, \operatorname{ofList}\left(\operatorname{replicate}\left(d, k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriProjection.pureProjection_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The empty word is included at d=0, with no factorial normalization. Rational coefficients and cancellation are unrestricted.

**Theorem 1.2 (pureProjection_commutator).**

$$\forall k:N,\forall p:H,\forall q:H,\operatorname{pureProjection}\left(k, \operatorname{commutator}\left(p, q\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriProjection.pureProjection_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

An algebra homomorphism to the commutative polynomial algebra kills every ordinary commutator.

**Theorem 1.3 (letterAction_projection).**

$$\forall k:N,\forall A:Word,\forall s:N,(A \ne 1) \implies \operatorname{pureProjection}\left(k, \operatorname{letterAction}\left(A, s\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriProjection.letterAction_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

A nonempty left word produces nested commutators for positive s and zero for s=0. Both project to zero.

**Theorem 1.4 (letterAction_above).**

$$\forall k:N,\forall A:Word,\forall s:N,\operatorname{letterAction}\left(A, s\right) \in \operatorname{above}\left(k, \operatorname{level}\left(k, \operatorname{of}\left(s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriProjection.letterAction_above` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The empty-left-word branch is the generator itself. In every other branch the projection identity excludes all pure words, so s different from k contributes at least one non-k letter.

## References

- Truth anchor: `D5/S1/Words/PostLie/AriProjection.letterAction_above`
- Truth anchor: `D5/S1/Words/PostLie/AriProjection.letterAction_projection`
- Truth anchor: `D5/S1/Words/PostLie/AriProjection.pureProjection_coeff`
- Truth anchor: `D5/S1/Words/PostLie/AriProjection.pureProjection_commutator`
- Dependency: [D5/S1/Words/PostLie/AriWordOperations](AriWordOperations.md)
