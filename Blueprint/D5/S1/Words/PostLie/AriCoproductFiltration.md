# AriCoproductFiltration

## Abstract

The ordinary ari coproduct preserves every right-factor level filtration

N includes zero. Word is FreeMonoid N, H is the finite rational concatenation-word algebra, and all tensor products are ordinary algebraic tensor products over Q. The word basis has coefficient one. Indices k and r, word lengths, and rational coefficients are unrestricted. The coproduct is characterized by the full ordinary pairing of Definition 1.20 and Remark 1.22, including the unit terms omitted from the display in Example 4.28.

**Definition 1.1 (Ordinary tensor basis).**

$$\forall A:Word,\forall B:Word,\operatorname{tensorBasis}\left(\operatorname{pair}\left(A, B\right)\right) = \operatorname{tmulQ}\left(\operatorname{wordBasis}\left(A\right), \operatorname{wordBasis}\left(B\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriCoproductFiltration.tensorBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The basis index is Word times Word. There is no factorial normalization.

**Definition 1.2 (Exact finite original-weight window).**

$$\forall N:N,\operatorname{weightWindow}\left(N\right) = \operatorname{filter}\left(\operatorname{lambda}\left(w, \operatorname{weight}\left(w\right) \leq N\right), \operatorname{image}\left(\operatorname{lambda}\left(l, \operatorname{ofList}\left(\operatorname{map}\left(finVal, l\right)\right)\right), \operatorname{boundedLists}\left(\operatorname{Fin}\left(N + 1\right), N\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriCoproductFiltration.weightWindow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

boundedLists(Fin(N+1),N) is the finite set of lists of length at most N on the finite alphabet Fin(N+1). Mapping values back to natural indices and filtering by original weight gives exactly the desired words. Every letter weight is positive, including gamma(0)=1.

**Theorem 1.3 (Exact window membership).**

$$\forall N:N,\forall w:Word,w \in \operatorname{weightWindow}\left(N\right) \iff \operatorname{weight}\left(w\right) \leq N$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriCoproductFiltration.mem_weightWindow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

A word of weight at most N has length at most N and every index at most N. Conversely the weight filter imposes the exact bound.

**Definition 1.4 (Finite transpose on an original basis word).**

$$\forall w:Word,\operatorname{deltaWord}\left(w\right) = \operatorname{sum}\left(\operatorname{product}\left(\operatorname{weightWindow}\left(\operatorname{weight}\left(w\right)\right), \operatorname{weightWindow}\left(\operatorname{weight}\left(w\right)\right)\right), \operatorname{lambda}\left(ab, \operatorname{smulQ}\left(\operatorname{coeff}\left(\operatorname{starWord}\left(\operatorname{fst}\left(ab\right), \operatorname{snd}\left(ab\right)\right), w\right), \operatorname{tensorBasis}\left(\operatorname{pair}\left(\operatorname{fst}\left(ab\right), \operatorname{snd}\left(ab\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriCoproductFiltration.deltaWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

This is tensorBasis.repr.symm applied to the finitely supported function with value [w](A starWord B). Homogeneity proves that nonzero coordinates lie inside the displayed product window; no outside pair is discarded.

**Definition 1.5 (Ordinary bilinear word pairing).**

$$\forall P:H,\forall Q:H,\operatorname{pairing}\left(P, Q\right) = \operatorname{sum}\left(\operatorname{support}\left(P\right), \operatorname{lambda}\left(w, \operatorname{coeff}\left(P, w\right) \cdot \operatorname{coeff}\left(Q, w\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriCoproductFiltration.pairing` (`✓ std3`).

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Both polynomials have finite support. This is the bilinear extension of the ordinary Kronecker pairing on words, including the empty word.

**Theorem 1.6 (Pairing with a basis word extracts its coefficient).**

$$\forall w:Word,\forall P:H,\operatorname{pairing}\left(\operatorname{wordBasis}\left(w\right), P\right) = \operatorname{coeff}\left(P, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriCoproductFiltration.pairing_basis` (`✓ std3`). ∎

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The polynomial P is arbitrary and the basis word may be empty. Coefficients have the ordinary coefficient-one normalization.

**Definition 1.7 (Ordinary bilinear tensor pairing).**

$$\forall Q:H,\forall R:H,\forall U:H,\forall V:H,\operatorname{tensorPairing}\left(Q, R, \operatorname{tmulQ}\left(U, V\right)\right) = \operatorname{pairing}\left(Q, U\right) \cdot \operatorname{pairing}\left(R, V\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriCoproductFiltration.tensorPairing` (`✓ std3`).

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

tensorPairing is bilinear in Q and R and Q-linear in its tensor argument. It is TensorProduct.lift of the product of the ordinary pairing functionals, so the displayed simple-tensor identity specifies the actual algebraic tensor pairing.

**Definition 1.8 (Original full transpose characterization).**

$$\forall D:LinearMapQHTensorHH,\operatorname{transposeProperty}\left(D\right) \iff \forall P:H,\forall Q:H,\forall R:H,\operatorname{tensorPairing}\left(Q, R, \operatorname{apply}\left(D, P\right)\right) = \operatorname{pairing}\left(\operatorname{star}\left(Q, R\right), P\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriCoproductFiltration.transposeProperty` (`✓ std3`).

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

LinearMapQHTensorHH denotes Q-linear maps H to H tensor H. The product is paired on the left, as in Definition 1.20. Equality is required for every triple of finite rational polynomials, with the ordinary tensor pairing and the original primitive-unshuffle product.

**Definition 1.9 (The unique original ordinary ari coproduct).**

$$(\operatorname{transposeProperty}\left(delta\right)) \land (\forall D:LinearMapQHTensorHH,(\operatorname{transposeProperty}\left(D\right)) \implies D = delta)$$

*Formalization.* `D5/S1/Words/PostLie/AriCoproductFiltration.delta` (`✓ std3`).

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

delta is chosen from a proved unique-existence theorem for transposeProperty. Existence is constructed by the linear extension of deltaWord. Uniqueness follows by the ordinary tensor basis coefficients. This identifies the finite construction with Definition 1.20; it introduces no assumed comparison map or completed tensor product.

**Theorem 1.10 (The full original ordinary transpose identity).**

$$\forall P:H,\forall Q:H,\forall R:H,\operatorname{tensorPairing}\left(Q, R, \operatorname{delta}\left(P\right)\right) = \operatorname{pairing}\left(P, \operatorname{star}\left(Q, R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriCoproductFiltration.delta_transpose` (`✓ std3`). ∎

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

All three polynomials are arbitrary, including zero and the unit. The ordinary word pairing is symmetric; its proved symmetry converts Definition 1.20 to the displayed coefficient convention with the actual finite original product.

**Theorem 1.11 (Full ordinary transpose identity).**

$$\forall P:H,\forall A:Word,\forall B:Word,\operatorname{apply}\left(\operatorname{repr}\left(tensorBasis, \operatorname{delta}\left(P\right)\right), \operatorname{pair}\left(A, B\right)\right) = \operatorname{pairing}\left(P, \operatorname{star}\left(\operatorname{wordBasis}\left(A\right), \operatorname{wordBasis}\left(B\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriCoproductFiltration.delta_coefficient` (`✓ std3`). ∎

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The identity holds for arbitrary rational input and all basis pairs. Bilinearity extends the identity to arbitrary polynomials in each paired factor.

**Theorem 1.12 (All basis coefficients including outside the window).**

$$\forall w:Word,\forall A:Word,\forall B:Word,\operatorname{apply}\left(\operatorname{repr}\left(tensorBasis, \operatorname{delta}\left(\operatorname{wordBasis}\left(w\right)\right)\right), \operatorname{pair}\left(A, B\right)\right) = \operatorname{coeff}\left(\operatorname{starWord}\left(A, B\right), w\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriCoproductFiltration.delta_basis_coefficient` (`✓ std3`). ∎

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

Either A or B may be empty, and neither is assumed to belong to the defining finite window. Outside-window coefficients vanish by original-weight homogeneity.

**Definition 1.13 (Original rational level filtration).**

$$\forall k:N,\forall r:N,\operatorname{filtration}\left(k, r\right) = \operatorname{spanQ}\left(\operatorname{image}\left(wordBasis, \operatorname{set}\left(w, \operatorname{level}\left(k, w\right) \leq r\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriCoproductFiltration.filtration` (`✓ std3`).

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The set variable w ranges over all original words. This is the rational span of the words with at most r letters different from k, with no restriction on their weight or length.

**Definition 1.14 (The actual tensor-submodule image).**

$$\forall k:N,\forall r:N,\operatorname{rightFiltrationImage}\left(k, r\right) = \operatorname{range}\left(\operatorname{tensorMap}\left(idH, \operatorname{subtype}\left(\operatorname{filtration}\left(k, r\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriCoproductFiltration.rightFiltrationImage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

idH is the identity Q-linear map on H, and subtype is the natural inclusion of filtration(k,r) into H. The domain of the tensor map is H tensor filtration(k,r), and its range is a submodule of H tensor H.

**Definition 1.15 (Complete original Conjecture 4.29).**

$$claim \iff \forall k:N,\forall r:N,\forall P:H,(P \in \operatorname{filtration}\left(k, r\right)) \implies \operatorname{delta}\left(P\right) \in \operatorname{rightFiltrationImage}\left(k, r\right)$$

*Formalization.* `D5/S1/Words/PostLie/AriCoproductFiltration.claim` (`✓ std3`).

*Citation.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

For every natural k and r and every finite rational word polynomial P in the original level span, the original ordinary ari coproduct lies in the image of H tensor that same right-factor span. The case k=0, the unit, arbitrary lengths, rational coefficients and cancellation are all included.

**Theorem 1.16 (The full right-factor filtration assertion).**

$$\forall k:N,\forall r:N,\forall P:H,(P \in \operatorname{filtration}\left(k, r\right)) \implies \operatorname{delta}\left(P\right) \in \operatorname{rightFiltrationImage}\left(k, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/PostLie/AriCoproductFiltration.result` (`✓ std3`). ∎

*Resolves.* `Problems/burmester-kuhn-2025-conjecture-4-29-ari-coproduct-filtration` (proved) by `D5/S1/Words/PostLie/AriCoproductFiltration.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"burmester-kuhn-2025-conjecture-4-29-ari-coproduct-filtration","declaration_gid":"D5/S1/Words/PostLie/AriCoproductFiltration.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Annika Burmester; Ulf Kühn (2025). *On post-Lie structures for free Lie algebras*. DOI: [10.48550/arXiv.2504.19661](https://doi.org/10.48550/arXiv.2504.19661). URL: <https://arxiv.org/html/2504.19661v1>.

*Commentary.*

The product support bound forces every nonzero transpose coefficient at (A,B) to have level(k,B) at most level(k,w). Each allowed tensor basis vector is the image of wordBasis(A) tensor an actual element of the filtration submodule. Basis spans and Q-linearity give the assertion for every P in the filtration.

## References

- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.claim`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.delta`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.deltaWord`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.delta_basis_coefficient`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.delta_coefficient`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.delta_transpose`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.filtration`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.mem_weightWindow`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.pairing`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.pairing_basis`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.result`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.rightFiltrationImage`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.tensorBasis`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.tensorPairing`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.transposeProperty`
- Truth anchor: `D5/S1/Words/PostLie/AriCoproductFiltration.weightWindow`
- Dependency: [D5/S1/Words/PostLie/AriWordProduct](AriWordProduct.md)
