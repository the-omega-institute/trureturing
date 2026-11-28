# Shitov's exact word length in size three

## Abstract

Seven is the least universal exact word length for eventually full complex matrix spans in size three.

**Definition 1.1 (Exact word span).**

$$\forall S \in \operatorname{Set}\left(M_{3}(\mathbb{C})\right),\; \forall k \in \mathbb{N},\; \operatorname{exactWordSpan}\left(S, k\right) = \operatorname{span}_{\mathbb{C}}(\{ \prod_{i \in \operatorname{Fin}\left(k\right)} f(i) \mid f : \operatorname{Fin}\left(k\right) \to S \})$$

*Formalization.* `D5/S3/Quantum/Matrix/WordSpans/ShitovSizeThree.exactWordSpan` (`✓ std3`).

*Citation.* Yaroslav Shitov (2023). *Growth in Matrix Algebras and a Conjecture of Pérez-García, Verstraete, Wolf and Cirac*. DOI: [10.1007/s00023-026-01728-6](https://doi.org/10.1007/s00023-026-01728-6). URL: <https://vixra.org/pdf/2308.0028v1.pdf>.

*Commentary.*

In Remark 1, the product uses precisely k factors. The index runs in increasing order, with one independently chosen member of S at each position. The empty product is the identity. Fullness in Question 2 is tested at positive lengths.

**Theorem 1.2 (Least universal length).**

$$\operatorname{IsLeast}\left(\{ k \in \mathbb{N} \mid 0 < k \land \left(\forall S \in \operatorname{Set}\left(M_{3}(\mathbb{C})\right),\; \left(\exists m \in \mathbb{N},\; 0 < m \land \operatorname{exactWordSpan}\left(S, m\right) = M_{3}(\mathbb{C})\right) \Rightarrow \operatorname{exactWordSpan}\left(S, k\right) = M_{3}(\mathbb{C})\right) \}, 7\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/WordSpans/ShitovSizeThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/shitov-2023-size-three-exact-word-length` (proved) by `D5/S3/Quantum/Matrix/WordSpans/ShitovSizeThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"shitov-2023-size-three-exact-word-length","declaration_gid":"D5/S3/Quantum/Matrix/WordSpans/ShitovSizeThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yaroslav Shitov (2023). *Growth in Matrix Algebras and a Conjecture of Pérez-García, Verstraete, Wolf and Cirac*. DOI: [10.1007/s00023-026-01728-6](https://doi.org/10.1007/s00023-026-01728-6). URL: <https://vixra.org/pdf/2308.0028v1.pdf>.

*Acknowledgement.* Yi Yu (2026). *A Better Lower Bound for the Quantum Wielandt Inequality*. DOI: [10.5281/zenodo.24562446](https://doi.org/10.5281/zenodo.24562446). URL: <https://zenodo.org/records/24562446/files/wielandt_lower_bound.pdf>.

*Commentary.*

Shitov's Question 2 asks for the universal index. Here S ranges over every subset of the complex three-by-three matrix algebra. If the span is full at any positive exact length m, it is full at length seven. Seven is the least positive length with this property.

The span of the exact words is the corresponding power of the generator subspace. Fullness at positive length persists. An invertible element in degree s enforces strict dimension growth in steps of s until fullness. For an invertible generator the rank-one return analysis gives enough growth, with the scalar-cube case excluded by its cyclic orbit lines. For a singular generator space the alternating normal form gives a full square, and the compression normal form gives a unit in degree two and at least seven dimensions in degree three.

The lower witness is Yi Yu's published pair in Theorem 1.2, specialized to size three. A linear functional vanishes on every six-letter word, and nine seven-letter words form a basis. By persistence, a universal positive length below seven would make the sixth span full for Yu's pair.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/WordSpans/ShitovSizeThree.exactWordSpan`
- Truth anchor: `D5/S3/Quantum/Matrix/WordSpans/ShitovSizeThree.result`
