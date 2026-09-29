# Counting Words by Their Fixed Points

## Abstract

Fixed-point subsets of one-line permutation words are counted by factorials and derangement numbers.

**Definition 1.1 (Permutation words on a support).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.words`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfCountingCore.words` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The finite set words(s) contains all lists that permute the elements of the finite set s.

**Definition 1.2 (A word on a support).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.Word`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfCountingCore.Word` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Word(s) is the type of elements of the finite set words(s).

**Definition 1.3 (Insert a new singleton block).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.insertWord`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfCountingCore.insertWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Canonical insertion takes a word on s and a fresh value f to a word on s with f inserted.

**Definition 1.4 (Erase one support value).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.eraseWord`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfCountingCore.eraseWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Erasing f from a word on s gives a word on the support s without f.

**Definition 1.5 (A fixed point is a free insertion).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.fixedWordEquiv`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfCountingCore.fixedWordEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

Words on s are equivalent to words on s with a fresh f whose inverse Foata map fixes f.

**Definition 1.6 (Prescribed fixed points).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.ForcedFixed`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfCountingCore.ForcedFixed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

ForcedFixed(s,F) contains words on s whose hat map fixes every value in F.

**Definition 1.7 (Adding a prescribed fixed point).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.forcedInsertEquiv`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfCountingCore.forcedInsertEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For F contained in s and fresh f, fixed-point insertion gives an equivalence between ForcedFixed(s,F) and ForcedFixed(s with f,F with f).

**Theorem 1.8 (Count with prescribed fixed points).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.card_forcedFixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfCountingCore.card_forcedFixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If F is contained in s, the number of words fixing F is the factorial of the cardinality of s minus the cardinality of F.

**Definition 1.9 (Words with no fixed point).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.NoFixed`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfCountingCore.NoFixed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

NoFixed(s) contains words on s whose hat map fixes no value of s.

**Theorem 1.10 (Derangement count).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.card_noFixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfCountingCore.card_noFixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The number of words on s with no hat-fixed value equals the derangement number at the cardinality of s.

**Definition 1.11 (An exact fixed-point set).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.ExactFixed`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfCountingCore.ExactFixed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

ExactFixed(s,F) contains words on s for which a value is hat-fixed exactly when it belongs to F.

**Definition 1.12 (Extending an exact fixed-point set).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.exactInsertEquiv`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfCountingCore.exactInsertEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For a fresh f, insertion gives an equivalence between words with exact fixed set F and words with exact fixed set F with f.

**Theorem 1.13 (Count with an exact fixed-point set).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfCountingCore.card_exactFixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfCountingCore.card_exactFixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If F is contained in s, the number of words with exact hat-fixed set F is the derangement number at the cardinality of s minus the cardinality of F.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.ExactFixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.ForcedFixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.NoFixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.Word`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.card_exactFixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.card_forcedFixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.card_noFixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.eraseWord`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.exactInsertEquiv`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.fixedWordEquiv`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.forcedInsertEquiv`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.insertWord`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfCountingCore.words`
- Dependency: [D5/S3/Combinatorics/ArrowWilfFixedInsertion](ArrowWilfFixedInsertion.md)
