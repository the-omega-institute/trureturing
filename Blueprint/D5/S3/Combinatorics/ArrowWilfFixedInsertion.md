# Insertion and Singleton Cycles

## Abstract

Canonical insertion makes a chosen new value a singleton cycle in the inverse Foata map.

**Definition 1.1 (Canonical singleton insertion).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The recursive insertion places a new value f immediately before the first value at least f, or at the end if none exists; it preserves the order of the old entries.

**Theorem 1.2 (Insertion preserves the old word).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert_perm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

The inserted word is a permutation of f followed by the original word.

**Theorem 1.3 (Erasing the inserted point).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.erase_fixedInsert`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfFixedInsertion.erase_fixedInsert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When f is absent from p, erasing f from fixedInsert f p returns p.

**Theorem 1.4 (Commutation of distinct insertions).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert_comm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For distinct new values f and g absent from p, inserting f and g in either order gives the same word.

**Theorem 1.5 (Fixed points are exactly canonical insertions).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert_erase_eq_iff_hat_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert_erase_eq_iff_hat_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For a word with distinct entries containing f, reinserting f after erasure recovers the word exactly when hat fixes f.

**Definition 1.6 (Singleton-block syntax).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.FixedSyntax`

*Formalization.* `D5/S3/Combinatorics/ArrowWilfFixedInsertion.FixedSyntax` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

FixedSyntax f p records the recursive word shape in which f begins a singleton block: entries before f are smaller and the next entry, when present, is larger.

**Theorem 1.7 (Syntax and fixed points).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedSyntax_iff_hat_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedSyntax_iff_hat_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For a word with distinct entries containing f, FixedSyntax f p is equivalent to hat p f equal to f.

**Theorem 1.8 (Other fixed points under insertion).**

Lean statement: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.hat_fixed_fixedInsert_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfFixedInsertion.hat_fixed_fixedInsert_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

If f is freshly inserted, the fixed-point status of any distinct old value g is unchanged.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.FixedSyntax`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.erase_fixedInsert`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert_comm`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert_erase_eq_iff_hat_fixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedInsert_perm`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.fixedSyntax_iff_hat_fixed`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfFixedInsertion.hat_fixed_fixedInsert_iff`
- Dependency: [D5/S3/Combinatorics/ArrowWilfCharacterization](ArrowWilfCharacterization.md)
