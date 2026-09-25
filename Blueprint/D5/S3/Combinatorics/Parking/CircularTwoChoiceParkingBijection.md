# Circular Two-Choice Parking and Classical Parking Functions

## Abstract

Cutting the literal circular process at its observed vacancy gives an explicit fixed-fiber equivalence with classical parking functions, while a separate global equivalence retains all original observables.

**Definition 1.1 (Classical parking functions).**

Lean statement: `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.ClassicalPF`

*Formalization.* `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.ClassicalPF` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

ClassicalPF n is the subtype of natural-number lists with length n satisfying the frozen supplier's literal IsParkingFunction predicate. Preferences and their final spots therefore both lie in the linear street 1 through n.

**Definition 1.2 (Cut and uncut are inverse).**

Lean statement: `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.oneChoiceClassicalEquiv`

*Formalization.* `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.oneChoiceClassicalEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For every natural n and every circular vacancy j, this construction is an explicit equivalence between OneChoiceFiber n j and ClassicalPF n. Forward, each anchor is cut relative to j. The cut_run theorem identifies the complete circular run with the supplier's parkFrom, proving the parking predicate. Reverse, every classical preference is uncut by adding j. The reverse feedback-state induction uses parkStep_spec and firstFree_ne_vacancy to show that its circular run is the uncut classical run and leaves j empty. Pointwise cut-after-uncut and uncut-after-cut identities prove both inverse laws.

**Definition 1.3 (The fixed-increment fixed-vacancy equivalence).**

Lean statement: `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.fixedFiberEquiv`

*Formalization.* `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.fixedFiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For every natural n, every per-car increment matrix, and every vacancy j, this is the composition of fixedFiberOneChoiceEquiv with oneChoiceClassicalEquiv. Its forward map performs orbit normalization and then cuts at j. Its inverse uncuts a classical parking function, reverses the normalization, and reconstructs each literal ordered pair. Both equivalence laws are inherited from those explicit two-sided constructions. This definition remains the explicit map and inverse used by the source-level settlement.

**Theorem 1.4 (Every source-level fixed fiber is bijective).**

Lean statement: `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.result` (`✓ std3`). ∎

*Resolves.* `Problems/circular-two-choice-parking-fixed-fiber-bijection` (proved) by `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"circular-two-choice-parking-fixed-fiber-bijection","declaration_gid":"D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For every n with 1 <= n, every per-car increment matrix with entries in 1 through n, and every vacancy j, fixedFiberEquiv n increments j is bijective. The theorem certifies the exact explicit equivalence above, so its surjectivity and injectivity retain the orbit normalization, vacancy cut and uncut maps, and both proved inverse laws. This is the sole typed settlement of the paper's fixed-increment, fixed-vacancy problem.

**Definition 1.5 (The auxiliary global observable equivalence).**

Lean statement: `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.globalParkingEquiv`

*Formalization.* `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.globalParkingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

For n with hypothesis 1 <= n, every literal actual preference is equivalent to a classical parking function together with its original increment matrix and its actual vacancy. The forward map definitionally projects actualIncrements and actualEmpty. The inverse enters that exact fixed fiber and applies fixedFiberEquiv, so its round trip reconstructs each car's anchor and second choice, not only the encoded increment. Mathlib's sigma-fiber and product equivalences assemble the fibers; they do not replace the orbit and cut/uncut construction. This global interface is auxiliary and is not a second ownership claim for the source problem.

## References

- Truth anchor: `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.ClassicalPF`
- Truth anchor: `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.fixedFiberEquiv`
- Truth anchor: `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.globalParkingEquiv`
- Truth anchor: `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.oneChoiceClassicalEquiv`
- Truth anchor: `D5/S3/Combinatorics/Parking/CircularTwoChoiceParkingBijection.result`
- Dependency: [D5/S3/Combinatorics/Parking/CutRunCorrespondence](CutRunCorrespondence.md)
- Dependency: [D5/S3/Combinatorics/Parking/FixedIncrementFiberTransport](FixedIncrementFiberTransport.md)
