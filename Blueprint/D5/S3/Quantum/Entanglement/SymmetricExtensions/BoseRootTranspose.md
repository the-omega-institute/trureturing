# Root partial transpose of actual star witnesses

## Abstract

Root partial transpose of actual star witnesses

Finite register and local-label types use the original product basis. This is the root-transpose transport underlying the CLDUI companion application in Haobo Ma and Wenlin Zhang's note. The GNP cone characterization is proved separately in BoseHierarchy. Full Bose support is not asserted for a companion witness.

**Definition 1.1 (AllCutsPPT).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.AllCutsPPT`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.AllCutsPPT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positivity is required at every subset, including the ordinary empty cut and full transpose. For a positive input this is equivalent to the existing FullyPPT predicate.

**Theorem 1.2 (partialTranspose composition).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.partialTranspose_composition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.partialTranspose_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing product-basis partial transposes replaces the cut by its symmetric difference. The identity holds for arbitrary matrices and all cuts.

**Definition 1.3 (pairRootTranspose).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.pairRootTranspose`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.pairRootTranspose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transpose the first member of the actual ordered pair, keeping the second member unchanged.

**Theorem 1.4 (marginal rootTranspose).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.marginal_rootTranspose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.marginal_rootTranspose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct root and leaf, the actual root partial transpose commutes with the root-leaf partial trace and transposes the first factor of that marginal.

**Theorem 1.5 (star rootTranspose iff).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.star_rootTranspose_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.star_rootTranspose_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Root partial transpose is an involutive bijection of fully PPT star witnesses for an arbitrary input and its first-factor transpose. The leaf sandwich is retained. Symmetric-difference cuts include ordinary and full-transpose endpoints, whose positivity is supplied explicitly.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.AllCutsPPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.marginal_rootTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.pairRootTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.partialTranspose_composition`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.star_rootTranspose_iff`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension](DickeExtension.md)
