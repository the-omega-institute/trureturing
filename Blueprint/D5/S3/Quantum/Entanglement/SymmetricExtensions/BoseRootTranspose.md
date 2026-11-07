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

Product-basis partial transposes compose by symmetric difference for arbitrary matrices and all cuts. The root transpose commutes with each distinct root-leaf partial trace and transposes the first pair factor. Applying the transport twice restores the original matrix and witness, so the leaf sandwich and the ordinary and full-transpose positivity endpoints are retained for every finite register and local-label type.

**Definition 1.2 (pairRootTranspose).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.pairRootTranspose`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.pairRootTranspose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transpose the first member of the actual ordered pair, keeping the second member unchanged.

Root partial transpose is an involutive transport of fully PPT star witnesses for an arbitrary input and its first-factor transpose. The leaf sandwich is retained, and symmetric-difference cuts include the ordinary and full-transpose endpoints with their positive semidefinite witnesses.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.AllCutsPPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose.pairRootTranspose`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension](DickeExtension.md)
