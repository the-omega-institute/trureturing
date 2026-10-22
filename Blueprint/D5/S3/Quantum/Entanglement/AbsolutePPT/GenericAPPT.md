# Generic APPT transport

## Abstract

Unitary transport and positivity over arbitrary finite product systems.

These existing consumed helpers retain their full Lean names. Bipartite supplies the shared partial transpose and literal all-unitary APPT predicate. The qutrit and arbitrary-dimension Schmidt proofs share the same transport declarations. No fixed dimension, density normalization, or restricted unitary family is added. The relocation supplies no new theorem or escape-audit validation; unfinished audit evidence is tracked in issue #19818.

**Definition 1.1 (Partial transposition).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.partialTranspose`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.partialTranspose` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

On arbitrary local types, the entry at ((a,b),(c,d)) equals the input entry at ((a,d),(c,b)). This original delegate is definitionally equal to Bipartite.partialTranspose on the same complex matrix domain.

**Definition 1.2 (Literal absolute PPT).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.APPT`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.APPT` (`✓ std3`).

*Citation.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Commentary.*

For arbitrary finite local types with their original Fintype and DecidableEq instances, every global unitary conjugation has positive semidefinite partial transpose. This original delegate equals Bipartite.APPT, including on empty systems. It adds no trace normalization.

**Definition 1.3 (extendUnitaryAlong).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.extendUnitaryAlong`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.extendUnitaryAlong` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Extend an arbitrary finite unitary by an identity block and transport it through a coordinate equivalence.

**Theorem 1.4 (extendUnitaryAlong diagonal).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.extendUnitaryAlong_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.extendUnitaryAlong_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by the extended unitary acts on the selected diagonal block and preserves the complement.

**Definition 1.5 (permutationU).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.permutationU`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.permutationU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unitary matrix associated with an arbitrary finite permutation.

**Theorem 1.6 (c square).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.c_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.c_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reciprocal square root of two has square one half over the complex numbers; Bell block consumers use this coefficient.

**Theorem 1.7 (c star).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.c_star`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.c_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complex conjugation fixes the real Bell coefficient.

**Theorem 1.8 (appt conjugate).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.appt_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.appt_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal APPT on arbitrary finite product types is preserved by global unitary conjugation.

**Theorem 1.9 (real psd of complex).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.real_psd_of_complex`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.real_psd_of_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity of the complex cast of a finite real matrix implies real positive semidefiniteness.

**Theorem 1.10 (permutation conjugate).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.permutation_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.permutation_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by a permutation unitary equals simultaneous row and column reindexing.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.APPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.appt_conjugate`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.c_square`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.c_star`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.extendUnitaryAlong`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.extendUnitaryAlong_diagonal`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.partialTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.permutationU`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.permutation_conjugate`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT.real_psd_of_complex`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite](Bipartite.md)
