# Native Descendant Contravariance

## Abstract

Adjoints of all native lattice descendants and finite mixed states

Let D be an arbitrary symmetric even integral lattice, let G be its complex Gram matrix, and let H satisfy both HG=1 and GH=1. The state space is the original finite-support charge space with unrestricted polynomial oscillators. Neither positivity nor a finite-dimensional energy fiber is required. All tested states, all charges and every integer field mode are included.

For a state a of integer grade w, the opposite coefficient is (-1)^w times the finite sum of (j!)^-1 Y(L1^j a)[2w-n-j-2]. Here L1 is the actual matrix-weighted Sugawara mode, and its proved local nilpotence bounds the sum by the actual oscillator support. The opposite coefficients need not be lower-truncated fields.

The proof starts at each charged ground state and inserts a finite word of negative neutral currents. Transposing the original two pointwise finite insertion sums gives precisely the two supported reversed sums. The second sum retains its zero-current term. Native basis expansion extends the word calculation to every homogeneous state. Coefficient conjugation together with charge and oscillator reflection gives the antilinear PCT map; complex-linear reflection alone does not give Hermitian contravariance.

These are classical lattice vertex-algebra contravariance identities in the context of Frenkel, Huang and Lepowsky, On axiomatic approaches to vertex operator algebras and modules, and Frenkel, Lepowsky and Meurman, Vertex Operator Algebras and the Monster. No claim of literature novelty is made. Matter contravariance does not establish ghost or BRST adjoints, physical positivity, no-ghost, a Monster realization, string theory or AdS/CFT.

**Theorem 1.1 (PCT preserves every integer grade).**

Lean statement: `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.pct_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.pct_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Antilinear coefficient conjugation and charge reflection preserve each actual grade, without an inverse matrix or positivity assumption.

**Theorem 1.2 (BPZ adjoints of all homogeneous descendants).**

Lean statement: `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.bpz_stateField_homogeneous`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.bpz_stateField_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original bilinear BPZ form transposes Y(a)[n] to the actual opposite coefficient at a's integer grade. Both inverse Gram equations are retained.

**Theorem 1.3 (Hermitian adjoints of all homogeneous descendants).**

Lean statement: `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.hermitian_stateField_homogeneous`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.hermitian_stateField_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original Hermitian form transposes Y(a)[n] to the actual opposite coefficient evaluated on the antilinear PCT transform of a. Arbitrary complex coefficients are conjugated.

**Theorem 1.4 (Finite mixed-state BPZ formula).**

Lean statement: `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.bpz_stateField_all`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.bpz_stateField_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each native grade projection has its own opposite weight. The sum runs over the state's actual finite set of energies, never a weight assigned to a genuinely mixed state.

**Theorem 1.5 (Finite mixed-state Hermitian formula).**

Lean statement: `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.hermitian_stateField_all`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.hermitian_stateField_all` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original finite energy decomposition is transposed componentwise, with antilinear PCT applied to each actual grade projection.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.bpz_stateField_all`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.bpz_stateField_homogeneous`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.hermitian_stateField_all`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.hermitian_stateField_homogeneous`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeAdjoints/Descendants.pct_grade`
- Dependency: [D5/S3/VertexAlgebra/LatticeOppositeCurrentClosure](../LatticeOppositeCurrentClosure.md)
