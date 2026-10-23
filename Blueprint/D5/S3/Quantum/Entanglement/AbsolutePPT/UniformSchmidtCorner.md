# UniformSchmidtCorner

## Abstract

An injectively labelled product corner extends to a permutation of the full spectrum and an actual corner unitary extends by the identity. Literal APPT therefore supplies positive semidefiniteness after partial transpose on every selected corner.

An injectively labelled product corner extends to a permutation of the full spectrum and an actual corner unitary extends by the identity. Literal APPT therefore supplies positive semidefiniteness after partial transpose on every selected corner.

Utility none: corner, corner_injective, Outside, outsideFintype, cornerEquiv, cornerEquiv_symm_corner. Symbolic product embeddings, complement types, finiteness and equivalences for all r,m,n; no bounded search or certified input is delivered.

Utility none: conjugate_corner, selected_corner_psd. Universal matrix transport and an implication from literal APPT, with the permutation and unitary constructed for arbitrary dimensions; no checker or numerical-premise reduction is delivered.

**Definition 1.1 (Partial transposition).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.partialTranspose`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.partialTranspose` (`✓ std3`).

*Citation.* T. Pathak (2026). *Mixed-State Entanglement in a Minimal Model of Quantum Chaos*. DOI: [10.48550/arXiv.2603.14292](https://doi.org/10.48550/arXiv.2603.14292). URL: <https://arxiv.org/abs/2603.14292v1>.

*Commentary.*

On arbitrary local types, the entry at ((a,b),(c,d)) equals the input entry at ((a,d),(c,b)). This original delegate is definitionally equal to Bipartite.partialTranspose on the same complex matrix domain.

**Definition 1.2 (Literal absolute PPT).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.APPT`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.APPT` (`✓ std3`).

*Citation.* Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter (2026). *The geometry of absolute separability and other convex matrix properties from spectrum*. DOI: [10.48550/arXiv.2608.03390](https://doi.org/10.48550/arXiv.2608.03390). URL: <https://arxiv.org/abs/2608.03390v2>.

*Commentary.*

For arbitrary finite local types with their original Fintype and DecidableEq instances, every global unitary conjugation has positive semidefinite partial transpose. This original delegate equals Bipartite.APPT, including on empty systems. It adds no trace normalization.

**Definition 1.3 (extendUnitaryAlong).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.extendUnitaryAlong`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.extendUnitaryAlong` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Extend an arbitrary finite unitary by an identity block and transport it through a coordinate equivalence.

**Theorem 1.4 (extendUnitaryAlong diagonal).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.extendUnitaryAlong_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.extendUnitaryAlong_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by the extended unitary acts on the selected diagonal block and preserves the complement.

**Definition 1.5 (permutationU).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.permutationU`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.permutationU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unitary matrix associated with an arbitrary finite permutation.

**Theorem 1.6 (c square).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.c_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.c_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reciprocal square root of two has square one half over the complex numbers; Bell block consumers use this coefficient.

**Theorem 1.7 (c star).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.c_star`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.c_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complex conjugation fixes the real Bell coefficient.

**Theorem 1.8 (appt conjugate).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.appt_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.appt_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal APPT on arbitrary finite product types is preserved by global unitary conjugation.

**Theorem 1.9 (real psd of complex).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.real_psd_of_complex`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.real_psd_of_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity of the complex cast of a finite real matrix implies real positive semidefiniteness.

**Theorem 1.10 (permutation conjugate).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.permutation_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.permutation_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by a permutation unitary equals simultaneous row and column reindexing.

**Definition 1.11 (corner).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def corner {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) (p : Fin r × Fin r) : Fin m × Fin n

**Theorem 1.12 (corner injective).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem corner_injective {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) : Function.Injective (corner hm hn)

**Definition 1.13 (Outside).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.Outside`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.Outside` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

abbrev Outside {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n)

**Definition 1.14 (cornerEquiv).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def cornerEquiv {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) : ((Fin r × Fin r) ⊕ Outside hm hn) ≃ (Fin m × Fin n)

**Theorem 1.15 (cornerEquiv symm corner).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv_symm_corner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv_symm_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

@[simp] theorem cornerEquiv_symm_corner {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) (p : Fin r × Fin r) : (cornerEquiv hm hn).symm (corner hm hn p) = Sum.inl p

**Theorem 1.16 (conjugate corner).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.conjugate_corner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.conjugate_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem conjugate_corner {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) (d : Fin m × Fin n → ℂ) (V : unitaryGroup (Fin r × Fin r) ℂ) : (((extendUnitaryAlong (cornerEquiv hm hn) V : Matrix _ _ ℂ) * diagonal d * (extendUnitaryAlong (cornerEquiv hm hn) V : Matrix _ _ ℂ)ᴴ).submatrix (corner hm hn) (corner hm hn)) = (V : Matrix _ _ ℂ) * diagonal (fun q => d (corner hm hn q)) * (V : Matrix _ _ ℂ)ᴴ

**Theorem 1.17 (selected corner psd).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.selected_corner_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.selected_corner_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem selected_corner_psd {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ) (label : Fin r × Fin r → Fin (m * n)) (hl : Function.Injective label) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) (V : unitaryGroup (Fin r × Fin r) ℂ) : (partialTranspose ((V : Matrix _ _ ℂ) * diagonal (fun q => (l (label q) : ℂ)) * (V : Matrix _ _ ℂ)ᴴ)).PosSemidef

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.APPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.Outside`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.appt_conjugate`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.c_square`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.c_star`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.conjugate_corner`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv_symm_corner`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.extendUnitaryAlong`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.extendUnitaryAlong_diagonal`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.partialTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.permutationU`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.permutation_conjugate`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.real_psd_of_complex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.selected_corner_psd`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite](Bipartite.md)
