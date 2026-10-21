# UniformSchmidtCorner

## Abstract

An injectively labelled product corner extends to a permutation of the full spectrum and an actual corner unitary extends by the identity. Literal APPT therefore supplies positive semidefiniteness after partial transpose on every selected corner. The Schmidt-entry identities allow arbitrary real coefficients.

An injectively labelled product corner extends to a permutation of the full spectrum and an actual corner unitary extends by the identity. Literal APPT therefore supplies positive semidefiniteness after partial transpose on every selected corner. The Schmidt-entry identities allow arbitrary real coefficients.

**Definition 1.1 (corner).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def corner {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) (p : Fin r × Fin r) : Fin m × Fin n

**Theorem 1.2 (corner injective).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem corner_injective {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) : Function.Injective (corner hm hn)

**Definition 1.3 (Outside).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.Outside`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.Outside` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

abbrev Outside {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n)

**Definition 1.4 (cornerEquiv).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def cornerEquiv {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) : ((Fin r × Fin r) ⊕ Outside hm hn) ≃ (Fin m × Fin n)

**Theorem 1.5 (cornerEquiv inl).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv_inl`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv_inl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

@[simp] theorem cornerEquiv_inl {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) (p : Fin r × Fin r) : cornerEquiv hm hn (Sum.inl p) = corner hm hn p

**Theorem 1.6 (cornerEquiv symm corner).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv_symm_corner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv_symm_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

@[simp] theorem cornerEquiv_symm_corner {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) (p : Fin r × Fin r) : (cornerEquiv hm hn).symm (corner hm hn p) = Sum.inl p

**Theorem 1.7 (conjugate corner).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.conjugate_corner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.conjugate_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem conjugate_corner {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) (d : Fin m × Fin n → ℂ) (V : unitaryGroup (Fin r × Fin r) ℂ) : (((extendUnitaryAlong (cornerEquiv hm hn) V : Matrix _ _ ℂ) * diagonal d * (extendUnitaryAlong (cornerEquiv hm hn) V : Matrix _ _ ℂ)ᴴ).submatrix (corner hm hn) (corner hm hn)) = (V : Matrix _ _ ℂ) * diagonal (fun q => d (corner hm hn q)) * (V : Matrix _ _ ℂ)ᴴ

**Theorem 1.8 (selected corner psd).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.selected_corner_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.selected_corner_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem selected_corner_psd {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ) (label : Fin r × Fin r → Fin (m * n)) (hl : Function.Injective label) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) (V : unitaryGroup (Fin r × Fin r) ℂ) : (partialTranspose ((V : Matrix _ _ ℂ) * diagonal (fun q => (l (label q) : ℂ)) * (V : Matrix _ _ ℂ)ᴴ)).PosSemidef

**Definition 1.9 (schmidt).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def schmidt {r : ℕ} (x : Fin r → ℝ) : Fin r × Fin r → ℂ

**Definition 1.10 (schmidtPT).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidtPT`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidtPT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def schmidtPT {r : ℕ} (x : Fin r → ℝ) : Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ

**Theorem 1.11 (schmidt pt entry).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem schmidt_pt_entry {r : ℕ} (x : Fin r → ℝ) (p q : Fin r × Fin r) : schmidtPT x p q = if p = (q.2, q.1) then ((x q.1 * x q.2 : ℝ) : ℂ) else 0

**Theorem 1.12 (schmidt pt single).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_single`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem schmidt_pt_single {r : ℕ} (x : Fin r → ℝ) (i j : Fin r) : schmidtPT x *ᵥ Pi.single (i, j) 1 = Pi.single (j, i) (((x i * x j : ℝ) : ℂ))

**Theorem 1.13 (schmidt pt diagonal).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem schmidt_pt_diagonal {r : ℕ} (x : Fin r → ℝ) (i : Fin r) : schmidtPT x *ᵥ Pi.single (i, i) 1 = (((x i ^ 2 : ℝ) : ℂ)) • (Pi.single (i, i) 1)

**Theorem 1.14 (schmidt pt symmetric).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem schmidt_pt_symmetric {r : ℕ} (x : Fin r → ℝ) (i j : Fin r) : schmidtPT x *ᵥ (Pi.single (i, j) 1 + Pi.single (j, i) 1) = (((x i * x j : ℝ) : ℂ)) • (Pi.single (i, j) 1 + Pi.single (j, i) 1)

**Theorem 1.15 (schmidt pt antisymmetric).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_antisymmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_antisymmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem schmidt_pt_antisymmetric {r : ℕ} (x : Fin r → ℝ) (i j : Fin r) : schmidtPT x *ᵥ (Pi.single (i, j) 1 - Pi.single (j, i) 1) = (((-(x i * x j) : ℝ) : ℂ)) • (Pi.single (i, j) 1 - Pi.single (j, i) 1)

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.Outside`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.conjugate_corner`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv_inl`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.cornerEquiv_symm_corner`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.corner_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidtPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_antisymmetric`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_diagonal`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_entry`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_single`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.schmidt_pt_symmetric`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner.selected_corner_psd`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity](QuadbitQuintitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Matrix/PartialTransposeTrace](../../Matrix/PartialTransposeTrace.md)
