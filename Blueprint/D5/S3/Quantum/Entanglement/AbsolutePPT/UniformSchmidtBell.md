# UniformSchmidtBell

## Abstract

A block Hadamard unitary on every edge pair realizes the independently labelled Bell family. The principal partial-transpose compression is one half of the complexification of the real Schmidt matrix. Literal APPT gives positive semidefiniteness for every independent assignment.

A block Hadamard unitary on every edge pair realizes the independently labelled Bell family. The principal partial-transpose compression is one half of the complexification of the real Schmidt matrix. Literal APPT gives positive semidefiniteness for every independent assignment.

**Definition 1.1 (pairMatrix).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pairMatrix`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pairMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def pairMatrix (r : ℕ) : Matrix (Edge r ⊕ Edge r) (Edge r ⊕ Edge r) ℂ

**Theorem 1.2 (pairMatrix unitary).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pairMatrix_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pairMatrix_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem pairMatrix_unitary (r : ℕ) : pairMatrix r ∈ unitaryGroup _ ℂ

**Definition 1.3 (pairUnitary).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pairUnitary`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pairUnitary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def pairUnitary (r : ℕ) : unitaryGroup (Edge r ⊕ Edge r) ℂ

**Definition 1.4 (bellEquiv).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bellEquiv`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bellEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def bellEquiv (r : ℕ) : ((Edge r ⊕ Edge r) ⊕ Fin r) ≃ (Fin r × Fin r)

**Definition 1.5 (bellUnitary).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bellUnitary`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bellUnitary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def bellUnitary (r : ℕ) : unitaryGroup (Fin r × Fin r) ℂ

**Theorem 1.6 (pair conjugate diagonal).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pair_conjugate_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pair_conjugate_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem pair_conjugate_diagonal {r : ℕ} (u v : Edge r → ℂ) : (pairUnitary r : Matrix _ _ ℂ) * diagonal (Sum.elim u v) * (pairUnitary r : Matrix _ _ ℂ)ᴴ = fromBlocks (diagonal (fun e => (u e + v e) / 2)) (diagonal (fun e => (u e - v e) / 2)) (diagonal (fun e => (u e - v e) / 2)) (diagonal (fun e => (u e + v e) / 2))

**Definition 1.7 (pack).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pack`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pack` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def pack {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) : Fin r × Fin r → ℂ

**Theorem 1.8 (bell conjugate).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bell_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bell_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem bell_conjugate {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) : (bellUnitary r : Matrix _ _ ℂ) * diagonal (pack t b) * (bellUnitary r : Matrix _ _ ℂ)ᴴ = (fromBlocks (fromBlocks (diagonal (fun e => ((b (.inr e) + t e : ℝ) : ℂ) / 2)) (diagonal (fun e => ((b (.inr e) - t e : ℝ) : ℂ) / 2)) (diagonal (fun e => ((b (.inr e) - t e : ℝ) : ℂ) / 2)) (diagonal (fun e => ((b (.inr e) + t e : ℝ) : ℂ) / 2))) 0 0 (diagonal (fun i => (b (.inl i) : ℂ)))).submatrix (bellEquiv r).symm (bellEquiv r).symm

**Theorem 1.9 (bell pt principal).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bell_pt_principal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bell_pt_principal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem bell_pt_principal {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) : (partialTranspose ((bellUnitary r : Matrix _ _ ℂ) * diagonal (pack t b) * (bellUnitary r : Matrix _ _ ℂ)ᴴ)).submatrix (fun i => (i, i)) (fun i => (i, i)) = (1 / 2 : ℂ) • (K t b).map Complex.ofReal

**Theorem 1.10 (actual pack).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.actual_pack`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.actual_pack` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_pack {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ) (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) : (fun q => (l (label hN π σ q) : ℂ)) = pack (fun e => l (assignedTopIndex hN π e)) (fun p => l (assignedBottomIndex hN σ p))

**Theorem 1.11 (literal assignment psd).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.literal_assignment_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.literal_assignment_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem literal_assignment_psd {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) : let hN : a r + b r ≤ m * n := (pool_card_sum r).trans_le (Nat.mul_le_mul hm hn) (assignedK hN l π σ).PosSemidef

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.actual_pack`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bellEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bellUnitary`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bell_conjugate`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.bell_pt_principal`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.literal_assignment_psd`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pack`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pairMatrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pairMatrix_unitary`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pairUnitary`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell.pair_conjugate_diagonal`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum](UniformSchmidtSpectrum.md)
