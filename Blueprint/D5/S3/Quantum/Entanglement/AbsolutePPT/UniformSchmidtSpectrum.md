# UniformSchmidtSpectrum

## Abstract

The ordered spectrum supplies disjoint top and bottom pools. Independent pool permutations give an injective labelling of one actual product corner. Its charge and diagonal bounds use these same pool values, including zeros and ties.

The ordered spectrum supplies disjoint top and bottom pools. Independent pool permutations give an injective labelling of one actual product corner. Its charge and diagonal bounds use these same pool values, including zeros and ties.

**Definition 1.1 (a).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.a`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

abbrev a (r : ℕ)

**Definition 1.2 (b).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.b`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

abbrev b (r : ℕ)

**Definition 1.3 (bellSlotsEquiv).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bellSlotsEquiv`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bellSlotsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def bellSlotsEquiv (r : ℕ) : (BottomSlot r ⊕ Edge r) ≃ (Fin r × Fin r)

**Theorem 1.4 (pool card sum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.pool_card_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.pool_card_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem pool_card_sum (r : ℕ) : a r + b r = r * r

**Definition 1.5 (topIndex).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.topIndex`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.topIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def topIndex {N a b : ℕ} (hN : a + b ≤ N) (i : Fin a) : Fin N

**Definition 1.6 (bottomIndex).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottomIndex`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottomIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def bottomIndex {N a b : ℕ} (hN : a + b ≤ N) (i : Fin b) : Fin N

**Definition 1.7 (bottomStart).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottomStart`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottomStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def bottomStart {N a b : ℕ} (hN : a + b ≤ N) (hb : 0 < b) : Fin N

**Theorem 1.8 (topIndex injective).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.topIndex_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.topIndex_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem topIndex_injective {N a b : ℕ} (hN : a + b ≤ N) : Function.Injective (topIndex hN)

**Theorem 1.9 (bottomIndex injective).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottomIndex_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottomIndex_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem bottomIndex_injective {N a b : ℕ} (hN : a + b ≤ N) : Function.Injective (bottomIndex hN)

**Theorem 1.10 (bottom top separated).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottom_top_separated`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottom_top_separated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem bottom_top_separated {N a b : ℕ} (hN : a + b ≤ N) (i : Fin a) (j : Fin b) : topIndex hN i < bottomIndex hN j

**Definition 1.11 (assignedTopIndex).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedTopIndex`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedTopIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def assignedTopIndex {r N : ℕ} (hN : a r + b r ≤ N) (π : Equiv.Perm (Fin (a r))) (e : Edge r) : Fin N

**Definition 1.12 (assignedBottomIndex).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedBottomIndex`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedBottomIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def assignedBottomIndex {r N : ℕ} (hN : a r + b r ≤ N) (σ : Equiv.Perm (Fin (b r))) (p : BottomSlot r) : Fin N

**Definition 1.13 (label).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.label`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def label {r N : ℕ} (hN : a r + b r ≤ N) (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) : Fin r × Fin r → Fin N

**Theorem 1.14 (label injective).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.label_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.label_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem label_injective {r N : ℕ} (hN : a r + b r ≤ N) (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) : Function.Injective (label hN π σ)

**Definition 1.15 (assignedK).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def assignedK {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ) (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) : Matrix (Fin r) (Fin r) ℝ

**Theorem 1.16 (assignedK offDiag).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK_offDiag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK_offDiag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem assignedK_offDiag {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ) (hl : Antitone l) (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) (i j : Fin r) (hij : i ≠ j) : assignedK hN l π σ i j ≤ 0

**Theorem 1.17 (assignedK diag).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem assignedK_diag {r N : ℕ} (hN : a r + b r ≤ N) (hb : 0 < b r) (l : Fin N → ℝ) (hl : Antitone l) (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) (i : Fin r) : assignedK hN l π σ i i ≤ 2 * l (bottomStart hN hb)

**Theorem 1.18 (sum assignedTop).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.sum_assignedTop`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.sum_assignedTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem sum_assignedTop {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ) (π : Equiv.Perm (Fin (a r))) : (∑ e : Edge r, l (assignedTopIndex hN π e)) = ∑ k : Fin (a r), l (topIndex hN k)

**Theorem 1.19 (sum assignedBottom).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.sum_assignedBottom`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.sum_assignedBottom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem sum_assignedBottom {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ) (σ : Equiv.Perm (Fin (b r))) : (∑ p : BottomSlot r, l (assignedBottomIndex hN σ p)) = ∑ k : Fin (b r), l (bottomIndex hN k)

**Theorem 1.20 (assignedK charge).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK_charge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem assignedK_charge {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ) (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) : UniformSchmidtDefectMoment.uniformCharge (assignedK hN l π σ) = 2 * ((∑ k : Fin (b r), l (bottomIndex hN k)) - ∑ k : Fin (a r), l (topIndex hN k))

**Theorem 1.21 (actual corner psd).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.actual_corner_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.actual_corner_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_corner_psd {r m n : ℕ} (hm : r ≤ m) (hn : r ≤ n) (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) (π : Equiv.Perm (Fin (a r))) (σ : Equiv.Perm (Fin (b r))) (V : unitaryGroup (Fin r × Fin r) ℂ) : let hN : a r + b r ≤ m * n := (pool_card_sum r).trans_le (Nat.mul_le_mul hm hn) (partialTranspose ((V : Matrix _ _ ℂ) * diagonal (fun q => (l (label hN π σ q) : ℂ)) * (V : Matrix _ _ ℂ)ᴴ)).PosSemidef

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.a`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.actual_corner_psd`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedBottomIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK_charge`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK_diag`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedK_offDiag`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.assignedTopIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.b`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bellSlotsEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottomIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottomIndex_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottomStart`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.bottom_top_separated`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.label`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.label_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.pool_card_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.sum_assignedBottom`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.sum_assignedTop`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.topIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtSpectrum.topIndex_injective`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner](UniformSchmidtCorner.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence](UniformSchmidtIncidence.md)
