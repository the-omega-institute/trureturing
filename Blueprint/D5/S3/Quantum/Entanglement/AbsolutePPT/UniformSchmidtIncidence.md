# UniformSchmidtIncidence

## Abstract

Complete-graph edges and diagonal-plus-edge bottom slots give the exact incidence weights of the Schmidt matrix. The row, trace, charge and weight-moment identities hold in arbitrary finite dimension, including degenerate dimensions whenever the displayed hypotheses permit them.

Complete-graph edges and diagonal-plus-edge bottom slots give the exact incidence weights of the Schmidt matrix. The row, trace, charge and weight-moment identities hold in arbitrary finite dimension, including degenerate dimensions whenever the displayed hypotheses permit them.

**Definition 1.1 (Edge).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.Edge`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

abbrev Edge (r : ℕ)

**Definition 1.2 (BottomSlot).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.BottomSlot`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.BottomSlot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

abbrev BottomSlot (r : ℕ)

**Definition 1.3 (slotCoord).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.slotCoord`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.slotCoord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def slotCoord {r : ℕ} : (Fin r ⊕ (Edge r ⊕ Edge r)) → Fin r × Fin r | .inl i => (i, i) | .inr (.inl e) => e.val | .inr (.inr e) => (e.val.2, e.val.1) def coordSlot {r : ℕ} (p : Fin r × Fin r) : Fin r ⊕ (Edge r ⊕ Edge r)

**Definition 1.4 (coordSlot).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.coordSlot`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.coordSlot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def coordSlot {r : ℕ} (p : Fin r × Fin r) : Fin r ⊕ (Edge r ⊕ Edge r)

**Definition 1.5 (slotEquiv).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.slotEquiv`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.slotEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def slotEquiv (r : ℕ) : (Fin r ⊕ (Edge r ⊕ Edge r)) ≃ (Fin r × Fin r)

**Theorem 1.6 (edge card real).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.edge_card_real`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.edge_card_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem edge_card_real (r : ℕ) : (Fintype.card (Edge r) : ℝ) = (r : ℝ) * ((r : ℝ) - 1) / 2

**Theorem 1.7 (bottom card real).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_card_real`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_card_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem bottom_card_real (r : ℕ) : (Fintype.card (BottomSlot r) : ℝ) = (r : ℝ) * ((r : ℝ) + 1) / 2

**Definition 1.8 (incident).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def incident {r : ℕ} (i : Fin r) (e : Edge r) : Prop

**Definition 1.9 (edge).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.edge`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def edge {r : ℕ} (i j : Fin r) (h : i ≠ j) : Edge r

**Theorem 1.10 (edge symm).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.edge_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.edge_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem edge_symm {r : ℕ} (i j : Fin r) (h : i ≠ j) : edge i j h = edge j i h.symm

**Definition 1.11 (incidentNeighbor).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incidentNeighbor`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incidentNeighbor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def incidentNeighbor {r : ℕ} (i : Fin r) (e : {e : Edge r // incident i e}) : {j : Fin r // j ≠ i}

**Definition 1.12 (neighborIncident).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.neighborIncident`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.neighborIncident` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def neighborIncident {r : ℕ} (i : Fin r) (j : {j : Fin r // j ≠ i}) : {e : Edge r // incident i e}

**Definition 1.13 (incidentEquiv).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incidentEquiv`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incidentEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def incidentEquiv {r : ℕ} (i : Fin r) : {e : Edge r // incident i e} ≃ {j : Fin r // j ≠ i}

**Theorem 1.14 (incident card).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident_card`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem incident_card {r : ℕ} (i : Fin r) : Fintype.card {e : Edge r // incident i e} = r - 1

**Definition 1.15 (topWeight).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.topWeight`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.topWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def topWeight {r : ℕ} (i : Fin r) (e : Edge r) : ℝ

**Definition 1.16 (bottomWeight).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottomWeight`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottomWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def bottomWeight {r : ℕ} (i : Fin r) : BottomSlot r → ℝ | .inl j => if i = j then 2 else 0 | .inr e => if incident i e then 1 else 0 theorem incident_indicator_sum {r : ℕ} (i : Fin r) : (∑ e : Edge r, if incident i e then (1 : ℝ) else 0) = (r : ℝ) - 1

**Theorem 1.17 (incident indicator sum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident_indicator_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident_indicator_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem incident_indicator_sum {r : ℕ} (i : Fin r) : (∑ e : Edge r, if incident i e then (1 : ℝ) else 0) = (r : ℝ) - 1

**Theorem 1.18 (top weight sum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.top_weight_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.top_weight_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem top_weight_sum {r : ℕ} (i : Fin r) : (∑ e, topWeight i e) = -((r : ℝ) - 1)

**Theorem 1.19 (top weight squares).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.top_weight_squares`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.top_weight_squares` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem top_weight_squares {r : ℕ} (i : Fin r) : (∑ e, (topWeight i e)^2) = (r : ℝ) - 1

**Theorem 1.20 (bottom weight sum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_weight_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_weight_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem bottom_weight_sum {r : ℕ} (i : Fin r) : (∑ p, bottomWeight i p) = (r : ℝ) + 1

**Theorem 1.21 (bottom weight squares).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_weight_squares`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_weight_squares` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem bottom_weight_squares {r : ℕ} (i : Fin r) : (∑ p, (bottomWeight i p)^2) = (r : ℝ) + 3

**Definition 1.22 (K).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def K {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) : Matrix (Fin r) (Fin r) ℝ

**Theorem 1.23 (K isHermitian).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem K_isHermitian {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) : (K t b).IsHermitian

**Theorem 1.24 (K offDiag).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_offDiag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_offDiag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem K_offDiag {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) (hsep : ∀ e f, b (.inr e) ≤ t f) (i j : Fin r) (h : i ≠ j) : K t b i j ≤ 0

**Theorem 1.25 (K diag).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem K_diag {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) (γ : ℝ) (hb : ∀ i, b (.inl i) ≤ γ) (i : Fin r) : K t b i i ≤ 2 * γ

**Theorem 1.26 (incident sum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem incident_sum {r : ℕ} (i : Fin r) (f : Edge r → ℝ) : (∑ j : {j : Fin r // j ≠ i}, f (edge i j.val j.property.symm)) = ∑ e : Edge r, if incident i e then f e else 0

**Theorem 1.27 (neighbor sum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.neighbor_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.neighbor_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem neighbor_sum {r : ℕ} (i : Fin r) (f : Edge r → ℝ) : (∑ j : Fin r, if h : i = j then 0 else f (edge i j h)) = ∑ e : Edge r, if incident i e then f e else 0

**Theorem 1.28 (K row).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_row`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem K_row {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) (i : Fin r) : UniformSchmidtDefectMoment.rowSum (K t b) i = (∑ e, topWeight i e * t e) + (∑ p, bottomWeight i p * b p)

**Theorem 1.29 (top column sum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.top_column_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.top_column_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem top_column_sum {r : ℕ} (e : Edge r) : (∑ i : Fin r, topWeight i e) = -2

**Theorem 1.30 (bottom column sum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_column_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_column_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem bottom_column_sum {r : ℕ} (p : BottomSlot r) : (∑ i : Fin r, bottomWeight i p) = 2

**Theorem 1.31 (K charge).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_charge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem K_charge {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) : UniformSchmidtDefectMoment.uniformCharge (K t b) = 2 * ((∑ p, b p) - ∑ e, t e)

**Theorem 1.32 (K trace).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem K_trace {r : ℕ} (t : Edge r → ℝ) (b : BottomSlot r → ℝ) : (K t b).trace = 2 * ∑ i, b (.inl i)

**Theorem 1.33 (incidence factors).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incidence_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incidence_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem incidence_factors {r : ℕ} (hr : 3 ≤ r) : let a : ℝ := Fintype.card (Edge r) let b : ℝ := Fintype.card (BottomSlot r) (a * ((r : ℝ) - 1) - (-((r : ℝ) - 1))^2) / (a * (a - 1)) = 2 * ((r : ℝ) - 1) / ((r : ℝ) * ((r : ℝ) + 1)) ∧ (b * ((r : ℝ) + 3) - ((r : ℝ) + 1)^2) / (b * (b - 1)) = 2 / (r : ℝ)

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.BottomSlot`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.Edge`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_charge`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_diag`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_isHermitian`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_offDiag`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_row`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.K_trace`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottomWeight`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_card_real`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_column_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_weight_squares`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.bottom_weight_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.coordSlot`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.edge`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.edge_card_real`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.edge_symm`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incidence_factors`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incidentEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incidentNeighbor`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident_card`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident_indicator_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.incident_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.neighborIncident`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.neighbor_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.slotCoord`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.slotEquiv`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.topWeight`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.top_column_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.top_weight_squares`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtIncidence.top_weight_sum`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment](UniformSchmidtDefectMoment.md)
