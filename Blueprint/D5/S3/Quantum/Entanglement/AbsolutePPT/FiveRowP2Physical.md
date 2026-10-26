# FiveRowP2Physical

## Abstract

Literal APPT of one ordered spectrum supplies every independently labelled Bell compression. These compressions imply the scalar constraints and exact concentrated moments. The physical upper estimate covers every integer n at least nineteen, with separate zero-scale, nineteen, and at-least-twenty branches. This upper estimate does not assert attainment or the full maximum.

Literal APPT of one ordered spectrum supplies every independently labelled Bell compression. These compressions imply the scalar constraints and exact concentrated moments. The physical upper estimate covers every integer n at least nineteen, with separate zero-scale, nineteen, and at-least-twenty branches. This upper estimate does not assert attainment or the full maximum.

Middle-gap concentration preserves the labelled boundaries of the actual spectrum. The concentration definitions and consumed transfer helpers belong to this physical proof chain; they supply no separate host admission claim.

**Definition 1.1 (middle).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.middle`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.middle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def middle (N : ℕ) : Finset (Fin N)

**Definition 1.2 (middleMass).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.middleMass`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.middleMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def middleMass {N : ℕ} (g : Fin N → ℝ) : ℝ

**Definition 1.3 (frozen).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.frozen`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.frozen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def frozen {N : ℕ} (g : Fin N → ℝ) : Fin N → ℝ

**Definition 1.4 (concentrated).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def concentrated {N : ℕ} (g : Fin N → ℝ) (j : Fin N) : Fin N → ℝ

**Theorem 1.5 (concentrated nonnegative).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem concentrated_nonnegative {N : ℕ} (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i,0 ≤ l i) (j : Fin N) : ∀ k,0 ≤ concentrated (spectralGap l) j k

**Theorem 1.6 (middle mass actual).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.middle_mass_actual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.middle_mass_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem middle_mass_actual {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : middleMass (spectralGap l) = l ⟨9,by omega⟩-l ⟨N-15,by omega⟩

**Theorem 1.7 (concentrated boundary).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem concentrated_boundary {N : ℕ} (l : Fin N → ℝ) (j : Fin N) (hj : j ∈ middle N) (k : Fin N) (hk : k.val < 10 ∨ N-15 ≤ k.val) : concentrated (spectralGap l) j k = l k

**Theorem 1.8 (concentration transfer).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentration_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentration_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem concentration_transfer {N : ℕ} (hN : 25 ≤ N) (theta : ℝ) (ht : 0 ≤ theta) (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i) (hc : ∀ j ∈ middle N, 0 ≤ ∑ i, concentrated (spectralGap l) j i) (hb : ∀ j ∈ middle N, ∑ i, (concentrated (spectralGap l) j i)^2 ≤ theta*(∑ i, concentrated (spectralGap l) j i)^2) : ∑ i, (l i)^2 ≤ theta*(∑ i, l i)^2

**Theorem 1.9 (literal five row variance).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.literal_five_row_variance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.literal_five_row_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem literal_five_row_variance (n : ℕ) (hn : 5 ≤ n) (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ) (hl : Antitone l) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) : let hN : a 5+b 5 ≤ 5*n := (pool_card_sum 5).trans_le (Nat.mul_le_mul (by rfl) hn) let A := ∑ k : Fin (a 5),l (topIndex hN k) let B' := ∑ k : Fin (b 5),l (bottomIndex hN k) let s := B'-A let u := l (bottomStart hN (bottom_pos (by norm_num))) momentLHS hN l ≤ 4*u*s-(2/5)*s^2

**Definition 1.10 (u).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.u`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.u` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def u {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ

**Definition 1.11 (v).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.v`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def v {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ

**Definition 1.12 (heads).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.heads`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.heads` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def heads {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : Fin 10 → ℝ

**Definition 1.13 (tails).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.tails`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.tails` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def tails {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : Fin 15 → ℝ

**Definition 1.14 (H).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.H`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def H {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ

**Definition 1.15 (D).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.D`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def D {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ

**Definition 1.16 (headEnergy).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.headEnergy`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.headEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def headEnergy {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ

**Definition 1.17 (tailEnergy).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.tailEnergy`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.tailEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def tailEnergy {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ

**Theorem 1.18 (literal defect family).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.literal_defect_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.literal_defect_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem literal_defect_family (n : ℕ) (hn : 5 ≤ n) (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) : let hN : 25 ≤ 5*n := by omega FiveRowP2Star.FullPSD (u hN l) (v hN l) (heads hN l) (tails hN l)

**Theorem 1.19 (actual pool signs).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.actual_pool_signs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.actual_pool_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_pool_signs {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) (hl : Antitone l) (h0 : ∀ i,0 ≤ l i) : 0 ≤ u hN l ∧ 0 ≤ v hN l ∧ (∀ i,0 ≤ heads hN l i) ∧ (∀ i,0 ≤ tails hN l i ∧ tails hN l i ≤ u hN l) ∧ heads hN l 9=0 ∧ tails hN l 0=0

**Theorem 1.20 (homogeneous zero actual).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.homogeneous_zero_actual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.homogeneous_zero_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem homogeneous_zero_actual (n : ℕ) (hn : 5 ≤ n) (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ) (hl : Antitone l) (h0 : ∀ i,0 ≤ l i) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) (hu : u (by omega : 25 ≤ 5*n) l=0) : l=0

**Definition 1.21 (normalizedHyp).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.normalizedHyp`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.normalizedHyp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def normalizedHyp {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : Prop

**Definition 1.22 (PhysicalScalarExtractionGap).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.PhysicalScalarExtractionGap`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.PhysicalScalarExtractionGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def PhysicalScalarExtractionGap : Prop

**Definition 1.23 (ConcentratedMomentsGap).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.ConcentratedMomentsGap`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.ConcentratedMomentsGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def ConcentratedMomentsGap : Prop

**Theorem 1.24 (zero slot cauchy).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.zero_slot_cauchy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.zero_slot_cauchy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem zero_slot_cauchy {m : ℕ} (z : Fin (m+1) → ℝ) (i : Fin (m+1)) (hi : z i=0) : (∑ j,z j)^2 ≤ (m:ℝ)*(∑ j,(z j)^2)

**Theorem 1.25 (top three psd).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.top_three_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.top_three_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem top_three_psd (U V : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ) (hV : 0 ≤ V) (hh : ∀ i,0 ≤ h i) (hd : ∀ i,0 ≤ d i) (hf : FiveRowP2Star.FullPSD U V h d) : (d 12)^2 ≤ 4*(U-d 14)*(U-d 13)

**Theorem 1.26 (monotone tail square cap).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.monotone_tail_square_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.monotone_tail_square_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem monotone_tail_square_cap (z : Fin 15 → ℝ) (m : ℝ) (hm : 3 ≤ m) (h0 : ∀ i,0 ≤ z i) (h1 : ∀ i,z i ≤ 1) (ho : Monotone z) (hsum : ∑ i,z i ≤ m) (hp : (z 12)^2 ≤ 4*(1-z 14)*(1-z 13)) : (∑ i,(z i)^2) ≤ 2*m/3

**Theorem 1.27 (actual variance).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.actual_variance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.actual_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_variance (n : ℕ) (hn : 5 ≤ n) (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ) (hl : Antitone l) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) : let hN : 25 ≤ 5*n := by omega let S := 5*u hN l-10*v hN l-H hN l-D hN l (2/3)*(headEnergy hN l-(H hN l)^2/10)+ (tailEnergy hN l-(D hN l)^2/15) ≤ 4*u hN l*S-(2/5)*S^2

**Theorem 1.28 (physical extraction with witness).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.physical_extraction_with_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.physical_extraction_with_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem physical_extraction_with_witness (n : ℕ) (hn : 19 ≤ n) (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ) (hl : Antitone l) (h0 : ∀ i,0 ≤ l i) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) (hu : 0 < u (by omega : 25 ≤ 5*n) l) (w : FiveRowP2Star.CouplingWitness (u (by omega) l) (v (by omega) l) (heads (by omega) l) (tails (by omega) l)) : normalizedHyp (by omega) l

**Theorem 1.29 (physicalScalarExtraction).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.physicalScalarExtraction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.physicalScalarExtraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem physicalScalarExtraction : PhysicalScalarExtractionGap

**Theorem 1.30 (concentrated raw moments).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated_raw_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated_raw_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem concentrated_raw_moments {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) (j : Fin N) (hj : j ∈ middle N) : (∑ k,concentrated (spectralGap l) j k)= (N:ℝ)*u hN l+(j.val+1:ℕ)*v hN l+H hN l-D hN l ∧ (∑ k,(concentrated (spectralGap l) j k)^2)= (N:ℝ)*(u hN l)^2+(j.val+1:ℕ)*(2*u hN l*v hN l+(v hN l)^2)+ 2*(u hN l+v hN l)*H hN l-2*u hN l*D hN l+ headEnergy hN l+tailEnergy hN l

**Theorem 1.31 (concentratedMoments).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentratedMoments`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentratedMoments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem concentratedMoments : ConcentratedMomentsGap

**Theorem 1.32 (physical upper from exact bridges).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.physical_upper_from_exact_bridges`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.physical_upper_from_exact_bridges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem physical_upper_from_exact_bridges (n : ℕ) (hn : 19 ≤ n) (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ) (hl : Antitone l) (h0 : ∀ i,0 ≤ l i) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) : (∑ i,(l i)^2) ≤ (5/(24*(n:ℝ)))*(∑ i,l i)^2

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.ConcentratedMomentsGap`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.D`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.H`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.PhysicalScalarExtractionGap`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.actual_pool_signs`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.actual_variance`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentratedMoments`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated_boundary`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated_nonnegative`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentrated_raw_moments`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.concentration_transfer`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.frozen`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.headEnergy`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.heads`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.homogeneous_zero_actual`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.literal_defect_family`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.literal_five_row_variance`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.middle`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.middleMass`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.middle_mass_actual`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.monotone_tail_square_cap`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.normalizedHyp`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.physicalScalarExtraction`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.physical_extraction_with_witness`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.physical_upper_from_exact_bridges`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.tailEnergy`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.tails`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.top_three_psd`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.u`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.v`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical.zero_slot_cauchy`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Nineteen](FiveRowP2Nineteen.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Star](FiveRowP2Star.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer](HalfspaceConeTransfer.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer](UniformSchmidtVarianceConsumer.md)
