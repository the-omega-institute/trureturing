# FiveRowP2Lift

## Abstract

Spectral gaps reconstruct an arbitrary ordered nonnegative vector. Concentrating its middle gaps preserves the boundary values; convexity transfers a quadratic upper bound from the concentrated vectors.

Spectral gaps reconstruct an arbitrary ordered nonnegative vector. Concentrating its middle gaps preserves the boundary values; convexity transfers a quadratic upper bound from the concentrated vectors.

**Definition 1.1 (middle).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middle`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def middle (N : ℕ) : Finset (Fin N)

**Definition 1.2 (middleMass).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middleMass`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middleMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def middleMass {N : ℕ} (g : Fin N → ℝ) : ℝ

**Definition 1.3 (frozen).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.frozen`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.frozen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def frozen {N : ℕ} (g : Fin N → ℝ) : Fin N → ℝ

**Definition 1.4 (concentrated).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def concentrated {N : ℕ} (g : Fin N → ℝ) (j : Fin N) : Fin N → ℝ

**Theorem 1.5 (concentrated nonnegative).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem concentrated_nonnegative {N : ℕ} (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i,0 ≤ l i) (j : Fin N) : ∀ k,0 ≤ concentrated (spectralGap l) j k

**Theorem 1.6 (middle mass actual).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middle_mass_actual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middle_mass_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem middle_mass_actual {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : middleMass (spectralGap l) = l ⟨9,by omega⟩-l ⟨N-15,by omega⟩

**Theorem 1.7 (concentrated boundary).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem concentrated_boundary {N : ℕ} (l : Fin N → ℝ) (j : Fin N) (hj : j ∈ middle N) (k : Fin N) (hk : k.val < 10 ∨ N-15 ≤ k.val) : concentrated (spectralGap l) j k = l k

**Theorem 1.8 (concentration transfer).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentration_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentration_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem concentration_transfer {N : ℕ} (hN : 25 ≤ N) (theta : ℝ) (ht : 0 ≤ theta) (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i) (hc : ∀ j ∈ middle N, 0 ≤ ∑ i, concentrated (spectralGap l) j i) (hb : ∀ j ∈ middle N, ∑ i, (concentrated (spectralGap l) j i)^2 ≤ theta*(∑ i, concentrated (spectralGap l) j i)^2) : ∑ i, (l i)^2 ≤ theta*(∑ i, l i)^2

**Theorem 1.9 (augmented norm lift).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.augmented_norm_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.augmented_norm_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem augmented_norm_lift {I J : Type*} [Fintype I] [Fintype J] (p : I → ℝ) (x : I → J → ℝ) (l : J → ℝ) (theta c : ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) (ht : 0 ≤ theta) (hc : 0 ≤ c) (hm : ∀ i, 0 ≤ ∑ j, x i j) (hr : ∀ j, l j=∑ i, p i*x i j) (hb : ∀ i, (∑ j, (x i j)^2)+c ≤ theta*(∑ j, x i j)^2) : (∑ j, (l j)^2)+c ≤ theta*(∑ j, l j)^2

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.augmented_norm_lift`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated_boundary`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentrated_nonnegative`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.concentration_transfer`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.frozen`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middle`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middleMass`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift.middle_mass_actual`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer](HalfspaceConeTransfer.md)
