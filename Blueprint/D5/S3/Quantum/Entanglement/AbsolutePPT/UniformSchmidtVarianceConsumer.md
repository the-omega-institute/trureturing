# UniformSchmidtVarianceConsumer

## Abstract

Exact independent assignment moments apply to the literal Bell family produced by one APPT spectrum. Singular PSD matrices and zero pool variances are included. Rank two uses its singleton top pool separately; larger ranks use the general incidence moments.

Exact independent assignment moments apply to the literal Bell family produced by one APPT spectrum. Singular PSD matrices and zero pool variances are included. Rank two uses its singleton top pool separately; larger ranks use the general incidence moments.

**Theorem 1.1 (bottom pos).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.bottom_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.bottom_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem bottom_pos {r : ℕ} (hr : 2 ≤ r) : 0 < b r

**Definition 1.2 (variance).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.variance`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.variance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def variance {k : ℕ} (z : Fin k → ℝ) : ℝ

**Definition 1.3 (momentLHS).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.momentLHS`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.momentLHS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def momentLHS {r N : ℕ} (hN : a r + b r ≤ N) (l : Fin N → ℝ) : ℝ

**Definition 1.4 (momentRHS).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.momentRHS`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.momentRHS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def momentRHS {r N : ℕ} (hN : a r + b r ≤ N) (hb : 0 < b r) (l : Fin N → ℝ) : ℝ

**Theorem 1.5 (literal r2 variance moment).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.literal_r2_variance_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.literal_r2_variance_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem literal_r2_variance_moment {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ) (hl : Antitone l) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) : let hN : a 2 + b 2 ≤ m * n := (pool_card_sum 2).trans_le (Nat.mul_le_mul hm hn) momentLHS hN l ≤ momentRHS hN (bottom_pos (by norm_num)) l

**Theorem 1.6 (literal variance moment).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.literal_variance_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.literal_variance_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem literal_variance_moment {r m n : ℕ} (hr : 2 ≤ r) (hm : r ≤ m) (hn : r ≤ n) (e : (Fin m × Fin n) ≃ Fin (m * n)) (l : Fin (m * n) → ℝ) (hl : Antitone l) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) : let hN : a r + b r ≤ m * n := (pool_card_sum r).trans_le (Nat.mul_le_mul hm hn) momentLHS hN l ≤ momentRHS hN (bottom_pos hr) l

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.bottom_pos`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.literal_r2_variance_moment`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.literal_variance_moment`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.momentLHS`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.momentRHS`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtVarianceConsumer.variance`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell](UniformSchmidtBell.md)
