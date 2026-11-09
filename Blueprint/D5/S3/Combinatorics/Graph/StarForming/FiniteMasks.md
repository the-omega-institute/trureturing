# Exact finite selection masks

## Abstract

Exact finite selection masks

For every natural n, including zero, the bounded masks Fin(2^n) are in bijection with Boolean selections of Fin n. Bit functions are injective because all higher bits vanish; equality of the finite cardinalities gives surjectivity. Every actual finite subset is therefore represented, and the original supplier List.finRange filter count equals its canonical Finset cardinality. No bounded verification replaces a theorem over unbounded graph orders.

**Definition 1.1 (bits).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.bits`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.bits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def bits (n : ℕ) (mask : Fin (2 ^ n)) (v : Fin n) : Bool.

**Theorem 1.2 (bits injective).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.bits_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.bits_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem bits_injective (n : ℕ) : Function.Injective (bits n).

**Theorem 1.3 (bits surjective).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.bits_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.bits_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem bits_surjective (n : ℕ) : Function.Surjective (bits n).

**Theorem 1.4 (selection mask).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.selection_mask`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.selection_mask` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem selection_mask {n : ℕ} (S : Finset (Fin n)) : ∃ mask : Fin (2 ^ n), ∀ v, mask.val.testBit v.val = true ↔ v ∈ S.

**Theorem 1.5 (list count).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.list_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.list_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem list_count {n : ℕ} (p : Fin n → Bool) : ((List.finRange n).filter p).length = (Finset.univ.filter (fun v => p v = true)).card.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.bits`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.bits_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.bits_surjective`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.list_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.selection_mask`
