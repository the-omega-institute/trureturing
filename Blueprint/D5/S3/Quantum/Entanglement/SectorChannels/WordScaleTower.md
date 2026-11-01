# Compact Physical Word Tower

## Abstract

Common digit words give a strictly composable compact physical CPTP tower.

This construction is the physical transport part of the integer-scale sector tower. The intended base range b(s) >= 2 and finite nonempty sector families is included. Repeated bases, singleton families, level zero and zero-length segments require no exceptions. The local map acts on every physical matrix, including unused code coordinates and cross-sector coherences.

The proof first reconstructs a compact coordinate from its kept word and residual word. It then proves that equality of a direct residual word is equivalent to equality of the two consecutive residual words. Applying the actual Kraus action on every matrix unit yields full channel composition. Equality only on the encoded logical subspace is never used to infer equality on the physical matrix algebra.

**Definition 1.1 (Compact physical level).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.Level`

*Formalization.* `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.Level` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The physical carrier at level n is the dependent sum of Fin(b(s)^n), retaining every sector label.

**Definition 1.2 (One common digit alphabet).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.alphabet`

*Formalization.* `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.alphabet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The alphabet size is the maximum of the finite base family. Each sector digit embeds by its ordinary value.

**Definition 1.3 (Common residual words).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.Word`

*Formalization.* `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word of length l is a function from Fin l into the common finite alphabet. Empty words form a singleton.

**Definition 1.4 (Least significant digits).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.digits`

*Formalization.* `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.digits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit pinned Mathlib finFunctionFinEquiv gives a genuine equivalence between Fin(b(s)^n) and length-n base-b(s) digit words. Its inverse evaluates the sum of digit(q) times b(s)^q.

**Definition 1.5 (Expansion in the common alphabet).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.commonWord`

*Formalization.* `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.commonWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each sector digit is included in the same alphabet, without identifying the numerical values of whole residual integers across different bases.

**Definition 1.6 (Retain the low positions).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.keep`

*Formalization.* `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.keep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrict the actual compact basis word to positions below j, then use the same explicit base expansion equivalence to return to the compact level-j carrier.

**Definition 1.7 (Discard the high positions).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.tail`

*Formalization.* `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.tail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The residual word records the original positions j through n-1 in the fixed common alphabet. The same word equality compares residual digits across all sectors.

**Definition 1.8 (Actual word Kraus operators).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.localKraus`

*Formalization.* `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.localKraus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix entry is one exactly when its retained coordinate and residual word match the input expansion, and zero otherwise. A common word invalid in a sector therefore annihilates every basis vector of that sector.

**Definition 1.9 (Local CPTP channel).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.localChannel`

*Formalization.* `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.localChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep and tail together determine each compact input coordinate. This injectivity proves Kraus completeness. The existing finite_kraus_quantum_channel theorem then constructs the actual completely positive trace-preserving map.

**Definition 1.10 (Product physical channel).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.jointChannel`

*Formalization.* `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.jointChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The joint channel uses pairs of independent residual-word labels. Its all-matrix tensor action is proved against the existing TensorRealization predicate.

**Theorem 1.11 (Strict compact physical word tower).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite sector family, every base family and every n >= j >= h >= 0, the constructed local and joint channels compose strictly on their entire physical matrix algebras. The theorem also supplies their tensor realization, the exact local matrix-unit action and both zero-segment identity actions.

Original theorem 34.3 is not closed by this physical transport result. The common canonical level encoding, its exact encoded Schur action and reference lift, transfer of the published full operation-class optimum, the floor-lambda distinct-base limit, and both actual endpoint marginal bridges remain separate obligations. No standalone endpoint-normalization unit is supplied here.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.Level`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.Word`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.alphabet`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.commonWord`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.digits`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.jointChannel`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.keep`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.localChannel`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.localKraus`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.tail`
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorChannelModel](../FiniteSectorChannelModel.md)
- Dependency: [D5/S3/Quantum/Entanglement/SectorSchmidtEncoding](../SectorSchmidtEncoding.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../../Foundation/FiniteKrausChannel.md)
