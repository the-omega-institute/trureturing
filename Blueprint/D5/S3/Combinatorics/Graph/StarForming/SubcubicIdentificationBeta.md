# Dissociation and single-counted port attainment

## Abstract

Dissociation and single-counted port attainment

The original twelve-vertex port-state cap is applied to every actual block slice. Summing these slices counts each shared port twice and every other vertex once; the touched-block count is at most both the block count and twice the selected-port count. This proves two beta at most thirteen times the cell count. Alternating phases restrict exactly to the original attaining port witnesses and produce the matching lower bound. The full statement requires a fixed-point-free permutation and an explicit alternating Boolean phase, so odd cyclic sizes are not silently included.

**Definition 1.1 (label).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.label`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.label` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def label (next : Equiv.Perm I) (i : I) (v : Fin 12) : I × Fin 11.

**Definition 1.2 (blockSlice).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.blockSlice`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.blockSlice` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def blockSlice (next : Equiv.Perm I) (S : Finset (I × Fin 11)) (i : I) : Finset (Fin 12).

**Definition 1.3 (ports).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.ports`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.ports` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def ports (S : Finset (I × Fin 11)) : Finset I.

**Definition 1.4 (touched).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.touched`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.touched` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def touched (next : Equiv.Perm I) (S : Finset (I × Fin 11)) : Finset I.

**Theorem 1.5 (block cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.block_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.block_cap` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem block_cap (next : Equiv.Perm I) (nf : ∀ i, next i≠i) (S : Finset (I × Fin 11)) (hS : IsKIndependent (graph next) 2 S) (i : I) : (blockSlice next S i).card≤6+(if i∈touched next S then 1 else 0).

**Theorem 1.6 (block sum).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.block_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.block_sum` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem block_sum (next : Equiv.Perm I) (S : Finset (I × Fin 11)) : ∑ i : I, (blockSlice next S i).card=S.card+(ports S).card.

**Theorem 1.7 (beta upper).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.beta_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.beta_upper` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_upper (next : Equiv.Perm I) (nf : ∀ i, next i≠i) : 2*beta (graph next) 2≤13*Fintype.card I.

**Definition 1.8 (witness).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.witness`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.witness` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def witness (phase : I → Bool) (x : I × Fin 11) : Prop.

**Theorem 1.9 (witness restriction).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.witness_restriction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.witness_restriction` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem witness_restriction (next : Equiv.Perm I) (phase : I → Bool) (hp : ∀ i, phase (next i)= !(phase i)) (i : I) (v : Fin 12) : witness phase (label next i v) ↔ Subcubic.membership (Subcubic.portWitness (phase i) (phase (next i))) v=true.

**Theorem 1.10 (beta exact).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.beta_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.beta_exact` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_exact (next : Equiv.Perm I) (nf : ∀ i, next i≠i) (phase : I → Bool) (hp : ∀ i, phase (next i)= !(phase i)) : 2*beta (graph next) 2=13*Fintype.card I.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.beta_exact`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.beta_upper`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.blockSlice`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.block_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.block_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.label`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.ports`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.touched`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.witness`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.witness_restriction`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DisjointUnion](DisjointUnion.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentification](SubcubicIdentification.md)
