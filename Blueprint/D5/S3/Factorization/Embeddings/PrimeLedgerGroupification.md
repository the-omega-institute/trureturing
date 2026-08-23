# Prime Ledger Direction and Groupification

## Abstract

Natural prime ledgers are forward-only; signed ledgers record explicit inverses.

**Theorem 1.1 (Natural ledgers are forward-only and signed ledgers record inverses).**

$$\forall z,\ ((\exists f: NaturalPrimeLedger, naturalLedgerCast(f)=z) \iff (\forall p, 0\leq z_p)) \land\\\exists f,i: NaturalPrimeLedger,\ z=naturalLedgerCast(f)-naturalLedgerCast(i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/PrimeLedgerGroupification.prime_ledger_direction_and_groupification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite signed prime ledger comes from a natural prime ledger exactly when every exponent is nonnegative. Thus a ledger with no inverse component can move only in the coordinatewise forward direction.

Every signed ledger also has an explicit forward-minus-inverse presentation. The forward ledger records the positive part of each exponent and the inverse ledger records the positive part of its negation, so negative exponents occur only through the second recorded ledger.

The library was searched before proving. Finsupp.mapRange constructs both finite natural ledgers, Int.toNat_of_nonneg identifies the nonnegative image, and the exact Mathlib identity Int.toNat_sub_toNat_neg supplies the pointwise groupification decomposition. The theorem applies these pinned components directly.

## References

- Truth anchor: `D5/S3/Factorization/Embeddings/PrimeLedgerGroupification.prime_ledger_direction_and_groupification`
- Dependency: [D5/S3/Factorization/PositiveRationalGroup](../PositiveRationalGroup.md)
