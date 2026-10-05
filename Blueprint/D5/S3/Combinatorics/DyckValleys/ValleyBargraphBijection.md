# Mu–Welker valley/profile inverse core

## Abstract

The boundary-level list operations behind the Mu–Welker bargraph/Dyck-path correspondence are literal inverses.

**Theorem 1.1 (Expansion and contraction).**

*Formalization.* `D5/S3/Combinatorics/DyckValleys/ValleyBargraphBijection.expand_contract`, `contract_expand`, and `valleyCount_expand`.

*Proof.* Machine-checked in Lean as the declarations above. `expand` replaces a profile horizontal edge (`none`) by `DU`; `contract` replaces each `DU` factor by one horizontal edge. `contract_expand` assumes that profile words have no adjacent profile `D,U` steps, and `expand_contract` is unconditional.

**Theorem 1.2 (Valley-count agreement).**

*Formalization.* `D5/S3/Combinatorics/DyckValleys/ValleyBargraphBijection.sourceValleys_eq_valleyCount`.

The kernel count agrees with the project's zipped adjacent-pair definition of valleys. The remaining source-faithful admission work is to prove that positive column-height lists produce valid profiles/Dyck words and that contracting a UUDD-avoiding Dyck word satisfies the bargraph boundary conditions and preserves semiperimeter.

## References

- Truth anchor: `D5/S3/Combinatorics/DyckValleys/ValleyBargraphBijection.expand_contract`
- Truth anchor: `D5/S3/Combinatorics/DyckValleys/ValleyBargraphBijection.contract_expand`
- Truth anchor: `D5/S3/Combinatorics/DyckValleys/ValleyBargraphBijection.sourceValleys_eq_valleyCount`
