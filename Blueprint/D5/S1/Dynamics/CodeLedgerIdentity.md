# Identity from Canonical Code and Ledger

## Abstract

A canonical prime-axis code together with a ledger coordinate exactly determines state identity.

**Theorem 1.1 (States agree exactly when their codes and ledgers agree).**

$$\forall Ledger: \operatorname{Type}, \forall K_1, K_2: \operatorname{CodeLedgerState}(Ledger), K_1=K_2 \iff \operatorname{code}(K_1)=\operatorname{code}(K_2) \land \operatorname{ledger}(K_1)=\operatorname{ledger}(K_2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/CodeLedgerIdentity.same_state_iff_same_code_and_ledger` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A state pairs a canonical prime-axis coordinate with an arbitrary ledger coordinate. Its code is the positive-natural value supplied by the existing prime-axis encoding equivalence. Equality of states therefore has exactly two observable requirements: equality of the canonical codes and equality of the ledgers. The reverse implication uses injectivity of the canonical encoding, so it does not assume the identity criterion as a premise.

The pinned library was searched first for equivalence injectivity and product extensionality. It supplies Equiv.apply_eq_iff_eq, Equiv.injective, and Prod.ext_iff, but no theorem combining the repository's canonical prime-axis code with a ledger. The formal declaration is consequently a new repository-local composition of the existing encoding equivalence with generated structure constructor injectivity, matching the single criterion in the source atom.

## References

- Truth anchor: `D5/S1/Dynamics/CodeLedgerIdentity.same_state_iff_same_code_and_ledger`
- Dependency: [D5/S1/Digit/PrimeAxisEncoding](../Digit/PrimeAxisEncoding.md)
