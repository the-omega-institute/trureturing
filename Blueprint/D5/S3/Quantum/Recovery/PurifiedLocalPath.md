# PurifiedLocalPath

## Abstract

For every finite local protocol with a nonempty finite holder set and a finite spectator, with independent mixed local ancillas, internally constructed spectral local purifications reproduce the original initialization on every matrix. Every observed path has an exact holder-local product factorization with explicit inaccessible-register regrouping, isometric root maps, the accumulated local recurrence and inactive identity coordinate equivalences.

**Theorem 1.1 (purified local path bridge).**

Lean statement: `D5/S3/Quantum/Recovery/PurifiedLocalPath.purified_local_path_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PurifiedLocalPath.purified_local_path_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite local protocol with a nonempty finite holder set and a finite spectator, with independent mixed local ancillas, internally constructed spectral local purifications reproduce the original initialization on every matrix. Every observed path has an exact holder-local product factorization with explicit inaccessible-register regrouping, isometric root maps, the accumulated local recurrence and inactive identity coordinate equivalences.

**Definition 1.2 (original-input effect laws).**

Lean statement: `D5/S3/Quantum/Recovery/PurifiedLocalPath.InputEffectTreeLaws`

*Formalization.* `D5/S3/Quantum/Recovery/PurifiedLocalPath.InputEffectTreeLaws` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate specifies root local and product identities, positive Gram effects, actor child sums, unchanged inactive factors, full descendant completeness and the complex source-entry formula for every finite index and every complex matrix. It is a proved conclusion of actual_shared_label_support_rigidity, not a physical bridge assumed by that theorem. Product effects describe true histories; coarse label sums need not be products.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PurifiedLocalPath.InputEffectTreeLaws`
- Truth anchor: `D5/S3/Quantum/Recovery/PurifiedLocalPath.purified_local_path_bridge`
- Dependency: [D5/S3/Quantum/Recovery/RetainedLocalProtocol](RetainedLocalProtocol.md)
