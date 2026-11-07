# Bose adaptation and closedness of actual DPS cones

## Abstract

Bose adaptation and closedness of actual DPS cones

Britz-Laurent equations (25)-(31) use a Bose leaf-projector sandwich, unnormalized partial trace, and leaf cuts. The definitions here quantify all leaf subsets, with exact equivalences to the ordinary prefix and adapted half-prefix conventions. Complementary cuts account for the root. The support argument is due to Hansenne-Xu-Kraft-Guehne; the equality application note has byline Haobo Ma then Wenlin Zhang.

**Definition 1.1 (OrdinaryWitness).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.OrdinaryWitness`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.OrdinaryWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One actual root-leaf marginal is prescribed; the leaf-projector sandwich and positivity at every leaf-only cut are imposed. The empty cut supplies ordinary positivity.

**Definition 1.2 (AdaptedWitness).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.AdaptedWitness`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.AdaptedWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The witness is supported by the full symmetric projector, has the prescribed ordered marginal, and is positive at every cut, including both endpoints.

**Definition 1.3 (ordinaryDPS).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.ordinaryDPS`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.ordinaryDPS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the set of inputs possessing the actual ordinary tensor witness. No trace normalization is imposed.

**Definition 1.4 (adaptedDPS).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.adaptedDPS`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.adaptedDPS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the set of inputs possessing the actual full-Bose tensor witness. No trace normalization is imposed.

**Theorem 1.5 (adapted iff ordinary).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.adapted_iff_ordinary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.adapted_iff_ordinary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any pair-Bose-supported input, the ordinary and adapted predicates select the same individual E. Complementary cuts account for cuts containing the root. Zero and singular matrices remain in scope.

**Theorem 1.6 (adapted eq inter).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.adapted_eq_inter`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.adapted_eq_inter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual adapted cone equals the ordinary cone intersected with the positive symmetric-support face, for arbitrary finite register and local-label types with two distinct selected registers.

**Theorem 1.7 (ordinary closed).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.ordinary_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.ordinary_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a convergent sequence of inputs, every positive lift has trace equal to its input trace. The existing PSD entry bound therefore bounds the lifts. A convergent lift subsequence preserves the leaf sandwich, prescribed marginal, and every cut inequality, proving closedness of the projected cone.

For the ordinary witness, permutations fixing the root carry any two leaf cuts of equal cardinality to one another. The leaf-projector sandwich supplies the required conjugation invariance, and positive semidefiniteness transports through the corresponding computational-basis submatrix.

For registers 0 through t with root 0, choosing k equal to the cardinality of a leaf cut identifies every leaf-only positivity condition with the first k leaves. The prescribed ordered marginal and the unnormalized scale are unchanged.

For a full Bose-supported positive operator, arbitrary register permutations carry cuts of equal cardinality, including cuts containing the root. The complementary-cut transpose reduces the remaining cuts to the first k leaves for k at most floor((t+1)/2), while empty and full cuts remain explicit.

These cardinality transports are the complete ordinary and adapted DPS prefix conventions used by the application; they retain zero and singular matrices and impose no trace normalization.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.AdaptedWitness`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.OrdinaryWitness`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.adaptedDPS`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.adapted_eq_inter`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.adapted_iff_ordinary`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.ordinaryDPS`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS.ordinary_closed`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseRootTranspose](BoseRootTranspose.md)
- Dependency: [D5/S3/Quantum/Measurement/IncoherentCone](../../Measurement/IncoherentCone.md)
