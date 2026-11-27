# Pure vector states and product GNS sectors

## Abstract

The distance of two pure matrix states and the tail-product classification of qubit product representations.

The difference of the two ray projections obeys a cubic matrix identity. Its positive square root gives the trace norm. On the qubit observable algebra, finite products of local observables factor in each reference vacuum. The vacua define cyclic pure states. Finite rotations yield a common realization under summability, and finite products of vacuum projections force every intertwiner to vanish under divergence. Applying the classification to matched null-cone clock cuts requires a common model of the clock-cut algebras and their embeddings.

**Theorem 1.1 (Trace norm of a ray-projection difference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_matrix_traceNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_matrix_traceNorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

For unit vectors ψ and φ, the trace norm of their ray-projection difference is 2√(1 − |⟨ψ,φ⟩|²).

**Definition 1.2 (Matrix vector functional).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.matrixVectorState`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.matrixVectorState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The functional of a vector ψ pairs the matrix argument with the ray density of ψ by the trace.

**Theorem 1.3 (Matrix vector evaluation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.matrixVectorState_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.matrixVectorState_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The trace-pairing functional evaluates at A as the inner product ⟨ψ,Aψ⟩.

**Theorem 1.4 (Norm distance between matrix vector states).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_matrix_vectorState_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_matrix_vectorState_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

On the full matrix algebra with the operator norm, the distance of the vector states of unit ψ and φ is 2√(1 − |⟨ψ,φ⟩|²).

**Definition 1.5 (Unitary equivalence of GNS representations).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.GNSEquivalent`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.GNSEquivalent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The two completed GNS representations admit a surjective linear isometry that intertwines every observable.

**Definition 1.6 (Disjoint GNS representations).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.GNSDisjoint`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.GNSDisjoint` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Every bounded linear operator intertwining the two completed GNS representations is zero.

**Definition 1.7 (First qubit product state).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.firstProductState`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.firstProductState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The first component of the common observable algebra acts on the first vacuum, defining its normalized vector state.

**Definition 1.8 (Second qubit product state).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.secondProductState`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.secondProductState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The second component of the common observable algebra acts on the second vacuum, defining its normalized vector state.

**Theorem 1.9 (Purity of the qubit product states).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_product_states`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_product_states` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

Both product states are pure on the common norm-closed algebra generated by the paired local matrix actions.

**Theorem 1.10 (Tail-product dichotomy).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_product_gns_dichotomy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_product_gns_dichotomy` (`✓ std3`). ∎

*Citation.* Alain Guichardet (1966). *Produits tensoriels infinis et représentations des relations d’anticommutation*. DOI: [10.24033/asens.1146](https://doi.org/10.24033/asens.1146). URL: <https://doi.org/10.24033/asens.1146>.

*Commentary.*

The product GNS representations are unitarily equivalent exactly when the overlap deficits sum finitely. They are disjoint exactly when the limit of the finite products is zero for every starting site.

**Theorem 1.11 (Norm distance of product states).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_product_state_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_product_state_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The operator norm of the difference of the product state functionals is 2√(1 − p²), where p is the full overlap product. The finite tests attain the corresponding finite-product distances.

**Definition 1.12 (Even-site diagonal observables).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.evenDiagonalAlgebra`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.evenDiagonalAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The incoming algebra is the norm-closed star subalgebra generated by diagonal observables at even sites.

**Theorem 1.13 (Equivalent sectors with one orthogonal site).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.one_orthogonal_site_equivalent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.one_orthogonal_site_equivalent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The first and second states are distinct and agree on the even-site diagonal algebra. The overlap vanishes at site one and equals one elsewhere. The full product is zero, and the GNS representations are equivalent.

**Theorem 1.14 (Disjoint sectors with odd-site orthogonality).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.odd_orthogonal_sites_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.odd_orthogonal_sites_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Venkatesa Chandrasekaran (2026). *An algebraic quantization of gravity from the null cone*. URL: <https://arxiv.org/html/2611.34924v1>.

*Commentary.*

The first and second states are distinct and agree on the even-site diagonal algebra. The overlap is one at each even site and zero at each odd site, and the GNS representations are disjoint.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.GNSDisjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.GNSEquivalent`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.evenDiagonalAlgebra`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.firstProductState`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.matrixVectorState`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.matrixVectorState_apply`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.odd_orthogonal_sites_disjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.one_orthogonal_site_equivalent`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_matrix_traceNorm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_matrix_vectorState_norm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_product_gns_dichotomy`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_product_state_norm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.pure_product_states`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/PureGNSExtensionSectors.secondProductState`
- Dependency: [D5/S3/Quantum/Analysis/GNSOrderCoordinates](../GNSOrderCoordinates.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/QuantumStates/GNSCompatibleStateExtension](../../../QuantumStates/GNSCompatibleStateExtension.md)
