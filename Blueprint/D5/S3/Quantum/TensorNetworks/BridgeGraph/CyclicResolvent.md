# CyclicResolvent

## Abstract

CyclicResolvent supplies the width-three bridge max-flow proof.

Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.

**Definition 1.1 (inclusion).**

$$\forall (m : Type) (n : Type) [DecidableEq m] (e : n \to m) , \operatorname{CyclicResolvent.inclusion} e = (\operatorname{Matrix.submatrix} 1 id e)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent.inclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

inclusion is the matrix that inserts coordinates along a map e, with entry one when the row index equals e of the column index; inclusion_injective recovers the original vector at these rows when e is injective.

**Theorem 1.2 (inclusion_injective).**

$$\forall \{m : Type\} \{n : Type\} [Fintype n] [DecidableEq m] (e : n \to m) , \operatorname{Function.Injective} e \to \operatorname{Function.Injective} (\operatorname{CyclicResolvent.inclusion} e) . mulVec$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent.inclusion_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective index map induces an injective coordinate-insertion map; schur_injective uses this to recover the input vector after its inserted image vanishes.

**Theorem 1.3 (cyclic_resolvent_lemma).**

$$\operatorname{FloorSelectorCycles.CyclicResolventLemma}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent.cyclic_resolvent_lemma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 < B ≤ A, 0 < D ≤ G and κ > 0, the reservoir is invertible and schurMap is injective when A*D ≤ B*G and surjective when B*G ≤ A*D; ReservoirSchur.short_short_injective_witness uses the invertibility to eliminate the reservoir variables.

**Theorem 1.4 (schur_rank).**

$$\forall (A B G D : \mathbb{N}) , 0 < B \to B \leq A \to 0 < D \to D \leq G \to \forall (\kappa : \mathbb{Q}) , 0 < \kappa \to (\operatorname{FloorSelectorCycles.schurMap} A B G D \kappa) . rank = min (A \cdot D) (B \cdot G)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent.schur_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 < B ≤ A, 0 < D ≤ G and κ > 0, schurMap has rank min(A*D,B*G); ShiftPencilBlocks.short_short_cyclic_schur_rank applies this at κ=p to compute the short reservoir Schur complement.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent.cyclic_resolvent_lemma`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent.inclusion`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent.inclusion_injective`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent.schur_rank`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles](FloorSelectorCycles.md)
