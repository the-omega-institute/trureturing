# LongReservoir

## Abstract

LongReservoir supplies the width-three bridge max-flow proof.

Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.

**Theorem 1.1 (base_witness).**

$$\operatorname{QuantumMaxFlowBound.BaseWitness}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/LongReservoir.base_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every strict base pair admits rational three-slice matrices attaining the outer cut. A shift pencil with κ=p couples short and long blocks to a cyclic reservoir.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/LongReservoir.base_witness`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/ReservoirSchur](ReservoirSchur.md)
