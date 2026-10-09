# CastlingDeficit

## Abstract

CastlingDeficit supplies the width-three bridge max-flow proof.

Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.

**Theorem 1.1 (castling_proved).**

$$\operatorname{QuantumMaxFlowBound.Castling}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/CastlingDeficit.castling_proved` (`✓ std3`). ∎

*Citation.* Fulvio Gesmundo; Vladimir Lysikov; Vincent Steffan (2025). *Quantum max-flow in the bridge graph*. DOI: [10.1007/s00031-024-09863-2](https://doi.org/10.1007/s00031-024-09863-2). URL: <https://arxiv.org/abs/2212.09794v2>.

*Commentary.*

The width-three castling deficit identity is proved by common kernels and annihilator complements over a field, then applied to complex maximizing assignments. The proof does not assume the source Theorem 3.1.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/CastlingDeficit.castling_proved`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound](QuantumMaxFlowBound.md)
