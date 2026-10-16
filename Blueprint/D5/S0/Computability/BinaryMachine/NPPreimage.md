# NP preimages with exact target witness bounds

## Abstract

NP preimages with exact target witness bounds.

A target verifier is normalized to enforce its original witness bound before its original decision. PairPreimage transforms only the instance; DecisionComposition preserves the complete normalized decision. The physical output bound for the reduction supplies a polynomial source witness envelope. Soundness uses the target bound checked internally, so an oversized target witness cannot become valid merely because the source envelope is larger. coNP is defined by complements of NP languages, and DP by intersections of an NP language and a coNP language.

**Theorem 1.1 (inNP_preimage).**

$$\forall A \in \mathit{Language},\; \forall f \in \mathit{WordFunction},\; \operatorname{InNP}\left(A\right) \Rightarrow \left(\operatorname{PolyTime}\left(f\right) \Rightarrow \operatorname{InNP}\left(\operatorname{preimage}\left(A, f\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/NPPreimage.inNP_preimage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

A target verifier is normalized to enforce its original witness bound before its original decision. PairPreimage transforms only the instance; DecisionComposition preserves the complete normalized decision. The physical output bound for the reduction supplies a polynomial source witness envelope. Soundness uses the target bound checked internally, so an oversized target witness cannot become valid merely because the source envelope is larger. coNP is defined by complements of NP languages, and DP by intersections of an NP language and a coNP language.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/NPPreimage.inNP_preimage`
- Dependency: [D5/S0/Computability/BinaryMachine/BoundedVerifier](BoundedVerifier.md)
- Dependency: [D5/S0/Computability/BinaryMachine/DecisionComposition](DecisionComposition.md)
- Dependency: [D5/S0/Computability/BinaryMachine/PairPreimage](PairPreimage.md)
