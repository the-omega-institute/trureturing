# Total normalization of bounded verifiers

## Abstract

Total normalization of bounded verifiers.

The raw word is saved in a disjoint frame before exact paired decoding. Malformed outer words reject. The program checks the target witness bound using the decoded target length; oversized witnesses reject. For a valid bounded pair it restores the identical original raw bytes and executes the original verifier, preserving both decisions. The resulting total polynomial tape machine accepts exactly Good, with no relaxed target certificate bound.

**Theorem 1.1 (normalize).**

$$\forall M \in \mathit{Machine},\; \forall c \in \mathit{Nat},\; \forall e \in \mathit{Nat},\; \operatorname{PolynomialTimeMachine}\left(M\right) \Rightarrow \left(\exists N \in \mathit{Machine},\; \operatorname{PolynomialTimeMachine}\left(N\right) \land \left(\forall w \in \mathit{Word},\; \operatorname{Accepts}\left(N, w\right) \Leftrightarrow \operatorname{Good}\left(M, c, e, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/BoundedVerifier.normalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* RBarish-UTokyo (2026). *NPCompleteness-Lean4 finite binary machine and composition source*. URL: <https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925>.

*Commentary.*

The raw word is saved in a disjoint frame before exact paired decoding. Malformed outer words reject. The program checks the target witness bound using the decoded target length; oversized witnesses reject. For a valid bounded pair it restores the identical original raw bytes and executes the original verifier, preserving both decisions. The resulting total polynomial tape machine accepts exactly Good, with no relaxed target certificate bound.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/BoundedVerifier.normalize`
- Dependency: [D5/S0/Computability/BinaryMachine/DecisionSimulation](DecisionSimulation.md)
- Dependency: [D5/S0/Computability/BinaryMachine/WitnessBudget](WitnessBudget.md)
