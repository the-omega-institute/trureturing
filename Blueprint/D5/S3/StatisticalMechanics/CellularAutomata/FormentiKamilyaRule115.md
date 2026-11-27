# Question 1 for RESOCA 115 on the integer line

## Abstract

Nine-step returns in finite RESOCA 115 configurations are already three-step returns.

**Theorem 1.1 (Nine-step returns from two finitely supported layers).**

$$\forall s : \operatorname{Config}, \operatorname{Set.Finite}(\{i \in \mathbb{Z} \mid s_{1}(i) = \operatorname{true} \lor s_{2}(i) = \operatorname{true}\}) \implies \operatorname{step}^{9}(s) = s \implies \operatorname{step}^{3}(s) = s$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.returns_three_of_returns_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Enrico Formenti, Supreeti Kamilya (2026). *The Curious Case of Reversible Elementary Second Order Cellular Automaton 115*. DOI: [10.4204/EPTCS.445.12](https://doi.org/10.4204/EPTCS.445.12). URL: <https://arxiv.org/abs/2606.13159v1>.

*Commentary.*

The state is the ordered pair of past and current Boolean layers on the integer line. Equation (1) on printed p. 96 gives the global reversible update. The new past layer is the old current layer. The new current bit at site i is b(i) XOR (NOT c(i) OR (c(i−1) AND NOT c(i+1))), using the elementary local rule in Table 1 on p. 97. The formula uses s₁ and s₂ for the past and current layers, respectively. The hypothesis is finiteness of the union of the two initial supports and equality of the full state after nine steps.

Radius-one propagation gives the three-phase background on both spatial tails. At time n it applies outside the initial support bound enlarged by n. Encode each nine-periodic time column as a nine-bit mask. The kernel checks 31 candidate masks, 40 forward-reachable pairs and 52 forward edges, then 3 returning pairs and 5 returning edges. Closure from the left background and predecessor closure from the right background apply along arbitrary integer segments. Every surviving column is invariant under time shift three. The nine-return hypothesis supplies the temporal wraparound for both layers, giving the three-step return. The finite enumeration bounds the time-column graph and applies to arbitrary finite spatial widths.

**Theorem 1.2 (Least period nine is impossible).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.result` (`✓ std3`). ∎

*Resolves.* `Problems/formenti-kamilya-2026-resoca-115-question-1` (refuted) by `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"formenti-kamilya-2026-resoca-115-question-1","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Enrico Formenti, Supreeti Kamilya (2026). *The Curious Case of Reversible Elementary Second Order Cellular Automaton 115*. DOI: [10.4204/EPTCS.445.12](https://doi.org/10.4204/EPTCS.445.12). URL: <https://arxiv.org/abs/2606.13159v1>.

*Commentary.*

Question 1 on printed p. 97 asks ‘For RESOCA 115, in the context of finite configurations, are all multiple of 3 periods?’ The claim requires a configuration for every positive multiple p of three, both initial layers finitely supported, with a p-step return and no earlier positive return. At p = 9 the preceding theorem forces a return at 3, contradicting least period nine.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.returns_three_of_returns_nine`
