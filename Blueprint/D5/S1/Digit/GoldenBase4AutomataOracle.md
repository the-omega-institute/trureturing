# The Base-Four Golden-Ratio Automata Oracle

## Abstract

Canonical Zeckendorf words and exact floor differences define the base-four golden-ratio DFAO specification.

**Theorem 1.1 (Successive floors decompose into quotient and exact base-four digit).**

$$\operatorname{base4Floor}(n + 1) = 4 \cdot \operatorname{base4Floor}(n) + \operatorname{base4GoldenDigit}(n).$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4AutomataOracle.base4_floor_succ_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The output digit is defined by an exact integer floor difference. A general radix-floor lemma proves that the difference lies in zero through three.

The theorem freezes the quotient-remainder identity without floating-point evaluation of the golden ratio.

**Theorem 1.2 (A finite prefix obstruction gives a global base-four state lower bound).**

$$\operatorname{NoSmallModel}(k, \operatorname{prefixSample}(N)) \land \operatorname{Fits}(M, \operatorname{spec}()) \implies k < \operatorname{card}(State).$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4AutomataOracle.base4_state_lower_bound_of_finite_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The global sample maps i to the canonical Zeckendorf word of four to the i and labels it by the exact i-th base-four digit.

Global correctness restricts to every finite prefix. The generic typed-sample theorem therefore turns any verified Fin k coloring obstruction into the strict global lower bound k < card(State).

## References

- Truth anchor: `D5/S1/Digit/GoldenBase4AutomataOracle.base4_floor_succ_decomposition`
- Truth anchor: `D5/S1/Digit/GoldenBase4AutomataOracle.base4_state_lower_bound_of_finite_obstruction`
- Dependency: [D5/S0/Automata/TypedSampleIdentification](../../S0/Automata/TypedSampleIdentification.md)
- Dependency: [D5/S0/Conventions/WDigits](../../S0/Conventions/WDigits.md)
