# Golden-Ratio DFAO Minimality Targets

## Abstract

M07-M16 register exact finite-prefix LRAT targets for the golden-ratio DFAO controls and the base-4 state-exclusion ladder.

**Theorem 1.1 (The registered problem uses the exact frozen oracle).**

$$\operatorname{input}(P, i) = \operatorname{W}(4^{i}) \land \operatorname{target}(P, i) = \lfloor4^{i+1}\cdot\varphi\rfloor-4\cdot\lfloor4^{i}\cdot\varphi\rfloor$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenDFAOMinimalityTargets.base4_problem_semantics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The registered sparse input at index i is definitionally the canonical most-significant-digit-first Zeckendorf word of four to the i, and the registered target output equals the exact golden-ratio floor difference certified by the frozen base-4 oracle layer.

**Theorem 1.2 (A verified upper machine and the M16 refutation imply exact minimality).**

$$\operatorname{HasGlobalModel}(P, 22) \land \operatorname{Refutation}(\operatorname{formula}(E)) \implies \operatorname{IsMinimalStateCount}(P, 22)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenDFAOMinimalityTargets.phi_base4_twenty_two_state_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The terminal theorem consumes two independent evidence objects: a globally correct twenty-two-state typed machine and a certified finite-prefix LRAT refutation of every machine using at most twenty-one states.

The theorem is a certificate eliminator. It does not assert that either external evidence object has already been constructed or checked.

## References

- Truth anchor: `D5/S1/Digit/GoldenDFAOMinimalityTargets.base4_problem_semantics`
- Truth anchor: `D5/S1/Digit/GoldenDFAOMinimalityTargets.phi_base4_twenty_two_state_minimality`
- Dependency: [D5/S0/Certificates/LRATDFAStateLowerBound](../../S0/Certificates/LRATDFAStateLowerBound.md)
- Dependency: [D5/S1/Digit/GoldenBase4AutomataOracle](GoldenBase4AutomataOracle.md)
