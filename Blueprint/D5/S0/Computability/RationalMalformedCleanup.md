# Rational Response Error Cleanup

## Abstract

Arbitrary response-error stacks reach the exact clean one-zero terminal state.

**Theorem 1.1 (Arbitrary scratch contents and linear physical erasure).**

$$\forall st \in \mathit{PostControl},\; \forall input \in \operatorname{List}\left(\mathit{ResponseSymbol}\right),\; \forall quotient \in \operatorname{List}\left(\mathit{ResponseSymbol}\right),\; \forall shifts \in \operatorname{List}\left(\mathit{ResponseSymbol}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{postMachine}\right), \operatorname{postCfg}\left(\mathit{badInput}, \mathit{st}, \mathit{input}, \mathit{quotient}, \mathit{shifts}, \mathit{nil}\right), \operatorname{some}\left(\operatorname{haltList}\left(\mathit{postMachine}, \operatorname{singleton}\left(\mathit{zero}\right)\right)\right), \operatorname{length}\left(\mathit{input}\right) + \operatorname{length}\left(\mathit{quotient}\right) + \operatorname{length}\left(\mathit{shifts}\right) + 3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/RationalMalformedCleanup.post_error_cleanup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At badInput, the finite control and the input, quotient and shift stacks may contain arbitrary ternary words. The output stack is initially empty. Three actual draining passes erase all remaining symbols, write one zero, reset the control and halt with all scratch empty. The bound is the three initial lengths plus three.

This theorem starts at error entry. The whole-word refinement establishes which parser branches reach that entry. No physical oracle or SAT count occurs in this cleanup statement.

## References

- Truth anchor: `D5/S0/Computability/RationalMalformedCleanup.post_error_cleanup`
- Dependency: [D5/S0/Computability/RationalPostprocessor](RationalPostprocessor.md)
