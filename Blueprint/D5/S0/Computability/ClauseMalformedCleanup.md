# Clause Machine Error Cleanup

## Abstract

Error cleanup returns the zero-variable, one-empty-clause query descriptor.

**Theorem 1.1 (All stack contents, exact clean halt and linear cleanup time).**

$$\forall st \in \mathit{PreControl},\; \forall input \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall header \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall scratch \in \operatorname{List}\left(\mathit{Bool}\right),\; \forall query \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{preMachine}\right), \operatorname{preCfg}\left(\mathit{badInput}, \mathit{st}, \mathit{input}, \mathit{header}, \mathit{scratch}, \mathit{query}, \mathit{nil}\right), \operatorname{some}\left(\operatorname{haltList}\left(\mathit{preMachine}, \mathit{dummyQuery}\right)\right), \operatorname{length}\left(\mathit{input}\right) + \operatorname{length}\left(\mathit{header}\right) + \operatorname{length}\left(\mathit{scratch}\right) + \operatorname{length}\left(\mathit{query}\right) + 5\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/ClauseMalformedCleanup.pre_error_cleanup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From error entry, every finite control state and all arbitrary Boolean input, header, scratch and partial-query words are included, with the output stack initially empty. The actual fixed machine drains those four stacks, writes the dummy query, resets its control to the initial state and reaches the exact haltList configuration.

The transition bound is the sum of the four initial stack lengths plus five. Each pop removes one real symbol. Four empty-stack transitions select the next cleanup phase, and the final fixed statement writes the complete dummy word.

The dummy word describes zero hidden variables and one empty raw clause. This result proves cleanup from error entry. The separate parser-to-error-entry run and its complete polynomial bound are required for universal malformed-source correctness.

## References

- Truth anchor: `D5/S0/Computability/ClauseMalformedCleanup.pre_error_cleanup`
- Dependency: [D5/S0/Computability/ClauseQueryPreprocessor](ClauseQueryPreprocessor.md)
