# Total Clause Machine Clock

## Abstract

Every raw Boolean word has a polynomial actual run to a clean terminal configuration.

**Theorem 1.1 (All raw words, exact clean halt and written-output growth).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \exists out \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{TM2OutputsInTime}\left(\mathit{preMachine}, w, \operatorname{some}\left(\mathit{out}\right), \left(4 \cdot \operatorname{length}\left(w\right) + 20\right) \cdot \operatorname{length}\left(w\right) + 13\right)\right) \land \operatorname{length}\left(\mathit{out}\right) \le \left(\left(4 \cdot \operatorname{length}\left(w\right) + 20\right) \cdot \operatorname{length}\left(w\right) + 13\right) \cdot \operatorname{programPushBound}\left(\operatorname{m}\left(\mathit{preMachine}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/ClausePreprocessorClock.pre_total_clock` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean input word of length L, the fixed five-stack machine reaches an exact clean haltList configuration in at most (4L plus 20)L plus 13 actual transitions. All input and work stacks are empty and the finite control is reset.

The decreasing clock assigns input symbols credit 4L plus 20, backup symbols credit three and query symbols credit one. Header symbols have credit five during coefficient copying and credit one during restoration. Phase constants pay for transitions without an input pop. The remaining input, header and scratch lengths always sum to at most L.

Each executed step decreases this clock, including malformed cleanup, coefficient copying, index restoration and output reversal. Strong induction constructs the run. The output length is bounded by the transition bound times the fixed program push bound. This proves termination and writing cost; the identity of the output is a separate word refinement.

## References

- Truth anchor: `D5/S0/Computability/ClausePreprocessorClock.pre_total_clock`
- Dependency: [D5/S0/Computability/ClauseQueryPreprocessor](ClauseQueryPreprocessor.md)
