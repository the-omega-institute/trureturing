# One Query Operational Protocol

## Abstract

Actual preprocessing, one physical ask, paid response writes and postprocessing.

**Theorem 1.1 (All-input execution with exactly one ask and a direct quadratic clock).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \exists r \in \operatorname{List}\left(\mathit{ResponseSymbol}\right),\; \operatorname{queryReply}\left(\operatorname{preparedQuery}\left(w\right), r\right) \land \left(\operatorname{length}\left(r\right) \le 2 \cdot \left(\operatorname{length}\left(w\right) + 1\right)^{2} + \operatorname{length}\left(w\right) + 5 \land \left(\operatorname{msbValue}\left(\operatorname{totalPostOutput}\left(r\right)\right) = \operatorname{satisfyingCount}\left(\operatorname{snd}\left(\operatorname{preparedFormula}\left(w\right)\right)\right) \land \left(\left(\exists t \in \mathit{Nat},\; t \le 16 \cdot \operatorname{length}\left(w\right)^{2} + 50 \cdot \operatorname{length}\left(w\right) + 71 \land \operatorname{ProtocolRun}\left(\operatorname{pre}\left(\operatorname{initList}\left(\mathit{preMachine}, w\right)\right), \operatorname{halt}\left(\operatorname{haltList}\left(\mathit{postMachine}, \operatorname{binaryWord}\left(\operatorname{totalPostOutput}\left(r\right)\right)\right)\right), t, 1\right)\right) \land \left(\forall o \in \operatorname{Cfg}\left(\mathit{postMachine}\right),\; \forall t \in \mathit{Nat},\; \forall asks \in \mathit{Nat},\; \operatorname{ProtocolRun}\left(\operatorname{pre}\left(\operatorname{initList}\left(\mathit{preMachine}, w\right)\right), \operatorname{halt}\left(o\right), t, \mathit{asks}\right) \Rightarrow \mathit{asks} = 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PhysicalProtocol/ClauseOracleProtocol.one_query_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every raw Boolean source word, the actual pre-machine emits the decoded physical query or the valid zero-variable one-empty-clause fallback. The ask relates its whole decoded query to a positive reduced rational whose complex cast equals the full physical trace. That relation contains no satisfying-count premise.

The ask exposes a read-only external stream while ordinary writable response stacks are empty. Each symbol is read into finite control in one transition, then written by the fixed materialization machine in a separate actual transition. A real reversal puts the response on the post input stack. The handoff preserves all those stack contents and changes only the fixed control and label.

The response length is at most twice (L plus one) squared plus L plus five. The complete run uses at most sixteen L squared plus fifty L plus seventy-one transitions. Its final configuration is the exact clean post halt for the canonical binary count. Every complete run has exactly one ask, including malformed sources. The count is over the decoded explicit variable universe; conventional appearing-name word conversion is separate.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PhysicalProtocol/ClauseOracleProtocol.one_query_run`
- Dependency: [D5/S0/Computability/ClausePreprocessorRefinement](../../../../S0/Computability/ClausePreprocessorRefinement.md)
- Dependency: [D5/S3/Quantum/Dynamics/PhysicalProtocol/PhysicalRationalResponse](PhysicalRationalResponse.md)
