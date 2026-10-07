# Paid Dense Physical Query Compiler

## Abstract

A fixed finite compiler executes dense naming and pays for every transfer into physical query construction.

**Theorem 1.1 (Actual complete word execution and independent count).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \operatorname{Nonempty}\left(\operatorname{EvalsToInTime}\left(\operatorname{step}\left(\mathit{queryCompiler}\right), \operatorname{initList}\left(\mathit{queryCompiler}, w\right), \operatorname{some}\left(\operatorname{haltList}\left(\mathit{queryCompiler}, \operatorname{preparedQuery}\left(\operatorname{denseOutput}\left(w\right)\right)\right)\right), 80 \cdot \left(\operatorname{length}\left(w\right) + 1\right)^{2} + 4 \cdot \left(\operatorname{length}\left(w\right)^{2} + 8 \cdot \operatorname{length}\left(w\right) + 7\right)^{2} + 22 \cdot \left(\operatorname{length}\left(w\right)^{2} + 8 \cdot \operatorname{length}\left(w\right) + 7\right) + 15\right)\right) \land \left(\operatorname{readWord}\left(\mathit{true}, \operatorname{preparedQuery}\left(\operatorname{denseOutput}\left(w\right)\right)\right) = \operatorname{some}\left(\operatorname{densePrepared}\left(w\right)\right) \land \operatorname{unaryCount}\left(\operatorname{snd}\left(\operatorname{densePrepared}\left(w\right)\right)\right) = \operatorname{rawCount}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DenseQueryCompiler.dense_query_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiler has twenty-three Boolean stacks and fixed finite labels and control. It translates every instruction of the actual dense converter and unary preprocessor. When the dense program finishes, two ordinary transfer loops move the output into the preprocessor input, charging twice the output length plus two transitions. All intermediate source, dictionary, saved, and query stacks are empty at the exact clean halt.

For raw source length L and B equal to L squared plus eight L plus seven, the direct clock is eighty times (L plus one) squared plus four B squared plus twenty-two B plus fifteen. The returned whole word decodes as a physical query for precisely the densely prepared raw clause family. Its ordinary explicit-universe count equals the conventional appearing-name count, which is defined independently of the Hamiltonian and oracle.

Every malformed word reaches the valid zero-variable one-empty-clause query. The same query can follow a valid empty-clause source, so validation follows the decoder rather than equality with the dummy word. The theorem proves query construction and paid ordinary execution; the physical response and distinguished Ask are supplied by the separate physical protocol.

## References

- Truth anchor: `D5/S0/Computability/DenseQueryCompiler.dense_query_run`
- Dependency: [D5/S0/Computability/ClausePreprocessorRefinement](ClausePreprocessorRefinement.md)
- Dependency: [D5/S0/Computability/DenseClauseConversion](DenseClauseConversion.md)
