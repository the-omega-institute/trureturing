# Conventional One Query Physical Protocol

## Abstract

Every raw appearing-name clause word executes one physical query and paid response recovery.

**Theorem 1.1 (Actual compiler, response writes and independent count).**

$$\forall w \in \operatorname{List}\left(\mathit{Bool}\right),\; \exists r \in \operatorname{List}\left(\mathit{ResponseSymbol}\right),\; \operatorname{queryReply}\left(\operatorname{preparedQuery}\left(\operatorname{denseOutput}\left(w\right)\right), r\right) \land \left(\operatorname{length}\left(r\right) \le 2 \cdot \left(\operatorname{length}\left(w\right)^{2} + 8 \cdot \operatorname{length}\left(w\right) + 7 + 1\right)^{2} + \operatorname{length}\left(w\right)^{2} + 8 \cdot \operatorname{length}\left(w\right) + 7 + 5 \land \left(\operatorname{msbValue}\left(\operatorname{totalPostOutput}\left(r\right)\right) = \operatorname{rawCount}\left(w\right) \land \left(\left(\exists t \in \mathit{Nat},\; t \le 80 \cdot \left(\operatorname{length}\left(w\right) + 1\right)^{2} + 20 \cdot \left(\operatorname{length}\left(w\right)^{2} + 8 \cdot \operatorname{length}\left(w\right) + 7\right)^{2} + 72 \cdot \left(\operatorname{length}\left(w\right)^{2} + 8 \cdot \operatorname{length}\left(w\right) + 7\right) + 87 \land \operatorname{BinaryProtocolRun}\left(\operatorname{prefix}\left(\operatorname{initList}\left(\mathit{queryCompiler}, w\right)\right), \operatorname{physical}\left(\operatorname{halt}\left(\operatorname{haltList}\left(\mathit{postMachine}, \operatorname{binaryWord}\left(\operatorname{totalPostOutput}\left(r\right)\right)\right)\right)\right), t, 1\right)\right) \land \left(\forall output \in \operatorname{Cfg}\left(\mathit{postMachine}\right),\; \forall t \in \mathit{Nat},\; \forall asks \in \mathit{Nat},\; \operatorname{BinaryProtocolRun}\left(\operatorname{prefix}\left(\operatorname{initList}\left(\mathit{queryCompiler}, w\right)\right), \operatorname{physical}\left(\operatorname{halt}\left(\mathit{output}\right)\right), t, \mathit{asks}\right) \Rightarrow \mathit{asks} = 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PhysicalProtocol/BinaryClauseOracleProtocol.conventional_one_query_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix executes the fixed twenty-three-stack query compiler on the actual raw conventional word. Its exact clean output is the query for the densely prepared raw clauses. The physical phase uses the positive rational whose complex value equals the full matrix exponential trace of that same Hamiltonian at inverse temperature log two, in canonical reduced bare numerator slash denominator spelling. The oracle relation contains no satisfying count or arithmetic suitability premise.

A counted suffix is extracted from the actual unary physical trace, and the compiler trace is lifted instruction by instruction. The entry transition, one distinguished Ask, symbol reads, ordinary response writes, reversal and postprocessor execution are all charged. For input length L and B equal to L squared plus eight L plus seven, the complete time is at most eighty times (L plus one) squared plus twenty B squared plus seventy-two B plus eighty-seven. The response has at most two times (B plus one) squared plus B plus five symbols.

The ordinary post output represents the independent appearing-name satisfying count. Every complete trace has exactly one Ask, including malformed source words routed through the valid zero-variable empty-clause query. All ordinary post scratch is empty and control is reset at halt. The query retains the raw physical clauses; reverse conversion tautologies are not inserted into this Hamiltonian.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PhysicalProtocol/BinaryClauseOracleProtocol.conventional_one_query_run`
- Dependency: [D5/S0/Computability/DenseQueryCompiler](../../../../S0/Computability/DenseQueryCompiler.md)
- Dependency: [D5/S3/Quantum/Dynamics/PhysicalProtocol/ClauseOracleProtocol](ClauseOracleProtocol.md)
