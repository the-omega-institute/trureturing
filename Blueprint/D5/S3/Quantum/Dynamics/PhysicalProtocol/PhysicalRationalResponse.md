# Physical Rational Responses

## Abstract

The full complex partition has one reduced positive binary rational response.

**Theorem 1.1 (Unique ordinary response, length and actual count recovery).**

$$\forall n \in \mathit{Nat},\; \forall F \in \operatorname{Formula}\left(n\right),\; \exists w \in \operatorname{List}\left(\mathit{ResponseSymbol}\right),\; \operatorname{PhysicalReply}\left(F, w\right) \land \left(\left(\forall v \in \operatorname{List}\left(\mathit{ResponseSymbol}\right),\; \operatorname{PhysicalReply}\left(F, v\right) \Rightarrow v = w\right) \land \left(\operatorname{length}\left(w\right) \le n + 2 \cdot \left(n + 1\right) \cdot \operatorname{length}\left(F\right) + 5 \land \left(\operatorname{suitableResponse}\left(w\right) \land \left(\operatorname{Nonempty}\left(\operatorname{TM2OutputsInTime}\left(\mathit{postMachine}, w, \operatorname{some}\left(\operatorname{binaryWord}\left(\operatorname{totalPostOutput}\left(w\right)\right)\right), 3 \cdot \operatorname{length}\left(w\right) + 10\right)\right) \land \operatorname{msbValue}\left(\operatorname{totalPostOutput}\left(w\right)\right) = \operatorname{satisfyingCount}\left(F\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PhysicalProtocol/PhysicalRationalResponse.physical_reply_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

PhysicalReply relates a response word to a positive rational whose complex cast equals the full matrix exponential trace at beta log two. The word is the ordinary binary numerator, a slash, and the binary denominator of the reduced rational. The denominator one is written explicitly. This relation contains no counting or dyadic premise.

For every raw clause family over n declared variables, normalization of the actual trace yields one such word. Its length is at most n plus twice (n plus one) times the number of clauses plus five. Divisibility by three and a dyadic denominator follow from the trace and reducedness. The fixed postprocessor reaches its exact clean output in at most three times the response length plus ten steps, and that output denotes the independently defined satisfying count.

The construction includes zero variables, empty formulas and clauses, unused variables, repetitions and tautologies. Arithmetic suitability alone does not assert that a word is a physical response.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PhysicalProtocol/PhysicalRationalResponse.physical_reply_run`
- Dependency: [D5/S0/Computability/RationalResponseRefinement](../../../../S0/Computability/RationalResponseRefinement.md)
- Dependency: [D5/S3/Quantum/Dynamics/ClauseHamiltonian](../ClauseHamiltonian.md)
