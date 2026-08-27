# Finite Internal Protocol Obstruction

## Abstract

Finite internal protocol indexing cannot realize every response table.

**Theorem 1.1 (Finite internal protocol indexing is not response complete).**

$$\begin{gathered}\forall X, P, Lambda: \operatorname{Type},\\{}[\operatorname{Fintype} X] [\operatorname{Fintype} P] [\operatorname{Fintype} Lambda],\\{}e: X \to P \to Lambda,\\{}(2 \leq \operatorname{card}\left(Lambda\right) \land \operatorname{card}\left(P\right) \leq \operatorname{card}\left(X\right)) \Rightarrow\\{}(\operatorname{card}\left(X\right) < \operatorname{card}\left(Lambda\right)^{\operatorname{card}\left(X\right)}) \land\\{}\neg(\forall f: X \to Lambda, \exists p: P, \forall x: X, \operatorname{e}\left(x, p\right) = \operatorname{f}\left(x\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/FiniteInternalProtocolNoGo.finite_internal_protocol_no_go` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evaluation channel sends each protocol to its complete response table on the state carrier. Response completeness would make this map surjective onto all Lambda-valued tables.

There are card(Lambda)^card(X) such tables. With at least two responses this is strictly larger than card(X), while internal indexing allows at most card(X) protocols, contradicting surjectivity.

The source assumes a nonempty state carrier. The machine theorem is stronger and also proves the empty-carrier case, so that premise is not needed.

## References

- Truth anchor: `D5/S3/Observer/Budget/FiniteInternalProtocolNoGo.finite_internal_protocol_no_go`
