# Diagonal Completion Escape

## Abstract

Binary finite prefixes admit a compatible diagonal escape sequence.

**Theorem 1.1 (Diagonal escape through compatible binary prefixes).**

$$\forall x: Nat \to Nat \to Bool, (\exists d: Nat \to Bool, \exists s: \operatorname{CompatibleStageFamily}(S), (\forall n, d(n) = {if(x(n)(n)) then false else true} \land \forall n, s_{n} = P(n)(d) \land \forall i, j, h : i \leq j, \operatorname{restrict}(h)(P(j)(d)) = P(i)(d) \land \forall n, d \neq x(n))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/DiagonalEscape/DiagonalCompletionEscape.diagonal_completion_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At stage n, the binary word is a function on Fin n. The restriction channel from stage j to stage i forgets coordinates after i, and the prefix probe reads the first n entries of an infinite Boolean sequence.

For any proposed enumeration of Boolean sequences, choose the diagonal entry to be false when the enumerated sequence is true at its own coordinate, and true otherwise. The canonical completion map then packages its finite prefixes as a CompatibleStageFamily.

The resulting section satisfies every restriction equation and differs from the sequence at its self-coordinate for every enumeration index. The construction uses the source binary stages and channels rather than defining an object from the desired conclusion.

## References

- Truth anchor: `D5/S3/ObserverMemory/DiagonalEscape/DiagonalCompletionEscape.diagonal_completion_escape`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/CompletionIsomorphismCriterion](../InverseLimits/CompletionIsomorphismCriterion.md)
