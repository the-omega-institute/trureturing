# Finite Zeckendorf Euler Identity

## Abstract

Bounded Zeckendorf names enumerate an initial Fibonacci interval and its finite Euler sum.

**Theorem 1.1 (Finite Zeckendorf names give the complete Fibonacci interval).**

$$\begin{gathered}\forall Q: \mathbb{N},\\{}\text{let } E_{Q}: \operatorname{GoldenName}\left(Q\right) \to \operatorname{Fin}\left(\operatorname{Fib}\left(Q + 2\right)\right) := (eta: \operatorname{GoldenName}\left(Q\right) \mapsto \sum_{k \in eta} \operatorname{Fib}\left(k\right));\\{}\operatorname{Bijective}\left(E_{Q}\right) \land\\{}\forall x: \mathbb{R}, \lvert x \rvert < 1 \Rightarrow\\{}\sum_{eta \in \operatorname{GoldenName}\left(Q\right)} x^{(E_{Q}(eta) : \mathbb{N})} = \sum_{e \in \operatorname{Fin}\left(\operatorname{Fib}\left(Q + 2\right)\right)} x^{e} \land\\{}\sum_{e \in \operatorname{Fin}\left(\operatorname{Fib}\left(Q + 2\right)\right)} x^{e} = \frac{1 - x^{\operatorname{Fib}\left(Q + 2\right)}}{1 - x}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/FiniteZeckendorfEulerIdentity.finite_zeckendorf_interval_and_euler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

GoldenName(Q) is the canonical carrier of admissible occupied indices from two through Q+1. Thus Q=N-1 relative to the source notation, and the source endpoint Fib(N+1) is Fib(Q+2).

The displayed exponent is constructed directly by summing the occupied Fibonacci weights. The proof identifies this source-defined map with the inverse of the existing canonical golden-name equivalence.

Reindexing the finite sum through that equivalence gives the initial-interval sum. The source-wide bound |x|<1 supplies x != 1 for the quotient form of the finite geometric series.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/FiniteZeckendorfEulerIdentity.finite_zeckendorf_interval_and_euler`
- Dependency: [D5/S0/Tower/GoldenNames](../../../S0/Tower/GoldenNames.md)
