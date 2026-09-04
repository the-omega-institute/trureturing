# Gram Realizability

## Abstract

Positive Hilbert-space operators are exactly adjoint-square Gram operators.

**Theorem 1.1 (Positivity is equivalent to a Gram factorization).**

$$\begin{aligned}\forall V: \operatorname{Hilbert}(\mathbb{C}), Q: \operatorname{B}(V),\\Q \geq 0 \Leftrightarrow \exists O: \operatorname{B}(V),\\Q = O^{*} O \land \\\forall x, y\in V, \langle Q(x), y \rangle_{\mathbb{C}} = \langle O(x), O(y) \rangle_{\mathbb{C}}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/GramRealizability.gram_realizability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a complete complex inner-product space and Q a continuous linear endomorphism of V. Positivity is understood in the standard Loewner order on bounded operators.

The source uses Q both as an operator and as a two-variable form. The formal statement resolves this ambiguity by defining the form as the inner product of Qx with y.

If Q is positive, its continuous-functional-calculus square root is a canonical witness O on V. It is self-adjoint and its square is Q. Conversely, every adjoint-square operator is positive.

Pinned Mathlib supplies the positive square-root identities and the positivity theorem for adjoint compositions; the proof uses these results directly.

## References

- Truth anchor: `D5/S3/QuantumBounds/GramRealizability.gram_realizability`
