# Involution Decomposition

## Abstract

Every real-linear involution splits each vector into fixed and negated parts.

**Theorem 1.1 (Every vector splits into even and odd parts).**

$$\forall V, reverse, x,\ reverse \circ reverse = id, even = \frac{x + reverse(x)}{2}, odd = \frac{x - reverse(x)}{2}, x = even + odd \land reverse(even) = even \land reverse(odd) = -odd.$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/InvolutionDecomposition.involution_even_odd_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let reverse be a real-linear map whose square is the identity. For any vector x, the even part is one half of x plus reverse x, and the odd part is one half of x minus reverse x. Their sum is x; reverse fixes the even part and negates the odd part.

Pinned Mathlib was searched first. LinearEquiv.ofInvolutive packages an involutive linear map as an equivalence, while no general even-odd decomposition theorem was found. The proof uses the standard linear-map addition, subtraction, and scalar-preservation laws together with the involution hypothesis.

This is a continuation partial closure restricted to the algebraic reversal decomposition clause. The weighted integrals, trace-state vanishing, equilibrium-state arrow, fluctuation law, negative-power extension, and even-power cone selection remain unresolved.

## References

- Truth anchor: `D5/S0/Conventions/InvolutionDecomposition.involution_even_odd_decomposition`
