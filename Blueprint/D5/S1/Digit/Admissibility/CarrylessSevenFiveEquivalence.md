# Seven and Five Carryless Multiplier Equivalence

## Abstract

Seven and five define equivalent ordinary versus binary carryless multiplier conditions.

All variables range over the natural numbers, including zero. C(u,k) denotes binary coefficient convolution over GF(2): its bit of degree t is the parity of the sum of bit(u,i) times bit(k,t-i) for 0 <= i <= t. Multiplication outside C is ordinary natural-number multiplication.

**Theorem 1.1 (The two equations agree).**

$$\forall k \in Nat,\; 7 \cdot k = C\left(11, k\right) \Leftrightarrow 5 \cdot k = C\left(13, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/CarrylessSevenFiveEquivalence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antti Karttunen (2025). *OEIS A115770: seven and five versus binary carryless multiplication*. URL: <https://oeis.org/A115770>.

*Commentary.*

A state consists of the ordinary multiplication carry and the remaining exclusive-OR mask, or a rejecting state. Starting from the pair of zero carries and zero masks, fifteen paired states are closed under reading either binary digit from least to most significant. At every pair, the two equations have the same truth value when the remaining input is zero. The digit-step equivalence and binary induction give the equivalence for every natural input. Thus the finite relation establishes an unbounded statement; at zero, both equations are zero equals zero.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/CarrylessSevenFiveEquivalence.result`
- Dependency: [D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence](CarrylessMultiplierEquivalence.md)
