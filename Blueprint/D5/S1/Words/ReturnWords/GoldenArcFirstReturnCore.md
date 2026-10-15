# Forward displacement without wrapping

## Abstract

Fractional phases add their forward displacement when the sum stays below one.

**Theorem 1.1 (Fractional addition without wrapping).**

$$\forall alpha \in \mathrm{Real},\; \forall x \in \mathrm{Real},\; \forall k \in \mathrm{Nat},\; (0 \le x) \Rightarrow (x + \operatorname{forwardDisplacement}\left(alpha, k\right) < 1) \Rightarrow \operatorname{Int}.\operatorname{fract}\left(x + (\operatorname{Nat}.\operatorname{cast}\left(k\right) : \mathrm{Real}) \cdot alpha\right) = x + \operatorname{forwardDisplacement}\left(alpha, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.fract_add_displacement_of_no_wrap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real alpha and x and a natural k, if x is nonnegative and x plus forwardDisplacement alpha k is less than one, the fractional part of x plus k times alpha equals that sum.

## References

- Truth anchor: `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.fract_add_displacement_of_no_wrap`
