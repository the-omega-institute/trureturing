# Odd Squares Modulo Eight

## Abstract

Every odd natural number has square congruent to one modulo eight.

**Theorem 1.1 (Eight divides an odd square minus one).**

$$\forall T \in \mathbb{N}, \operatorname{Odd}(T) \Rightarrow 8 \mid T^{2} - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/OddSquareModuloEight.eight_dvd_odd_square_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If T is odd, its square differs from one by a multiple of eight. Pinned Mathlib supplies the exact theorem Nat.eight_dvd_sq_sub_one_of_odd, so the Lean declaration is a thin wrapper rather than a second proof of the parity argument.

This closes only the explicit divisibility clause in residual appendix E.115. It does not formalize the eta-multiplier branch formulas or the subsequent context-dependent assertion that quantities A and C are even.

## References

- Truth anchor: `D5/S3/Arith/Congruence/OddSquareModuloEight.eight_dvd_odd_square_sub_one`
