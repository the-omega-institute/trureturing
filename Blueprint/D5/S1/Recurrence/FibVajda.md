# Vajda's Fibonacci Identity

## Abstract

Vajda's identity relates shifted Fibonacci products over the integers.

**Theorem 1.1 (Vajda's identity).**

$$F_{n+i}F_{n+j} - F_n F_{n+i+j} = (-1)^n F_i F_j$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FibVajda.fib_vajda` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural indices n, i, and j, the difference between the two shifted Fibonacci products F_(n+i)F_(n+j) and F_nF_(n+i+j) equals (-1)^n F_iF_j. All terms are interpreted in the integers.

## References

- Truth anchor: `D5/S1/Recurrence/FibVajda.fib_vajda`
