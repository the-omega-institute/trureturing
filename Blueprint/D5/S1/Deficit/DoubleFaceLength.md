# The Two-Face Length Spread Is sqrt(5) log n

## Abstract

The expansion-face length minus the contraction-face length is sqrt(5) times log n.

**Theorem 1.1 (The expansion-face minus contraction-face length is sqrt(5) log n).**

$$\lambda_{+}(n) - \lambda_{-}(n) = \sqrt{5} \cdot \log n$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/DoubleFaceLength.lambdaPlus_sub_lambdaMinus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The expansion-face length lambdaPlus is the prime-exponent sum of the expansion-face readings betaReal (the golden ratio phi face), the companion of dev's contraction-face length lambdaMinus built from the contraction-face readings betaContraction (the conjugate psi face). For n != 0, the two lengths differ by exactly sqrt(5) * log n: lambdaPlus n - lambdaMinus n = sqrt(5) * log n. The spread constant sqrt(5) = phi - psi is positive because the expansion face phi exceeds the contraction face psi, so the difference sqrt(5) * log n is nonnegative, vanishing exactly at n = 1 and strictly positive for n > 1.

The core is the per-exponent identity betaReal v - betaContraction v = sqrt(5) * v: the expansion minus contraction face of the golden integer betaGolden v, whose phi-coordinate is v, equals (2 phi - 1) v = sqrt(5) v. Lifting this through the prime factorization and summing the exponent-weighted logarithms recovers sqrt(5) * log n.

This is the two-face spread of Theorem 6.47's two closed forms lambdaPlus(n) = log n_S - psi * log n and lambdaMinus(n) = log n_S - phi * log n: subtracting them cancels the hidden-face product n_S. Only the difference identity is recorded, together with the missing companion definition lambdaPlus. The individual closed forms relating each face to the hidden-face product n_S = prod_p p^(S(v_p)), the bound |lambdaMinus| <= (1/phi) * log rad(n), and the displacement surface D(s,w) of the source are not covered.

## References

- Truth anchor: `D5/S1/Deficit/DoubleFaceLength.lambdaPlus_sub_lambdaMinus`
