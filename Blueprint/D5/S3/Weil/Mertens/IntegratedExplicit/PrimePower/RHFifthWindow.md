# Fifth-root correction at both endpoints

## Abstract

The fifth-root coefficient in RH prime windows

**Theorem 1.1 (A uniform remainder at the third-power decay rate).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; 2 \le T \land \left(0 < K \land \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{R}\left(a, B\right) - \frac{25}{6} \cdot \left(a^{-\frac{3}{10}} - B^{-\frac{3}{10}}\right)\right| \le K \cdot \left(a^{-\frac{1}{3}} - B^{-\frac{1}{3}}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHFifthWindow.prime_window_fifth_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R(a,B) be the signed error in the cube and square correction. Start with the integral of the negative part of the prime-only tail divided by sqrt(x). Subtract 2 log(B/a), the ordinary zero primitive at B minus its value at a, the cube term, and the square-cutoff primitive at B minus its value at a. Both spectral primitives use the actual zero occurrences with multiplicity.

The Chebyshev difference after subtraction of the square, cube and fifth cutoffs is of sixth-root order by finite prime-power cancellation. After tail integration against t^(-2) and multiplication by sqrt(x), this error is of order x^(-1/3). The fifth uncentered root contributes (5/4)x^(-3/10). The centered fifth root contributes at order x^(-2/5) under RH.

Eventual positivity permits the use of the signed prime-only density. Integrating the fifth-root density on the same log interval gives 25/6 times the negative three-tenths power difference. Integrating the remaining majorant gives the negative one-third power difference. Both terms vanish at B=a.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHFifthWindow.prime_window_fifth_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHRootCorrection](RHRootCorrection.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePowerFifthCutoff](../PrimePowerFifthCutoff.md)
