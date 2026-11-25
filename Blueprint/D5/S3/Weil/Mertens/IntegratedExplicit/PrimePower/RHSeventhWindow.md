# The signed sixth and seventh terms and the cube-cutoff primitive

## Abstract

The seventh-root correction in RH prime windows

Let R5(a,B) be the signed remainder after the corrections through the fifth root. From the integral of max(-Qtheta(x),0)/sqrt(x) on [a,B], subtract 2 log(B/a), the ordinary spectral primitive at B minus its value at a, the cube main term 9 times the negative one-sixth power difference, the square primitive at B minus its value at a, and 25/6 times the negative three-tenths power difference. Here Qtheta is the prime-only tail.

At a positive cutoff x the cube-cutoff primitive is

$$
A_{3}(x) = 18 \Re \sum_{\rho} \frac{x^{\frac{\rho}{3} - \frac{1}{2}}}{\rho \cdot \left(3 - \rho\right) \cdot \left(3 - 2 \cdot \rho\right)}
$$

The sum uses every actual nontrivial zero occurrence with full analytic multiplicity.

**Theorem 1.1 (The uniform remainder at the three-eighths decay rate).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; 2 \le T \land \left(0 < K \land \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|R_{5}(a,B) + \frac{18}{5} \cdot \left(a^{-\frac{1}{3}} - B^{-\frac{1}{3}}\right) - A_{3}(B) + A_{3}(a) - \frac{49}{15} \cdot \left(a^{-\frac{5}{14}} - B^{-\frac{5}{14}}\right)\right| \le K \cdot \left(a^{-\frac{3}{8}} - B^{-\frac{3}{8}}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHSeventhWindow.prime_window_seventh_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tianyu Zhao (2025). *On the mean values of the error terms in Mertens' theorems*. DOI: [10.1007/s40993-025-00640-y](https://doi.org/10.1007/s40993-025-00640-y). URL: <https://arxiv.org/abs/2411.18903v2>.

*Commentary.*

The normalized sixth and seventh corrections have coefficients -6/5 and 7/6. The centered square and cube tails give their spectral densities with errors of order x^(-1/2). The centered fifth tail and the complete-tail residual are also bounded by the three-eighths power majorant.

Eventual positivity allows the signed prime-only density on the whole common log interval. Integrating the sixth and seventh terms gives the coefficients -18/5 and 49/15. Integrating the cube spectrum gives its oriented primitive difference. The majorant integrates on that same interval, so the error bound vanishes when B = a.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHSeventhWindow.prime_window_seventh_of_rh`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootSpectrum](RootSpectrum.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SeventhCutoff](SeventhCutoff.md)
