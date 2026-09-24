# A331474 Hankel Generating Function

## Abstract

The actual determinant sequence from the literal A331473 moments has Barry's conjectured rational generating function.

**Theorem 1.1 (The complete literal Hankel generating function).**

$$\operatorname{PowerSeries}.\operatorname{mk}(H) = (1 + 3x + 16x^{2} - 8x^{3} + 36x^{4} - 12x^{5} + x^{6} - x^{7}) \operatorname{invOfUnit}\left((1 + 7x^{2} + x^{4})^{2}, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/A331474HankelGeneratingFunction.a331474_hankel_generating_function` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a331474-hankel-generating-function` (proved) by `D5/S3/Constants/Moments/A331474HankelGeneratingFunction.a331474_hankel_generating_function`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a331474-hankel-generating-function","declaration_gid":"D5/S3/Constants/Moments/A331474HankelGeneratingFunction.a331474_hankel_generating_function","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry (2020). *OEIS A331474, Hankel transform of A331473*. URL: <https://oeis.org/A331474>.

*Acknowledgement.* Radica Bojičić; M. D. Petković; Paul Barry (2025). *Hankel transform of linear combination of three consecutive Catalan numbers*. DOI: [10.15672/hujms.1564485](https://doi.org/10.15672/hujms.1564485).

*Commentary.*

Here H is the determinant-defined sequence from the bridge module, and PowerSeries.mk H is the formal power series whose coefficient at n is that actual determinant. The denominator (1+7x^2+x^4)^2 has constant coefficient 1, so invOfUnit with witness 1 is defined.

The signed kernel bridge reduces H to scalar continuants. Parity gives p(2m)=1 and p(2m+1)=-4(m+1), while U(m)=u(2m) satisfies U(0)=1, U(1)=1, U(2)=7 and U(m+1)=7U(m)-U(m-1) for m at least 2. These identities give one recurrence for every H(n) from n=8 onward; the n=8 and n=9 closures are derived from the bridge, not accepted as a large finite verification.

The first ten values derived along that scalar route are 1, 3, 2, -50, -43, 535, 487, -4983, -4654, 43174. Coefficientwise multiplication by the squared denominator uses those initial values below order 8 and the all-order recurrence thereafter. Thus every coefficient of the denominator product equals the displayed numerator. Multiplication by the unit inverse yields the full formal identity, not merely agreement of a finite prefix.

OEIS revision 9 attributes the conjectured scalar formula to Paul Barry. The proof is repo-derived. The cited 2025 three-consecutive-Catalan families do not subsume this literal source: matching its first two coefficients makes those formulas predict 9 or 10 for the third, whereas the literal source has 12.

## References

- Truth anchor: `D5/S3/Constants/Moments/A331474HankelGeneratingFunction.a331474_hankel_generating_function`
- Dependency: [D5/S3/Constants/Moments/A331474HankelBridge](A331474HankelBridge.md)
