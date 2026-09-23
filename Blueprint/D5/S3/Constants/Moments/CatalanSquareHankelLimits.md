# Squared-Catalan Hankel Limits

## Abstract

Both Kotesovec squared-Catalan Hankel conjectures have logarithmic rate two times log two.

**Theorem 1.1 (The two literal OEIS limits).**

Lean statement: `D5/S3/Constants/Moments/CatalanSquareHankelLimits.catalan_square_hankel_log_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CatalanSquareHankelLimits.catalan_square_hankel_log_limits` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a277829-a278770-catalan-square-hankel-limits` (proved) by `D5/S3/Constants/Moments/CatalanSquareHankelLimits.catalan_square_hankel_log_limits`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a277829-a278770-catalan-square-hankel-limits","declaration_gid":"D5/S3/Constants/Moments/CatalanSquareHankelLimits.catalan_square_hankel_log_limits","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vaclav Kotesovec (2016). *OEIS A277829 and A278770: squared-Catalan Hankel determinants*. URL: <https://oeis.org/A277829>.

*Acknowledgement.* Gwo Dong Lin (2018). *On Powers of the Catalan Number Sequence*. DOI: [10.1016/j.disc.2018.05.009](https://doi.org/10.1016/j.disc.2018.05.009). URL: <https://arxiv.org/abs/1711.01536v3>.

*Acknowledgement.* Barry Simon (2007). *Equilibrium Measures and Capacities in Spectral Theory*. URL: <https://arxiv.org/abs/0711.2700v1>.

*Commentary.*

The theorem is one conjunction with no hypotheses. Its first component is the A277829 shift r=1 and its second is the A278770 shift r=2. In both components n ranges over all natural sizes, the size-zero determinant is one, and the limiting value is exactly 2*log(2).

The upper half of the squeeze comes from the monic Chebyshev-T bounds in the supporting Growth module. Positivity makes every logarithm and monotonicity step legitimate, including the two literal shifts.

For the lower half, fix 0<delta<8. On a compact central rectangle the two scaled beta densities have one positive lower constant independent of n. Measure domination transfers polynomial energy from the uniform rectangle to the product beta measure while retaining the weight for shift r.

Chebyshev-U orthogonality is proved and transported to the central interval. The resulting monic polynomials have exact squared norms. After normalizing the changed product functions, the proof bounds the full Gram quadratic form below by a scalar identity matrix. It then uses the positive-semidefinite remainder and all principal minors to obtain the determinant bound; this is not a diagonal-only argument.

One constant C>0, independent of n, yields for r=1 and r=2 the lower factor (C*delta^r)^n, the factor ((8-delta)*pi/2)^n, and the quadratic factor ((8-delta)/2)^(n*(n-1)). Exact logarithmic rate calculations for the lower and upper products, followed by delta tending to zero, squeeze both limits to log(4)=2*log(2).

Lin's Catalan product density together with Simon's regular-measure and capacity theorems gives a separate ordinary classical corollary. The Lean proof recorded here is the explicit beta, Gram, Chebyshev and quadratic-form derivation, not a formalization of that literature corollary. The bounded prior audit supports only the two named OEIS settlements and makes no worldwide priority or publication claim.

## References

- Truth anchor: `D5/S3/Constants/Moments/CatalanSquareHankelLimits.catalan_square_hankel_log_limits`
- Dependency: [D5/S3/Constants/Moments/CatalanSquareHankelGrowth](CatalanSquareHankelGrowth.md)
