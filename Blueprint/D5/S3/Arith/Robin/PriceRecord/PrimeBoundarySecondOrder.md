# Finite endpoints and normalization

## Abstract

Second-order expansion of the original finite calibrated prime-prefix quantity.

The finite-prefix Q is the original objective plus its tangent remainder. Original phi, baseline, realValues and realInfimum are imported without redefinition. This asymptotic does not assert integer Robin or RH.

**Theorem 1.1 (The exact endpoint and tie identity for canonical Q).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder.eventual_Q_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder.eventual_Q_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Eventually C=1+H*ell=r^2 and the actual supported boundary is b(p)=max(1,log(C)/log(p)-1). Original prefixQ equals 2*(pi(r)*log r-theta(r))/(r^2-1)+pi(r)*[-log(1-r^-2)]+logarithmicTail(r,P). Consume the existing prime_prefix_boundary_formulas and fixed_price_Q_identity; r<P has already been proved from H/P->1. Tied primes p=r are counted in the inclusive head and have zero clock contribution. There is no assumption theta(P)<=P.

**Theorem 1.2 (Coefficients four, four, sixteen in the genuine r scale).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder.calibrated_Q_second_order`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder.calibrated_Q_second_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal conclusion is log(r)^2*(r*log(r)*prefixQ-4-4/log(r))->16. Equivalently Q=4/(r*l)*(1+1/l+4/l^2+o(l^-2)). The clock component contributes 2,4,12; the head contributes 1,1,2; and the tail contributes 1,-1,2 at the three successive powers. The four-term pi residual and theta_error_log_power 3 supply the errors at the moving r. C/(C-1) is retained and its log(r)^2 correction tends to zero. The first head/tail corrections cancel, leaving the requested second-order coefficient.

All higher Euler powers are controlled together by the existing frozen PrimeSquareTail.prime_square_tail_logarithmic_refinements supplier. Its second conjunct has the same strict (floor(y),floor(z)] prime sum and finite upper endpoint, with error 6/(y*log(y)^4)+5/(y*log(y)^9); the consumer keeps tailPolynomial as a private local abbreviation and converts this bound to 130/(y*log(y)^4) using log(y)>=1. No FinitePrimeTailSecondOrder package or public tail wrapper is part of this consumer closure.

The finite endpoint is paid explicitly: prove r*log(r)^3/P->0 by squaring and using C/(H*ell)->1, log r/ell->1/2, H/P->1 and ell^7/H->0. Then r*log(r)^3*T(P)->0. The quantitative prime-counting and theta remainders come from QuantitativePrimeAbel; the prefix scales come from RealInfimumPrimeBoundary.

The complete three-coefficient expansion retains the finite endpoint correction before passing to the prefix limit.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder.calibrated_Q_second_order`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder.eventual_Q_exact`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PrimeSquareTail](PrimeSquareTail.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](QuantitativePrimeAbel.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/RealInfimumPrimeBoundary](RealInfimumPrimeBoundary.md)
