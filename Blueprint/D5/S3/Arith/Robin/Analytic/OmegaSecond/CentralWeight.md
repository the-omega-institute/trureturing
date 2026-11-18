# Uniform central prime-weight comparison

## Abstract

Prime-weight quadrature with endpoint errors and the total variation of the weight.

**Theorem 1.1 (Finite prime quadrature upper bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralWeight.prime_quadrature_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralWeight.prime_quadrature_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every real interval [a,b] with 0<=a<=b, let d be continuous and let f have derivative d throughout the interval. If abs(primeCount(t)-C*t)<=E there for E>=0, the prime sum of f over a<p<=b is at most C times the integral of f plus E times abs(f(a))+abs(f(b))+the integral of abs(d). Both endpoints and the full variation are retained.

**Theorem 1.2 (Uniform moving-weight comparison).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralWeight.central_prime_weight_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralWeight.central_prime_weight_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sufficiently large real P, the estimate holds for every s>=0: the localized prime-weight sum over P/2<p<=2P is at most its real integral over [P/2,2P] divided by log(P), plus 112*log(2)*P/log(P)^2.

The weight increases up to P and decreases after P, so its total variation is bounded independently of s. This prevents the error from growing with the moving saddle. This is an upper estimate; a matching lower counting bound at the second threshold is not established here.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralWeight.central_prime_weight_upper`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralWeight.prime_quadrature_upper`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingWeight](MovingWeight.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion](PrimeExpansion.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTailUpper](../OmegaTailUpper.md)
