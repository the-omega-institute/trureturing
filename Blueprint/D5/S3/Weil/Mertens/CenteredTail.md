# Centered Mertens tail cancellation

## Abstract

The finite weighted-prime limit cancels from the original Mertens logarithmic tail.

**Theorem 1.1 (A vanishing coefficient at the reciprocal-logarithm scale).**

Lean statement: `D5/S3/Weil/Mertens/CenteredTail.E2p_isLittleO_inv_log`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/CenteredTail.E2p_isLittleO_inv_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original Mertens.E₂p is little-o of x mapped to 1/log(x), at real infinity. Here E₂p(x)=sum(1/p,0<p<=floorNat(x),p prime)-log(log(x))-M, with exactly the original Mertens constant M and inclusive prime sum. Equivalently, for each c>0, eventually |E₂p(x)|<=c/log(x).

WeightedPrimeLimit.exists_E1p_limit supplies a finite limit ell of the original E₁p. For x>=2, Third.E₂p.eq expresses E₂p(x) as E₁p(x)/log(x) minus the integral of E₁p(t)/(t*log(t)^2) over t>x. The constant-integral identity gives the integral of ell/(t*log(t)^2) as ell/log(x). Subtracting this identity centers both terms: E₂p(x)=(E₁p(x)-ell)/log(x)-integral((E₁p(t)-ell)/(t*log(t)^2),t>x).

Choose a tail where |E₁p(t)-ell|<c/2. The centered integrand is integrable by subtraction of the existing actual and constant integrable kernels. Positivity of t*log(t)^2 bounds its integral between -c/(2*log(x)) and c/(2*log(x)); the point term has the same absolute bound. The triangle inequality gives the claimed c/log(x). Neither a value nor a convergence rate for ell is needed. The actual integer small-error envelope consumes this cancellation through the existing one-sided inequality -E₂p<=E₃. No RH or literature novelty is claimed.

## References

- Truth anchor: `D5/S3/Weil/Mertens/CenteredTail.E2p_isLittleO_inv_log`
- Dependency: [D5/S3/Weil/Mertens/WeightedPrimeLimit](WeightedPrimeLimit.md)
