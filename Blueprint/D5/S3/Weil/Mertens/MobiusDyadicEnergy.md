# Signed Möbius shell energy forced by a zeta zero

## Abstract

A quantitative lower bound for cumulative signed Möbius shell energy from each zeta zero in the right half of the critical strip.

**Definition 1.1 (Signed difference at two scales).**

Lean statement: `D5/S3/Weil/Mertens/MobiusDyadicEnergy.mobiusDyadicDifference`

*Formalization.* `D5/S3/Weil/Mertens/MobiusDyadicEnergy.mobiusDyadicDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write M(x) for the real sum of μ(n)/n over positive integers n at most the natural floor of x, as defined by mobiusPartialSum. The signed difference at x is M(x) − M(2x).

**Definition 1.2 (Energy of a dyadic shell).**

Lean statement: `D5/S3/Weil/Mertens/MobiusDyadicEnergy.mobiusDyadicShellEnergy`

*Formalization.* `D5/S3/Weil/Mertens/MobiusDyadicEnergy.mobiusDyadicShellEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural k, E(k) is the Lebesgue integral of the squared signed difference on the half-open interval (2^k, 2^(k+1)].

**Definition 1.3 (Exponential energy on a logarithmic prefix).**

$$K\left(\beta, U\right)=\int_{0}^{U} \exp\left((2\beta -1)t\right)\,d t$$

*Formalization.* `D5/S3/Weil/Mertens/MobiusDyadicEnergy.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real β and U, K(β,U) is the oriented real interval integral from zero to U. At β = 1/2 it equals U. For β > 1/2 and U tending to infinity it grows on the scale exp((2β − 1)U).

**Theorem 1.4 (Eventual cumulative shell lower bound).**

$$\forall \rho \in \mathbb{C}, \frac{1}{2} \leq \Re\left(\rho\right) < 1 \land \zeta\left(\rho\right)=0 \implies \exists c \in \mathbb{R}, 0<c \land (\exists N_{0} \in \mathbb{N}, \forall N \in \mathbb{N}, N_{0} \leq N \implies c K\left(\Re\left(\rho\right), N \log 2\right) \leq \sum_{0 \leq k<N} E\left(k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/MobiusDyadicEnergy.signed_dyadic_eventual_prefix_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each complex zero ρ of the Riemann zeta function with real part at least one half and strictly below one, the positive real c and natural N₀ can depend on ρ. The sum contains precisely the shells with indices k below N, and log is the natural logarithm.

The finite convolution of the fractional-part kernel and the weighted Möbius sum gives the exact forcing term. The kernel's vanishing Laplace transform at the shifted zero gives an integrable resolvent. Finite convolution with the signed profile leaves an exponential term of amplitude (1 − exp((ρ − 1) log 2))/ρ² and a decaying error. The amplitude is nonzero because Re(ρ) < 1. The finite-prefix Young inequality bounds the response energy by the input energy. The substitution x = exp(t) at U = N log 2 converts that input energy to the stated shell sum.

## References

- Truth anchor: `D5/S3/Weil/Mertens/MobiusDyadicEnergy.K`
- Truth anchor: `D5/S3/Weil/Mertens/MobiusDyadicEnergy.mobiusDyadicDifference`
- Truth anchor: `D5/S3/Weil/Mertens/MobiusDyadicEnergy.mobiusDyadicShellEnergy`
- Truth anchor: `D5/S3/Weil/Mertens/MobiusDyadicEnergy.signed_dyadic_eventual_prefix_lower_bound`
