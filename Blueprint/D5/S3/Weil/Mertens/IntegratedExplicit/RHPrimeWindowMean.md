# The contribution from prime powers

## Abstract

The logarithmic main term of the prime-only window mass under RH

**Theorem 1.1 (A bounded remainder for all real cutoffs).**

$$RH \Rightarrow \left(\exists C \in \mathbb{R},\; 0 \le C \land \left(\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; 2 \le a \Rightarrow \left(a \le b \Rightarrow \left|\operatorname{N}\left(a, b\right) - 2 \cdot \operatorname{log}\left(\frac{b}{a}\right)\right| \le C\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowMean.prime_tail_logarithmic_mass_of_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write Q for the complete Chebyshev tail and Qθ for the prime-only tail with integrand (θ(t)−t)/t². Write N(a,b) for the integral of max(−Qθ(x),0)/√x on [a,b].

The prime-power bounds compare ψ(x)−θ(x) with ψ(√x). Schoenfeld's estimate under RH, applied at √x, yields a bound O(x^(5/12)) for ψ(x)−θ(x)−√x. Tail integration therefore gives √x(Q(x)−Qθ(x))=2+O(x^(−1/12)). The error is integrable with respect to dx/x.

In logarithmic coordinates the complete normalized remainder is the real part of the normalized zero series plus an exponentially damped correction. All zeros contributing to that series lie on the critical line under RH. The phases have absolute ordinates greater than ten, so the integral of each mode over any interval is bounded by its coefficient modulus divided by five. Absolute summability gives a bound common to all endpoints.

The normalized zero series has modulus at most two, so adding two keeps its real part nonnegative. The positive-part map is one-Lipschitz. It preserves the integrable error estimate after adding the prime-power bias. Integration leaves the term 2 log(b/a) and a bounded remainder.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowMean.prime_tail_logarithmic_mass_of_rh`
- Dependency: [D5/S3/Weil/Mertens/Cryptids/Schoenfeld](../Cryptids/Schoenfeld.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeOnlyTailCorrection](PrimeOnlyTailCorrection.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHActualHSqrtBound](RHActualHSqrtBound.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope](RHSharpActualEnvelope.md)
