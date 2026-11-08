# A finite quantitative bracket for the complete original return threshold

## Abstract

Finite Gaussian envelopes locate the same unique original odd-wrap threshold within a quantitative interval.

**Theorem 1.1 (The unique original threshold retains all signs and satisfies the refined bracket).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyOddWrapThresholdBracket.actual_odd_wrap_threshold_bracket`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyOddWrapThresholdBracket.actual_odd_wrap_threshold_bracket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each odd integer p>=5, there is exactly one natural T>2 with the complete original sign criterion: W33<W19 for every natural 2<=t<T, W19<=W33 at T, and W19<W33 for every natural t>T. Every count is the existing original_return_pair at p,t and source length (p(6t-1)).toNat. The theorem preserves this whole criterion and adds alpha*p+1/6-1/(6p)<T<=ceil(alpha*p+1/6-1/(25p)). The first comparison is a strict real inequality; the second compares the integer T with an integer ceiling. Composite odd p are included.

The constant is alpha=2/(3*log(rho)), where rho is the existing frozen order-nine d-bonacci Perron root dbonacciPerronRoot 9. Its existing inverse-power identity gives rho+rho^(-9)=2, hence s_star=log(rho) satisfies G(s_star)=2 for G(s)=exp(s)+exp(-9s). The analytic estimates give 24/25<alpha<1 and the secant lower slope 98/75 for s>=2/3. This reuses the existing algebraic root instead of introducing a new root choice.

First reuse the original unique single crossing and positive cone to obtain T<=p. Write v=t-1/6+1/(6p), so the exact Gaussian parameter is s=2p/(3v). If T were at or below the proposed lower endpoint, then v<=alpha*p and s>=s_star. The strict finite lower envelope would force 2W19/W33>G(s)>=2, contradicting the original nonnegative comparison W19<=W33 at T. Positivity of W33 follows from its original exact binomial formula and is not an added premise.

For the upper endpoint put U=ceil(alpha*p+1/6-1/(25p)). If U>=p, the existing T<=p finishes. Otherwise U>=2 and U<p place the same integer state in the full upper-envelope band 24p<=25U. At that state v>=alpha*p+19/(150p), giving s_star-s>=19/(225p^2), with 2/3<=s<=s_star. The secant slope yields a Gaussian gap larger than the finite envelope error 1/(10p^2); the exact surplus is 349/(33750p^2)>0. Thus W19<W33 at U, and the original single crossing forces T<=U.

The proof uses both strict finite envelopes, the existing Perron-root identity and the original count formulas. It makes no asymptotic approximation, asserts no equality of counts at T and supplies no exact ceiling formula for T. The stated refined bracket is restricted to odd integers p>=5. No literature novelty or complete open-problem settlement is claimed.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyOddWrapThresholdBracket.actual_odd_wrap_threshold_bracket`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot](BajnokBeattyOddWrapGaussianRoot.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianUpperEnvelope](BajnokBeattyOddWrapGaussianUpperEnvelope.md)
