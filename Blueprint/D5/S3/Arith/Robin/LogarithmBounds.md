# Logarithmic bounds

## Abstract

Logarithmic bounds, reciprocal-logarithmic continuity and prime cutoffs for Robin estimates.

**Lemma 1.1 (Strict tangent for the iterated logarithm).**

Lean statement: `D5/S3/Arith/Robin/LogarithmBounds.loglog_tangent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LogarithmBounds.loglog_tangent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct real x,y>1, log(log(y))-log(log(x))<(y-x)/(x*log(x)). The price function is g(x)=1/(x*log(x)). The inequality follows from the strict logarithm tangent on the outer logarithm and its weak form on the inner one.

**Lemma 1.2 (Quadratic bound for a logarithmic tail).**

Lean statement: `D5/S3/Arith/Robin/LogarithmBounds.neg_log_one_sub_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LogarithmBounds.neg_log_one_sub_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

For 0<=x<=1/2, -log(1-x)<=x+x^2. Monotonicity of log(1-x)+x+x^2 on that interval proves the estimate. For 0<=x<=1/4, the right side is at most 4*x/3, as used in the prefix-lcm tail bound.

**Lemma 1.3 (Logarithms near an endpoint).**

Lean statement: `D5/S3/Arith/Robin/LogarithmBounds.buffer_log_size`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LogarithmBounds.buffer_log_size` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real x>=256 and x-2<=z<=x+1, one has 5<log(z)<=x/20. The estimate controls original endpoint windows and gives the lower logarithm bound used for cumulative Mertens peaks at cutoffs at least 10000.

**Lemma 1.4 (Continuity of the reciprocal-logarithmic weight).**

Lean statement: `D5/S3/Arith/Robin/LogarithmBounds.weight_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LogarithmBounds.weight_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>1, w(t)=(log(t)+1)/(t^2*log(t)^2) is continuous on [a,b]. Its denominator stays nonzero on the interval.

**Lemma 1.5 (Equivalent natural prime cutoffs).**

Lean statement: `D5/S3/Arith/Robin/LogarithmBounds.prime_filter_Icc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LogarithmBounds.prime_filter_Icc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t, filtering [0,floor(t)] by primality gives primeCutoff(t), the prime filter over (0,floor(t)]. A prime is positive, so the extra zero endpoint contributes nothing.

## References

- Truth anchor: `D5/S3/Arith/Robin/LogarithmBounds.buffer_log_size`
- Truth anchor: `D5/S3/Arith/Robin/LogarithmBounds.loglog_tangent`
- Truth anchor: `D5/S3/Arith/Robin/LogarithmBounds.neg_log_one_sub_le`
- Truth anchor: `D5/S3/Arith/Robin/LogarithmBounds.prime_filter_Icc`
- Truth anchor: `D5/S3/Arith/Robin/LogarithmBounds.weight_continuous`
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](ActualRobinClockCovariance.md)
- Dependency: [D5/S3/Arith/Robin/MellinWeightedVariation](MellinWeightedVariation.md)
