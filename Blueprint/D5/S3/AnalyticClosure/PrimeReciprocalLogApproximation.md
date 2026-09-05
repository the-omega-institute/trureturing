# Prime Reciprocal-Log Approximation

## Abstract

Prime reciprocal logarithms approximate positive offsets with quadratic error.

**Theorem 1.1 (A single prime sees every positive offset).**

$$(\forall delta: \mathbb{R}, 0 < delta \Rightarrow \exists Y: \mathbb{R}, N, q: \mathbb{N}, Y = \exp(\frac{1}{delta}) \land N = \operatorname{natCeil}(Y) \land \operatorname{Prime}(q) \land N < q \land q \leq 2 \times N \land 2 \times N \leq 4 \times Y \land \frac{1}{delta} < \log(q) \land \log(q) \leq \frac{1}{delta} + \log(4) \land 0 \leq delta - \frac{1}{\log(q)} \land delta - \frac{1}{\log(q)} < \log(4) \times delta^{2}) \land (\operatorname{IsBigO}((delta \mapsto \operatorname{infDist}(delta, primeReciprocalLogSpectrum)), \operatorname{nhdsWithin}(0, \operatorname{Ioi}(0)), (delta \mapsto delta^{2}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/PrimeReciprocalLogApproximation.prime_reciprocal_log_quadratic_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real offset delta, set Y = exp(1/delta) and N = ceil(Y). Bertrand's theorem supplies a prime q between N and 2N, while the ceiling estimate puts 2N below 4Y.

Monotonicity of the logarithm gives the displayed logarithmic window. Taking reciprocals then yields a nonnegative error strictly below log(4) times delta squared.

The same witnesses bound the infimum distance to the set of prime reciprocal logarithms, proving the right-hand big-O statement at zero. No uniform nearest-prime selector is asserted.

## References

- Truth anchor: `D5/S3/AnalyticClosure/PrimeReciprocalLogApproximation.prime_reciprocal_log_quadratic_approximation`
