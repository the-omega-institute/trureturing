# A Signed Harmonic–Logarithmic Tail Estimate

## Abstract

A signed estimate for the harmonic-logarithmic tail gives a rational upper bound for Euler's constant.

Let H_N be the sum of the reciprocals of the integers from 1 to N, and let γ be the Euler–Mascheroni constant. The estimate holds for every positive integer N.

**Theorem 1.1 (The signed lower estimate).**

$$\forall N\in\mathbb{N}, N \ge 1 \implies \frac{1}{2N} - \frac{1}{12N^{2}} < H_N - \log N - \gamma$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/HarmonicGammaTail.harmonic_log_tail_lower` (`✓ std3`). ∎

*Citation.* NIST Digital Library of Mathematical Functions (2026). *Asymptotic Expansions*. URL: <https://dlmf.nist.gov/5.11>.

*Commentary.*

Set q_N = H_N − log N − 1/(2N) + 1/(12N²). Its consecutive difference is f(N), where f(x) = log(x+1) − log x − 1/(2x) − 1/(2(x+1)) + 1/(12x²) − 1/(12(x+1)²). The derivative of f is −1/(6x³(x+1)³), strictly negative for x > 0, and f tends to zero at infinity. Thus f is strictly positive and q_N strictly decreases.

Mathlib supplies the limit H_N − log N → γ. The two rational corrections tend to zero, so q_N also tends to γ. The comparison γ ≤ q_(N+1) < q_N preserves the strict gap and gives the stated inequality. This is a classical Euler–Maclaurin estimate.

**Theorem 1.2 (A rational consequence at 128).**

$$\gamma < \frac{5772156650}{10^{10}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/HarmonicGammaTail.eulerMascheroni_upper_128` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2026). *Asymptotic Expansions*. URL: <https://dlmf.nist.gov/5.11>.

*Commentary.*

Apply the preceding inequality at N = 128 and use log 128 = 7 log 2. The first twelve terms of the series for one half of log((1+t)/(1−t)), evaluated at t = 1/3, give a rational lower bound for log 2. Exact rational arithmetic then yields the displayed upper bound. This consequence depends on the uniform signed estimate.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/HarmonicGammaTail.eulerMascheroni_upper_128`
- Truth anchor: `D5/S3/Arith/GoldenResource/HarmonicGammaTail.harmonic_log_tail_lower`
