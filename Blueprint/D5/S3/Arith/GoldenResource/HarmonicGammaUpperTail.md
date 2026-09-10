# A Fourth-Order Harmonic–Logarithmic Tail Bound

## Abstract

The corrected harmonic-logarithmic remainder lies strictly between zero and its fourth-order term.

For a positive integer N, write H_N for the harmonic sum and γ for the Euler–Mascheroni constant. Set R_N = H_N − log N − γ − 1/(2N) + 1/(12N²).

**Theorem 1.1 (The strict fourth-order upper estimate).**

$$\forall N\in\mathbb{N}, N \ge 1 \implies H_N - \log N - \gamma - \frac{1}{2N} + \frac{1}{12N^{2}} < \frac{1}{120N^{4}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/HarmonicGammaUpperTail.harmonic_log_tail_upper` (`✓ std3`). ∎

*Citation.* NIST Digital Library of Mathematical Functions (2026). *Asymptotic Expansions*. URL: <https://dlmf.nist.gov/5.11>.

*Commentary.*

Let q_N = H_N − log N − 1/(2N) + 1/(12N²), and let c(x) = 1/(120x⁴). The consecutive difference q_N − q_(N+1) is f(N), where f(x) = log(x+1) − log x − 1/(2x) − 1/(2(x+1)) + 1/(12x²) − 1/(12(x+1)²). Put w(x) = c(x) − c(x+1).

For x > 0, f′(x) = −1/(6x³(x+1)³) and (f−w)′(x) = (5x²+5x+1)/(30x⁵(x+1)⁵) > 0. Both f and f−w tend to zero at infinity. Thus f(x) < w(x), and a_N = q_N − c(N) satisfies a_N < a_(N+1).

Mathlib supplies the finite telescoping identity: the sum of a_(N+k+1) − a_(N+k) for 0 ≤ k < m equals a_(N+m) − a_N. Every summand is positive, so a_N ≤ a_(N+m). The known limit q_N → γ and c(N) → 0 give a_(N+1) ≤ γ. Keeping the first strict step yields a_N < a_(N+1) ≤ γ, which is precisely R_N < 1/(120N⁴). This is the positive-real Euler–Maclaurin remainder estimate.

**Theorem 1.2 (The two-sided strict bracket).**

$$\forall N\in\mathbb{N}, N \ge 1 \implies 0 < H_N - \log N - \gamma - \frac{1}{2N} + \frac{1}{12N^{2}} < \frac{1}{120N^{4}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/HarmonicGammaUpperTail.harmonic_log_tail_bounds` (`✓ std3`). ∎

*Citation.* NIST Digital Library of Mathematical Functions (2026). *Asymptotic Expansions*. URL: <https://dlmf.nist.gov/5.11>.

*Commentary.*

The signed lower estimate gives R_N > 0. Combining it with the preceding upper estimate produces the full strict bracket for every positive integer N.

**Theorem 1.3 (A rational consequence at 64).**

$$\frac{5772156649}{10^{10}} < \gamma$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/HarmonicGammaUpperTail.eulerMascheroni_lower_64` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2026). *Asymptotic Expansions*. URL: <https://dlmf.nist.gov/5.11>.

*Commentary.*

Apply the fourth-order estimate at N = 64 and write log 64 = 6 log 2. The first fourteen terms of the series for one half of log((1+t)/(1−t)), evaluated at t = 1/3, together with its absolute remainder bound, give a rational upper bound for log 2. Exact rational arithmetic yields the displayed lower bound for γ. Its proof depends on the uniform upper tail estimate.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/HarmonicGammaUpperTail.eulerMascheroni_lower_64`
- Truth anchor: `D5/S3/Arith/GoldenResource/HarmonicGammaUpperTail.harmonic_log_tail_bounds`
- Truth anchor: `D5/S3/Arith/GoldenResource/HarmonicGammaUpperTail.harmonic_log_tail_upper`
- Dependency: [D5/S3/Arith/GoldenResource/HarmonicGammaTail](HarmonicGammaTail.md)
