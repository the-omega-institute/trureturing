# Finite Prefix Deficit Kernel

## Abstract

A finite geometric-prefix deficit has an exact positive-kernel integral and uniform two-sided bounds.

For a natural exponent a, write S_a(t) = sum from k = 0 to a of t^k, Q_a(t) = sum from k = 1 to a of t^k/k, and P_a(t) = sum from k = 0 to a of (a-k)t^k. Let D_a(t) = Q_a(t) - log S_a(t), and K_a(t) = t^a P_a(t)/S_a(t). Interval integrability below is with respect to real Lebesgue measure.

**Theorem 1.1 (Exact integral and uniform reserve).**

$$\begin{aligned}\forall a \in \mathbb{N}, z \in \mathbb{R},\\1 \le a \land 0 < z \land z < 1 \Rightarrow\\IntervalIntegrable\left(K_a, 0, z\right) \land\\D_a\left(z\right) = \int_{0}^{z} \frac{t^{a} P_a\left(t\right)}{S_a\left(t\right)} dt \land\\\frac{a z^{a+1}}{(a+1)(1+z)} \le D_a\left(z\right) \le \frac{a z^{a+1}}{a+1}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/PrefixDeficitKernel.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponent is arbitrary and at least one; the real ratio is strictly between zero and one. The triangular recurrence P_(a+1) = P_a + S_a gives (1-t)P_a(t) = a+1-S_a(t). Differentiating the finite geometric identity and subtracting the logarithmic derivative gives D'_a(t) = K_a(t). The geometric normalization is positive on the entire integration interval, so the continuous kernel is integrable and the fundamental theorem of calculus gives the exact integral.

The inequality a S_a(t) <= (1+t)P_a(t) follows by induction: the increment is t S_a(t) - (a+1)t^(a+1), a sum of nonnegative power differences for 0 <= t <= 1. Termwise comparison also gives P_a(t) <= a S_a(t). Using the constant lower denominator 1+z on the interval and integrating t^a gives the bounds. The lower bound implies a z^(a+1)/(2(a+1)) <= D_a(z).

At a prime ratio z = 1/p, the factor P_a(t)/S_a(t) is the mean remaining exponent in the truncated geometric weights t^k/S_a(t). Only a finite local deficit is estimated. No signed-tail cancellation, Taylor coefficient positivity, Weil quadratic-form positivity, Robin inequality, or Riemann hypothesis follows from this statement.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/PrefixDeficitKernel.result`
