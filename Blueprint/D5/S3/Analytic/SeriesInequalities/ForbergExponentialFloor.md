# Forberg Exponential Floor

## Abstract

Forberg's exponential quotient has the shifted quarter-square floor at every positive integer.

**Theorem 1.1 (The whole positive-integer identity).**

$$\forall n: \mathbb{N}, 1\leq n \implies \lfloor \frac{n}{\operatorname{exp}\left(\frac{4}{n}\right) - 1}\rfloor = \lfloor \frac{(n - 1)^{2}}{4}\rfloor$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/ForbergExponentialFloor.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a002620-forberg-exponential-floor` (proved) by `D5/S3/Analytic/SeriesInequalities/ForbergExponentialFloor.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a002620-forberg-exponential-floor","declaration_gid":"D5/S3/Analytic/SeriesInequalities/ForbergExponentialFloor.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Richard R. Forberg; OEIS Foundation Inc. (2013). *Forberg's empirical exponential formula for OEIS A002620*. URL: <https://oeis.org/A002620/internal>.

*Commentary.*

Let n be a natural number with 1 <= n. All subtraction, division, squaring and exponential arguments in the formula are real arithmetic: n is first coerced to the reals, exp means Real.exp, and both floors take values in the integers. In particular, n-1 is real subtraction. The statement includes n=1, both parities and arbitrarily large n.

OEIS A002620 defines the quarter-squares by a(m)=floor(m^2/4). Richard R. Forberg's empirical formula is a(n-1)=floor(n/(exp(4/n)-1)); substituting m=n-1 gives the displayed identity.

For every real r >= 2, the analytic estimate is (r-1)^2/4 <= r/(exp(4/r)-1) < r^2/4-r/2+1. To prove the lower bound, put q=(1+1/r)/(1-1/r). The logarithmic series bound gives 4/r <= 2 log(q), hence exp(4/r) <= ((r+1)/(r-1))^2. The denominator exp(4/r)-1 is positive, so division gives the required lower bound. The upper bound follows from exp(4/r) >= 1+4/r+(4/r)^2/2 and multiplication by positive quantities.

For n=2k, both real expressions lie in the integer floor interval [k(k-1),k(k-1)+1). For n=2k+1, both lie in [k^2,k^2+1). The two-sided estimate supplies these intervals for all n >= 2. At n=1 the quadratic exponential bound gives 0 <= 1/(exp(4)-1) < 1, while the shifted square is zero. The characterization floor(x)=z if and only if z <= x < z+1 finishes every case.

The logarithmic, quadratic exponential, order and floor facts are classical. The identity is stated on the positive integers; no real-parameter extension or claim of priority is asserted.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/ForbergExponentialFloor.result`
