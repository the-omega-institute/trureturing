# Versine sums over the primes

## Abstract

For sigma >= 0 the series of 1 - cos p^(-sigma) over the primes converges exactly when sigma > 1/2; for every real sigma its difference from half the series of p^(-2 sigma) converges exactly when sigma > 1/4, with partial sums tending to minus infinity for sigma <= 1/4; on the line sigma = 1/2 the versine sum up to x differs from half the sum of the reciprocals of the primes up to x by a quantity within 1/(12 (floor(x) + 1)) of its limit.

P denotes the set of primes. For real sigma and x, the versine sum is the finite sum of 1 - cos(p^(-sigma)) over the primes p in the interval (0, floor(x)], where floor(x) is the natural-number floor of x, so the sum is empty for x < 2. For sigma >= 0 the argument t = p^(-sigma) satisfies 0 < t <= 1; for sigma < 0 it exceeds 1.

**Definition 1.1 (The versine sum over the primes up to x).**

$$\forall \sigma \in \mathbb{R}, \forall x \in \mathbb{R},\; \operatorname{primeVersineSum}\left(\sigma, x\right) = \sum_{p \in (0, \lfloor x \rfloor], p\ \text{prime}} (1 - \operatorname{cos}\left(p^{-\sigma}\right))$$

*Formalization.* `D5/S3/Analytic/Asymptotics/PrimeVersineSums.primeVersineSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

primeVersineSum(sigma, x) is the sum of 1 - cos(p^(-sigma)) over the primes p with p <= floor(x), where p^(-sigma) is the real power of the real number p.

**Theorem 1.2 (Thresholds and the critical line).**

$$\delta(p) = \frac{1}{2 \cdot p} - \left(1 - \operatorname{cos}\left(p^{-1/2}\right)\right),\quad\\(\forall \sigma \in \mathbb{R}, 0 \le \sigma \Rightarrow \left(\operatorname{Summable}\left(p \in \mathbb{P}, 1 - \operatorname{cos}\left(p^{-\sigma}\right)\right) \Leftrightarrow \frac{1}{2} < \sigma\right)) \land\\(\forall \sigma \in \mathbb{R}, \operatorname{Summable}\left(p \in \mathbb{P}, 1 - \operatorname{cos}\left(p^{-\sigma}\right) - \frac{p^{-2\sigma}}{2}\right) \Leftrightarrow \frac{1}{4} < \sigma) \land\\(\forall \sigma \in \mathbb{R}, \sigma \le \frac{1}{4} \Rightarrow \lim_{x \to \infty} (\operatorname{primeVersineSum}\left(\sigma, x\right) - \sum_{p \in (0, \lfloor x \rfloor], p\ \text{prime}} (\frac{p^{-2\sigma}}{2})) = -\infty) \land\\\forall x \in \mathbb{R},\; \sum_{p \in \mathbb{P}} \delta(p) - \frac{1}{12(\lfloor x \rfloor + 1)} \le \sum_{p \in (0, \lfloor x \rfloor], p\ \text{prime}} (\frac{1}{2 \cdot p}) - \operatorname{primeVersineSum}\left(\frac{1}{2}, x\right) \le \sum_{p \in \mathbb{P}} \delta(p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/PrimeVersineSums.prime_versine_phases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the display, Summable(p in P, f(p)) means that the family f indexed by the primes is summable, the sum over p in P is the sum of that summable family, delta(p) = 1/(2p) - (1 - cos(p^(-1/2))), and the limit of minus infinity is taken as the real variable x tends to plus infinity. The theorem has four conjuncts. For sigma >= 0, the series of 1 - cos(p^(-sigma)) over the primes is summable if and only if sigma > 1/2. For every real sigma, the series of 1 - cos(p^(-sigma)) - p^(-2 sigma)/2 is summable if and only if sigma > 1/4. For every real sigma <= 1/4, the versine sum up to x minus half the sum of p^(-2 sigma) over the primes up to x tends to minus infinity. For every real x, the difference between half the sum of 1/p over the primes up to x and the versine sum at sigma = 1/2 lies between the sum of delta over all primes minus 1/(12 (floor(x) + 1)) and that sum.

Put t = p^(-sigma). Two pointwise bounds hold for every real t: the Mathlib inequality 1 - t^2/2 <= cos t, and the quartic lower bound t^2/2 - t^4/24 <= 1 - cos t for the versine, proved in the module of accumulated versines of equal angle steps and reused here. Hence the fourth-order defect cos t - (1 - t^2/2) lies between 0 and t^4/24. For sigma >= 0 one has 0 < t <= 1, so t^4 <= t^2 and (11/24) t^2 <= 1 - cos t <= t^2/2; the first series therefore converges exactly when the series of p^(-2 sigma) over the primes does, which by Mathlib happens exactly when -2 sigma < -1. The summand of the second series is minus the defect. If sigma > 1/4 the defect is at most p^(-4 sigma)/24 and the series of p^(-4 sigma) converges, so the second series converges. For 0 <= sigma <= 1/4 the defect is at least t^4/30, by the bound t^4/30 <= cos t - (1 - t^2/2) for |t| <= 1 proved here from the half-angle identity cos t = 1 - 2 sin^2(t/2), the Mathlib fifth-order bound for the sine and a polynomial inequality; comparison with the divergent series of p^(-4 sigma) shows that the defect series diverges. For sigma < 0 the defect is at least p^(-2 sigma)/2 - 2, which tends to plus infinity, so its terms do not tend to 0 and the defect series diverges as well. Thus for every sigma <= 1/4 the defect series has nonnegative terms and diverges, its partial sums tend to plus infinity, and the third conjunct follows. The third conjunct also gives the forward direction of the second: for sigma <= 1/4 the summands of the second series are nonpositive and their partial sums tend to minus infinity, so that series is not summable. On the line sigma = 1/2 one has t^2 = 1/p, so delta(p) is the defect at t = p^(-1/2), nonnegative and at most 1/(24 p^2). Comparing the tail over n > N of 1/(24 n^2) with 2/(N + 1) bounds the tail of the defect series beyond N = floor(x) by 1/(12 (N + 1)), which is the fourth conjunct.

The hypothesis sigma >= 0 of the first conjunct keeps t in (0, 1]; at sigma = 0 every term of the first series is the positive constant 1 - cos 1, so it diverges, in agreement with the first equivalence. For sigma < 0 the arguments p^(-sigma) of the first series are unbounded, its behaviour depends on the distribution of p^(-sigma) modulo 2 pi, and no claim is made about it. The second series needs no such hypothesis: for sigma < 0 its summands tend to minus infinity, so it diverges and its partial sums tend to minus infinity, as the second and third conjuncts state. Each threshold is sharp because it is stated as an equivalence.

Combined with the Mertens estimate Mertens.E₂p.bound, which states that the sum of 1/p over the primes up to x equals log log x + M + O(1/log x) with the Mertens constant M, the fourth conjunct gives, as x tends to infinity, that the sum of 1 - cos(p^(-1/2)) over the primes up to x equals (log log x)/2 + M/2 minus the sum of delta over all primes plus O(1/log x). This consequence is not one of the formal statements of this module.

The thresholds are elementary comparisons with the prime zeta series, and the explicit tail on the critical line is a comparison with the tail of the series of 1/n^2; the combination is derived here.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/PrimeVersineSums.primeVersineSum`
- Truth anchor: `D5/S3/Analytic/Asymptotics/PrimeVersineSums.prime_versine_phases`
- Dependency: [D5/S3/Analytic/Asymptotics/AccumulatedSagittaPhases](AccumulatedSagittaPhases.md)
