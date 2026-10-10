# Actual Window Laws, Moments and Nonzero Counts

## Abstract

The actual four-window experiment has a positive raw-score mean but an increasing number of conditionally symmetric nonzero score differences.

The alphabet, in low-to-high bit order, is 000,100,010,101,001. A record contains four complete windows and a label in {0,1,2}. Window 1 has masses (rho,rho,rho,rho,1-4 rho); windows 2,3,4 have masses ((1-3 rho)/2,rho,(1-3 rho)/2,rho,rho). Windows at different positions are independent. The two endpoints inside window 3 belong to that same window and retain their actual joint law.

The true teacher uses windows (1,3,4), and its competitor uses (2,3,4). The priority teacher returns 1 when its first high-low gate is open, otherwise 2 when its second gate is open, and 0 otherwise. Given the true class c, the label is sampled from R_a=a R+(1-a)J/3, where the rows of R are (1/2,1/4,1/4), (3/8,1/4,3/8), (1/4,1/4,1/2). Z=Y-1 and score=Z(C_true-C_rival). The complete record mass is the product of the four window masses and this conditional label mass. The displayed limitCleanMass and limitCountTail denote limits as rho decreases to zero, with m=ceil(K/(a^2 rho^2)); the latter uses the conditional nonzero count and its displayed cutoff N.

**Theorem 1.1 (Legal whole-window position laws).**

$$\forall rho, 0<rho\le\frac{1}{8} \implies \operatorname{Admissible}\left(rho, \operatorname{positionLaw}\left(rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities.position_law_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 0<rho<=1/8, each position law has total mass one and each of its five symbol masses is at least rho.

**Theorem 1.2 (The pointwise teacher difference).**

$$\forall w: \operatorname{Record}\left(\right), \operatorname{difference}\left(w\right) = (\operatorname{apply}\left(h_{1}, w\right)-\operatorname{apply}\left(h_{2}, w\right))\operatorname{apply}\left(l_{3}, w\right)(1-2\operatorname{apply}\left(h_{3}, w\right)\operatorname{apply}\left(l_{4}, w\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities.difference_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This identity holds for every complete record, including every label. Here hi and li are the high and low zero-one endpoint indicators, and D=C_true-C_rival. Both h3 and l3 refer to window 3.

**Theorem 1.3 (Five exact actual-law moments).**

$$\forall rho: \operatorname{Real}\left(\right), \forall a: \operatorname{Real}\left(\right), 0<rho \land 0<a \implies \begin{aligned}\operatorname{disagreement}\left(rho, a\right) = 2rho(1-5rho+12rho^{2})\\\operatorname{normGap}\left(rho, a\right) = -2rho+10rho^{2}\\\operatorname{mean}\left(rho, a\right) = 3arho^{3}\\\operatorname{variance}\left(rho, a\right) = \operatorname{kappa}\left(a\right)\operatorname{disagreement}\left(rho, a\right)-9a^{2}rho^{6}\\0<\operatorname{mean}\left(rho, a\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities.actual_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identities are finite-sum identities for all rho>0 and a>0. For 0<rho<=1/8 and 0<a<=1, the mass is a probability law: d is the expectation of D squared, normGap is the expectation of (C_true-1)^2-(C_rival-1)^2, mean is the expectation of score, variance is its second moment minus its squared mean, and kappa(a)=(8+a)/12. These formulas integrate the actual joint window-label mass, with no independent endpoint replacement.

**Theorem 1.4 (Simultaneous exclusion of the reverse event).**

$$\forall a: \operatorname{Real}\left(\right), \forall K: \operatorname{Real}\left(\right), 0<a \land 0<K \implies \operatorname{limitCleanMass}\left(a, K\right)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities.all_clean_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all fixed a>0 and K>0, put m=ceil(K/(a^2 rho^2)). The reverse event is h1=0,h2=1,l3=1. Its single-record mass is 12 rho^3. The probability that all m independent records avoid it is (1-12 rho^3)^m, which tends to one as rho decreases to zero.

**Theorem 1.5 (Conditional nonzero counts escape every fixed cutoff).**

$$\forall a: \operatorname{Real}\left(\right), \forall K: \operatorname{Real}\left(\right), 0<a\le1 \land 0<K \implies \forall N: \operatorname{Nat}\left(\right), \operatorname{limitCountTail}\left(a, K, N\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities.nonzero_count_diverges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix 0<a<=1 and K>0. Condition each complete record on avoiding the reverse event, and let Jm count records with nonzero score. For every natural cutoff N, P(Jm<=N) tends to zero as rho decreases to zero. The conditional nonzero mass is p=kappa(a) 2 rho(1-3 rho)(1-2 rho)/(1-12 rho^3), and m p tends to infinity. The finite-product Laplace transform gives the bound exp(N) exp(-(1-exp(-1)) m p).

Finite sums and product factorization are standard probability algebra. The fair-sign tie coefficient is zero at odd lengths and choose(j,j/2)/2^j at even lengths. The central-binomial estimate is reused from Nat.choose_middle_sq_mul_le in the Gelfond module; it implies that the tie coefficient tends to zero. These classical estimates are applied to the specified complete-record experiment.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities.actual_moments`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities.all_clean_limit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities.difference_formula`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities.nonzero_count_diverges`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities.position_law_admissible`
- Dependency: [D5/S3/Arith/AbsoluteValues/Heights/Gelfond](../../AbsoluteValues/Heights/Gelfond.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation](../HeterogeneousTeacherSeparation.md)
