# Baez-Duarte Newton Reciprocal Zeta

## Abstract

The actual Baez-Duarte Newton series converges to reciprocal zeta for every complex argument with real part greater than one, with absolute interchange derived on that domain.

**Theorem 1.1 (The original Newton series on the initial half-plane).**

$$\forall s\in\mathbb{C}, 1<\operatorname{Re}\left(s\right)\Rightarrow \operatorname{HasSum}\left((k:\mathbb{N})\mapsto\operatorname{c}\left(k\right) \operatorname{P}\left(k, \frac{s}{2}\right), \frac{1}{\operatorname{riemannZeta}\left(s\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteNewton.baez_duarte_newton_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

Here c is the existing real baezDuarte finite binomial transform of reciprocals of real parts of zeta at the positive even integers, cast to the complex numbers. P is the existing normalizedPochhammer polynomial: the product of the factors one minus z divided by r for r from one to k. The conclusion is HasSum at the complex reciprocal of riemannZeta s. The only analytic hypothesis is that the real part of s exceeds one.

For m=n+1, the unsigned coupled kernel is the reciprocal square of m times the k-th power of one minus that reciprocal square, times the norm of P(k,s/2). Its row sums are Q(k) times that norm. The imported Q and P bounds yield an outer power exponent minus (Re(s)+1)/2, strictly below minus one. Eventual comparison retains the finite prefix, including k=0. The bound on the absolute Moebius function then proves absolute summability of the signed coupled series before Fubini is applied.

The imported signed coefficient HasSum evaluates one family of fibers. A private adapter of mathlib's complex binomial series evaluates the other, and positive-real-base power rules identify the resulting Moebius Dirichlet terms. The existing Dirichlet product and nonvanishing theorems identify their sum with reciprocal zeta. Both zero indices are retained; at n=0 the inner series sums to one, and at s=2 only c(0) survives.

This is a repo-derived formal proof of the source's initial half-plane identification, not its sharper half-plane extension or an RH direction. The generic adapters are private. Utility none classifies this as a general infinite analytical theorem, not a finite computation.

## References

- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteNewton.baez_duarte_newton_hasSum`
- Dependency: [D5/S3/Analytic/SeriesInequalities/BaezDuarteQBounds](../../Analytic/SeriesInequalities/BaezDuarteQBounds.md)
- Dependency: [D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds](../../Analytic/SeriesInequalities/NormalizedPochhammerBounds.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RieszBaezDuarte](../ZetaBridge/RieszBaezDuarte.md)
