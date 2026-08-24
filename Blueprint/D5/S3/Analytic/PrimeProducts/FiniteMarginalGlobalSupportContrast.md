# Finite Prime Marginals and Global Support

## Abstract

Compatible finite geometric prime-exponent laws coexist with a product law that almost surely has infinitely many active coordinates.

**Theorem 1.1 (Finite marginals are compatible while finite global support is null).**

$$\begin{aligned}0<s\leq1, q_{p,s}=p^{-s}, \gamma_{p,s}=\operatorname{geometricMeasure}\left(1-q_{p,s}\right), \Gamma_{s}=\operatorname{infinitePi}\left(\gamma_{p,s}\right)\\\forall S\subset_{\operatorname{fin}}\mathbb{P}, \operatorname{ProbabilityMeasure}\left(\operatorname{finiteProduct}\left(S, \gamma_{p,s}\right)\right) \land \operatorname{map}\left(\operatorname{restrict}\left(S\right), \Gamma_{s}\right)=\operatorname{finiteProduct}\left(S, \gamma_{p,s}\right)\\\forall S, e, \operatorname{Pr}\left(\Gamma_{s}, \operatorname{Cylinder}\left(S, e\right)\right)=\prod_{p\in S} (1-p^{-s})p^{-se_{p}}\\\operatorname{Pr}\left(\Gamma_{s}, FiniteSupportProfiles\right)=0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/FiniteMarginalGlobalSupportContrast.finite_marginals_and_global_support_contrast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real s and prime p, the activation probability is p to the power minus s. The coordinate law is constructed as the zero-start geometric measure with success parameter one minus that activation probability, and the global law is Mathlib's canonical infinite product of these coordinates.

Every finite coordinate product is a probability measure. Restricting the global product to any finite prime set gives exactly that finite product, and every finite cylinder has the displayed product of geometric singleton masses.

When s is at most one, the prime activation masses have divergent sum. Product-coordinate independence and the second Borel-Cantelli lemma therefore give infinitely many active primes almost surely, so the set of finite-support exponent profiles has measure zero.

## References

- Truth anchor: `D5/S3/Analytic/PrimeProducts/FiniteMarginalGlobalSupportContrast.finite_marginals_and_global_support_contrast`
