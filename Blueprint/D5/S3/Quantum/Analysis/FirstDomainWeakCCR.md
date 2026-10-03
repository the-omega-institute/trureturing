# First-Domain Weak Canonical Relation

## Abstract

The actual position and momentum outputs satisfy the weak canonical relation on individual first L2 domains.

**Theorem 1.1 (Actual position and weak momentum).**

$$\forall h \in \mathbb{R}, f \in \mathbb{R} \to \mathbb{C}, g \in \mathbb{R} \to \mathbb{C}, a \in \mathbb{R} \to \mathbb{C}, b \in \mathbb{R} \to \mathbb{C},\; (\left(\left(\left(\left(\left(\left(0 < h \land \operatorname{MemLp}\left(f, 2, \mathrm{volume}\right)\right) \land \operatorname{MemLp}\left(g, 2, \mathrm{volume}\right)\right) \land \operatorname{MemLp}\left(a, 2, \mathrm{volume}\right)\right) \land \operatorname{MemLp}\left(b, 2, \mathrm{volume}\right)\right) \land \operatorname{MemLp}\left(\operatorname{X}\left(f\right), 2, \mathrm{volume}\right)\right) \land \operatorname{MemLp}\left(\operatorname{X}\left(g\right), 2, \mathrm{volume}\right)\right) \land \left(\left(\forall p \in T,\; \int_{x: \mathbb{R}} \operatorname{deriv}\left(p, x\right) \cdot f\left(x\right) dx = -\int_{x: \mathbb{R}} p\left(x\right) \cdot a\left(x\right) dx\right) \land \left(\forall p \in T,\; \int_{x: \mathbb{R}} \operatorname{deriv}\left(p, x\right) \cdot g\left(x\right) dx = -\int_{x: \mathbb{R}} p\left(x\right) \cdot b\left(x\right) dx\right)\right)) \Rightarrow \operatorname{inner}\left(\operatorname{Q}\left(f\right), \operatorname{P}\left(b\right)\right) - \operatorname{inner}\left(\operatorname{P}\left(a\right), \operatorname{Q}\left(g\right)\right) = i \cdot h \cdot \operatorname{inner}\left([f], [g]\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/FirstDomainWeakCCR.first_domain_weak_ccr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All MemLp conditions and integrals use real-line Lebesgue measure volume. The six witnesses hf, hg, hdf, hdg, hxf and hxg provide the L2 classes. [u] denotes the class of u, X(u) is x mapping to x times u(x), Q(u)=[X(u)], and P(v)=-i h [v]. The positive real scalar h is the Planck scalar hbar. Here a=df and b=dg. Complex inner products are conjugate-linear in the first variable and linear in the second.

T consists of every real-valued C-infinity compactly supported test function, with ContDiff Real (WithTop.some ENat.top) and HasCompactSupport. Its values and ordinary derivatives are cast into Complex in the displayed integrals. The two weak equations specify the actual maximal first derivative domains.

Actual modulation U(s)[u]=[exp(isx)u(x)] has strong L2 derivative iQ(u): its slopes are bounded by |xu| and its squared errors by 4|xu| squared. Dominated convergence proves this derivative. The translation-domain equivalence gives the actual derivatives for V(t)[u]=[u(x+t)]. Differentiating the bounded Weyl pairing identity twice, once in each real parameter, gives the displayed positive sign. Only individual first domains are used; the statement requires neither an operator-product domain nor second derivatives.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/FirstDomainWeakCCR.first_domain_weak_ccr`
- Dependency: [D5/S3/Quantum/Analysis/TranslationDomainWeakStrong](TranslationDomainWeakStrong.md)
