# Translation Domain: Weak and Strong Derivatives

## Abstract

Smooth compact-test weak differentiation and strong differentiation of the L2 translation orbit have the same domain.

**Theorem 1.1 (Translation-domain equivalence).**

$$\forall f \in \mathbb{R} \to \mathbb{C}, h \in \mathbb{R} \to \mathbb{C},\; (\operatorname{MemLp}\left(f, 2, volume\right) \land \operatorname{MemLp}\left(h, 2, volume\right)) \Rightarrow (\left(\forall p \in T,\; \int_{x: \mathbb{R}} \operatorname{deriv}\left(p, x\right) \cdot f\left(x\right) dx = -\int_{x: \mathbb{R}} p\left(x\right) \cdot h\left(x\right) dx\right) \Leftrightarrow \operatorname{HasDerivAt}\left((t: \mathbb{R} \mapsto \operatorname{V}\left(t, [f]\right)), [h], 0\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/TranslationDomainWeakStrong.translation_domain_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All integrals and MemLp conditions use Lebesgue measure volume on the real line. The symbols hf and hh are witnesses of the two displayed MemLp conditions. The classes [f] and [h] denote hf.toLp f and hh.toLp h in L2. V(t)[f] is the actual DomAddAct translation DomAddAct.mk t acting on [f], represented almost everywhere by x mapping to f(x+t).

The test class T consists of all real-valued smooth compactly supported functions: ContDiff Real (WithTop.some ENat.top) and HasCompactSupport. Test values and their ordinary derivatives are cast into Complex in the two integrals. HasDerivAt denotes the norm derivative in the actual L2 space, with real time.

Compact-support finite-measure domination differentiates translated test pairings. Scalar FTC, continuous-linear-map interval-integral commutation and separation by compact tests give V(t)[f]-[f] equal to the integral from zero to t of V(r)[h]. Vector FTC proves the forward implication; pairing derivatives and uniqueness prove the reverse. The only function hypotheses are the two square-integrability conditions.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/TranslationDomainWeakStrong.translation_domain_iff`
