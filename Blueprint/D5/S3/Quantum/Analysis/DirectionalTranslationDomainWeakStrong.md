# Directional Translation Domains

## Abstract

Directional weak differentiation and norm differentiation of actual L2 translations agree in every finite Euclidean dimension.

**Theorem 1.1 (Weak and strong directional derivatives).**

$$\forall n \in \mathbb{N}, b \in \operatorname{E}\left(n\right), f \in \operatorname{E}\left(n\right) \to \mathbb{C}, h \in \operatorname{E}\left(n\right) \to \mathbb{C},\; (\operatorname{MemLp}\left(f, 2, \mathrm{volume}\right) \land \operatorname{MemLp}\left(h, 2, \mathrm{volume}\right)) \Rightarrow (\left(\forall p \in \operatorname{T}\left(n\right),\; \int_{x: \operatorname{E}\left(n\right)} \operatorname{D}\left(p, x, b\right) \cdot f\left(x\right) dx = -\int_{x: \operatorname{E}\left(n\right)} p\left(x\right) \cdot h\left(x\right) dx\right) \Leftrightarrow \operatorname{HasDerivAt}\left((t: \mathbb{R} \mapsto \operatorname{V}\left(b, t, [f]\right)), [h], 0\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/DirectionalTranslationDomainWeakStrong.directional_translation_domain_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural number n, E(n) is EuclideanSpace Real (Fin n), with its Lebesgue measure volume. Both f and h map E(n) to Complex and satisfy MemLp with exponent two. Their classes [f] and [h] are hf.toLp f and hh.toLp h in the actual L2 space. The direction b is an arbitrary element of E(n).

T(n) consists of every real-valued smooth compactly supported test function on E(n), with ContDiff Real (WithTop.some ENat.top) and HasCompactSupport. D(p,x,b) denotes fderiv Real p x applied to b. All real test values and directional derivatives in the integrals are cast to Complex. V(b,t)[f] is DomAddAct.mk (t scalar-multiplied by b) acting on [f]; its representative is x mapping to f(x+t*b). HasDerivAt is the norm derivative with real time.

A compact enlargement of the support of the test derivative gives a uniform integrable bound for translated test pairings. Scalar FTC and the interval-integral identity for continuous linear maps then identify V(b,t)[f]-[f] with the L2 integral of V(b,r)[h] from zero to t. Compact-test separation proves this vector identity, and vector FTC proves the forward implication. Pairing derivatives and derivative uniqueness prove the converse.

Neither global integrability nor derivatives in other directions are required. The dimension n may be zero and the direction b may be zero. The same equivalence retains these cases.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/DirectionalTranslationDomainWeakStrong.directional_translation_domain_iff`
