# Finite-Jet Signs at the Square-Root Endpoint

## Abstract

Finite even jets bound the slope and give strictly negative curvature after square-root reparametrization.

Let Q be smooth near zero and write Q1, Q2, Q3 and Q4 for its first four derivatives. Evenness supplies Q1(0)=Q3(0)=0. If Q2(0)<2k and Q4(0)<0, the reparametrized function C(z)=Q(sqrt(z)) has first derivative below k and negative second derivatives for all sufficiently small positive z. The formal sign theorem takes only the explicitly used derivative chain and endpoint values; it does not assume evenness or differentiability of C at zero.

**Definition 1.1 (Slope expression).**

$$\forall {Q1: \mathbb{R} \to \mathbb{R}}, \forall {z: \mathbb{R}}, \operatorname{sqrtSlope}\left(Q1, z\right) = \frac{\operatorname{Q1}\left(\operatorname{sqrt}\left(z\right)\right)}{2 \cdot \operatorname{sqrt}\left(z\right)}$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/CachinConvexLimits.sqrtSlope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The expression is Q1(sqrt(z))/(2 sqrt(z)). It is a total real function; its derivative interpretation is asserted only for z>0.

**Definition 1.2 (Curvature expression).**

$$\forall {Q1: \mathbb{R} \to \mathbb{R}}, \forall {Q2: \mathbb{R} \to \mathbb{R}}, \forall {z: \mathbb{R}}, \operatorname{sqrtCurvature}\left(Q1, Q2, z\right) = \frac{\operatorname{sqrt}\left(z\right) \cdot \operatorname{Q2}\left(\operatorname{sqrt}\left(z\right)\right) - \operatorname{Q1}\left(\operatorname{sqrt}\left(z\right)\right)}{4 \cdot \operatorname{sqrt}\left(z\right)^{3}}$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/CachinConvexLimits.sqrtCurvature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The numerator is sqrt(z) Q2(sqrt(z))-Q1(sqrt(z)); the denominator is 4 sqrt(z)^3.

**Theorem 1.3 (First derivative under square-root reparametrization).**

$$\forall {Q: \mathbb{R} \to \mathbb{R}}, \forall {Q1: \mathbb{R} \to \mathbb{R}}, \forall {z: \mathbb{R}}, {0 < z} \Rightarrow \left({\operatorname{HasDerivAt}\left(Q, \operatorname{Q1}\left(\operatorname{sqrt}\left(z\right)\right), \operatorname{sqrt}\left(z\right)\right)} \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{comp}\left(Q, sqrt\right), \operatorname{sqrtSlope}\left(Q1, z\right), z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexLimits.sqrt_comp_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For z>0 the square-root derivative and chain rule give the stated slope expression.

**Theorem 1.4 (Second derivative under square-root reparametrization).**

$$\forall {Q1: \mathbb{R} \to \mathbb{R}}, \forall {Q2: \mathbb{R} \to \mathbb{R}}, \forall {z: \mathbb{R}}, {0 < z} \Rightarrow \left({\operatorname{HasDerivAt}\left(Q1, \operatorname{Q2}\left(\operatorname{sqrt}\left(z\right)\right), \operatorname{sqrt}\left(z\right)\right)} \Rightarrow \operatorname{HasDerivAt}\left(\operatorname{sqrtSlope}\left(Q1\right), \operatorname{sqrtCurvature}\left(Q1, Q2, z\right), z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexLimits.sqrtSlope_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient and chain rules give the curvature expression from the first derivative chain.

**Theorem 1.5 (Negative endpoint signs from four finite jets).**

$$\forall {Q1: \mathbb{R} \to \mathbb{R}}, \forall {Q2: \mathbb{R} \to \mathbb{R}}, \forall {Q3: \mathbb{R} \to \mathbb{R}}, \forall {Q4: \mathbb{R} \to \mathbb{R}}, \forall {a: \mathbb{R}}, \forall {k: \mathbb{R}}, {{{{{{{{{0 < a} \land {\forall {t: \mathbb{R}}, {t \in \operatorname{Icc}\left(0, a\right)} \Rightarrow \operatorname{HasDerivAt}\left(Q1, \operatorname{Q2}\left(t\right), t\right)}} \land {\forall {t: \mathbb{R}}, {t \in \operatorname{Icc}\left(0, a\right)} \Rightarrow \operatorname{HasDerivAt}\left(Q2, \operatorname{Q3}\left(t\right), t\right)}} \land {\forall {t: \mathbb{R}}, {t \in \operatorname{Icc}\left(0, a\right)} \Rightarrow \operatorname{HasDerivAt}\left(Q3, \operatorname{Q4}\left(t\right), t\right)}} \land {\operatorname{Q1}\left(0\right) = 0}} \land {\operatorname{Q3}\left(0\right) = 0}} \land {\operatorname{Q2}\left(0\right) < 2 \cdot k}} \land {\operatorname{ContinuousAt}\left(Q4, 0\right)}} \land {\operatorname{Q4}\left(0\right) < 0}} \Rightarrow \exists delta: \mathbb{R}, {0 < delta} \land {\forall {z: \mathbb{R}}, {z \in \operatorname{Ioo}\left(0, delta\right)} \Rightarrow \left({\operatorname{sqrtSlope}\left(Q1, z\right) < k} \land {\operatorname{sqrtCurvature}\left(Q1, Q2, z\right) < 0}\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/CachinConvexLimits.exists_sqrt_jet_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity makes Q4 negative on a small interval. Since Q3(0)=0, the mean value theorem first gives Q3(t)<0. Thus Q2(t)<=Q2(0)<2k and Q1(t)<2kt. The derivative of t Q2(t)-Q1(t) is t Q3(t)<0, and this numerator vanishes at zero. It is therefore negative for t>0. Substituting t=sqrt(z) and using the positive denominators proves both signs without a Taylor remainder or l'Hopital argument.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexLimits.exists_sqrt_jet_negative`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexLimits.sqrtCurvature`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexLimits.sqrtSlope`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexLimits.sqrtSlope_hasDerivAt`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/CachinConvexLimits.sqrt_comp_hasDerivAt`
