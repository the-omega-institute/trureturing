# Parity resolvents of real control blocks

## Abstract

Exact parity resolvents and all-order moments of two-dimensional Pauli control blocks.

**Definition 1.1 (Actual control block).**

Lean statement: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.controlBlock`

*Formalization.* `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.controlBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary real a and t, H(a,t) is the real matrix [[(1+a)/4,t/4],[t/4,(1-a)/4]]. For a pure Y-axis source, t=mu sqrt(1-a squared) and the two blocks are H(a,t) and H(a,-t).

**Definition 1.2 (Shifted control filter).**

Lean statement: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.controlFilter`

*Formalization.* `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.controlFilter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary real a,t,s, P(a,t,s)=H(a,t)(H(a,t)+sI) inverse. The inverse is Mathlib's nonsingular inverse; subsequent statements use s>0.

**Definition 1.3 (Control determinant numerator).**

Lean statement: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.h`

*Formalization.* `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.h` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,t, h(a,t)=1-a squared-t squared. This is sixteen times the determinant of H(a,t).

**Definition 1.4 (Shifted determinant numerator).**

Lean statement: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.denom`

*Formalization.* `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.denom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,t,s, R(a,t,s)=8s(1+2s)+h(a,t). It is sixteen times the determinant of H(a,t)+sI.

**Definition 1.5 (Half parity trace).**

Lean statement: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.alpha`

*Formalization.* `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Define alpha(a,t,s)=4sa/R(a,t,s) for all real parameters.

**Definition 1.6 (Negative parity determinant).**

Lean statement: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.beta`

*Formalization.* `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Define beta(a,t,s)=h(a,t)/R(a,t,s) for all real parameters.

**Definition 1.7 (Actual cyclic product moment).**

Lean statement: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.moment`

*Formalization.* `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,t,s and natural j, moment(a,t,j,s) is the trace of (P(a,-t,s)P(a,t,s)) to the j-th power.

**Theorem 1.8 (Exact shifted resolvent and parity data).**

$$\forall a \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall s \in \mathbb{R},\; (0 \le a) \Rightarrow ((a \le 1) \Rightarrow ((t^{2} \le 1 - a^{2}) \Rightarrow ((0 < s) \Rightarrow ((0 < \operatorname{denom}\left(a, t, s\right)) \land ((0 \le \operatorname{alpha}\left(a, t, s\right)) \land ((0 \le \operatorname{beta}\left(a, t, s\right)) \land ((\operatorname{controlFilter}\left(a, t, s\right) = \begin{bmatrix}\frac{4 \cdot s + \operatorname{h}\left(a, t\right) + 4 \cdot s \cdot a}{\operatorname{denom}\left(a, t, s\right)}&\frac{4 \cdot s \cdot t}{\operatorname{denom}\left(a, t, s\right)}\\\frac{4 \cdot s \cdot t}{\operatorname{denom}\left(a, t, s\right)}&\frac{4 \cdot s + \operatorname{h}\left(a, t\right) - 4 \cdot s \cdot a}{\operatorname{denom}\left(a, t, s\right)}\end{bmatrix}) \land ((\operatorname{controlFilter}\left(a, -t, s\right) = parity \cdot \operatorname{controlFilter}\left(a, t, s\right) \cdot parity) \land ((\operatorname{trace}\left(parity \cdot \operatorname{controlFilter}\left(a, t, s\right)\right) = 2 \cdot \operatorname{alpha}\left(a, t, s\right)) \land (\operatorname{det}\left(parity \cdot \operatorname{controlFilter}\left(a, t, s\right)\right) = -\operatorname{beta}\left(a, t, s\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.resolvent_spectral_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, R is strictly positive, alpha and beta are nonnegative, and the exact filter is [[(4s+h+4sa)/R,4st/R],[4st/R,(4s+h-4sa)/R]]. With Z=diag(1,-1), the negative filter equals ZP(a,t,s)Z, the trace of ZP(a,t,s) is 2alpha, and its determinant is -beta. These identities include h=0; invertibility is required only after the positive shift.

**Theorem 1.9 (All-order exact matrix moment).**

$$\forall a \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall s \in \mathbb{R},\; (0 \le a) \Rightarrow ((a \le 1) \Rightarrow ((t^{2} \le 1 - a^{2}) \Rightarrow ((0 < s) \Rightarrow (\forall j \in \mathbb{N},\; \operatorname{moment}\left(a, t, j, s\right) = \operatorname{evenMoment}\left(\operatorname{alpha}\left(a, t, s\right), \operatorname{beta}\left(a, t, s\right), j\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.moment_eq_evenMoment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, and every natural j, moment(a,t,j,s) equals (alpha+sqrt(alpha squared+beta)) to the power 2j plus (alpha-sqrt(alpha squared+beta)) to the power 2j. Parity makes P(a,-t,s)P(a,t,s) the square of ZP(a,t,s); the Vieta power-trace identity supplies all orders, including repeated roots.

**Theorem 1.10 (Every-order matrix comparison).**

$$\forall a \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall s \in \mathbb{R},\; (0 \le a) \Rightarrow ((a \le 1) \Rightarrow ((t^{2} \le 1 - a^{2}) \Rightarrow ((0 < s) \Rightarrow (\forall j \in \mathbb{N},\; \frac{a^{2 \cdot j}}{\left(1 + 2 \cdot s\right)^{2 \cdot j}} \le \operatorname{moment}\left(a, t, j, s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.moment_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, and every natural j, a to the power 2j divided by (1+2s) to the power 2j is at most moment(a,t,j,s). The characteristic polynomial evaluated at a/(1+2s) equals beta times ((a/(1+2s)) squared-1), which is nonpositive.

**Theorem 1.11 (Strict comparison in the positive determinant case).**

$$\forall a \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall s \in \mathbb{R},\; (0 \le a) \Rightarrow ((a \le 1) \Rightarrow ((t^{2} \le 1 - a^{2}) \Rightarrow ((0 < \operatorname{h}\left(a, t\right)) \Rightarrow ((0 < s) \Rightarrow (\forall j \in \mathbb{N},\; (1 \le j) \Rightarrow (\frac{a^{2 \cdot j}}{\left(1 + 2 \cdot s\right)^{2 \cdot j}} < \operatorname{moment}\left(a, t, j, s\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.moment_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a,t,s with 0<=a<=1, t squared<=1-a squared, h(a,t)>0 and s>0, and every natural j>=1, a to the power 2j divided by (1+2s) to the power 2j is strictly less than moment(a,t,j,s). The comparison polynomial is strictly negative.

**Theorem 1.12 (Exact rank-one boundary).**

$$\forall a \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall s \in \mathbb{R},\; (0 \le a) \Rightarrow ((a \le 1) \Rightarrow ((t^{2} \le 1 - a^{2}) \Rightarrow ((\operatorname{h}\left(a, t\right) = 0) \Rightarrow ((0 < s) \Rightarrow (\forall j \in \mathbb{N},\; (1 \le j) \Rightarrow (\operatorname{moment}\left(a, t, j, s\right) = \frac{a^{2 \cdot j}}{\left(1 + 2 \cdot s\right)^{2 \cdot j}}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.moment_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a,t,s with 0<=a<=1, t squared<=1-a squared, h(a,t)=0 and s>0, and every natural j>=1, moment(a,t,j,s) equals a to the power 2j divided by (1+2s) to the power 2j. This includes a=0 and the zero product moment.

**Definition 1.13 (Actual complex shifted filter).**

Lean statement: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.complexFilter`

*Formalization.* `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.complexFilter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,t,s, complexFilter(a,t,s) is Hc(Hc+sI) inverse, where Hc is the entrywise complex embedding of H(a,t). Thus it uses the actual complex matrix inverse rather than an assumed embedding rule.

**Definition 1.14 (Actual complex sandwich moment).**

Lean statement: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.complexMoment`

*Formalization.* `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.complexMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a,t,s and natural j, complexMoment(a,t,j,s) is the real part of the trace of (sqrt(Pc(a,-t,s))Pc(a,t,s)sqrt(Pc(a,-t,s))) to the j-th power. The square root is the positive square root from the continuous functional calculus.

**Theorem 1.15 (Complex square-root sandwich and real cyclic product).**

$$\forall a \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall s \in \mathbb{R},\; (0 \le a) \Rightarrow ((a \le 1) \Rightarrow ((t^{2} \le 1 - a^{2}) \Rightarrow ((0 < s) \Rightarrow (\forall j \in \mathbb{N},\; \operatorname{complexMoment}\left(a, t, j, s\right) = \operatorname{moment}\left(a, t, j, s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.complex_moment_eq_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, and every natural j, complexMoment(a,t,j,s)=moment(a,t,j,s). The embedded shifted filter equals the embedding of the real filter. The exact filter formula proves positive semidefiniteness, including h=0; the square of its positive square root is therefore the filter itself. Cyclicity of power traces proves the equality without requiring either unshifted block or either filter to be invertible. In fact the full complex sandwich trace is the real embedding of the real product moment.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.alpha`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.beta`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.complexFilter`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.complexMoment`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.complex_moment_eq_real`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.controlBlock`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.controlFilter`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.denom`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.h`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.moment`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.moment_boundary`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.moment_comparison`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.moment_eq_evenMoment`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.moment_strict`
- Truth anchor: `D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.resolvent_spectral_data`
- Dependency: [D5/S3/Quantum/Matrix/PauliFunding/ParityTraceComparison](ParityTraceComparison.md)
- Dependency: [D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness](../../Measurement/FreeSpectrahedronFeasibilityWitness.md)
