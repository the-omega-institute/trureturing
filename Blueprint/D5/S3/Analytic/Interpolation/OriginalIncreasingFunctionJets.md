# Original increasing-function endpoint jets

## Abstract

The original all-order endpoint-jet assertion, with its monotone input class and one simultaneous smooth witness.

**Definition 1.1 (unitInterval).**

$$\operatorname{unitInterval}\left(\right) = \operatorname{Icc}\left(0, 1\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.unitInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnOriginal.unitInterval: The closed real interval [0,1]. Every endpoint derivative below is iteratedDerivWithin on this interval.

**Definition 1.2 (primitive).**

$$\forall g \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right),\; \forall x \in \operatorname{Real}\left(\right),\; \operatorname{primitive}\left(g, x\right) = \int_{0}^{x} \operatorname{g}\left(s\right) \operatorname{ds}\left(\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.primitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnOriginal.primitive: The variable s is bound by the interval integral; its orientation is from 0 to x.

**Definition 1.3 (repeatedIntegral).**

$$\forall k \in \operatorname{Nat}\left(\right),\; \forall g \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right),\; \operatorname{repeatedIntegral}\left(k, g\right) = \operatorname{iterate}\left(\operatorname{primitive}\left(\right), k, g\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.repeatedIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnOriginal.repeatedIntegral: Function.iterate applies primitive k times; k=0 returns g.

**Definition 1.4 (jet).**

$$\forall j \in \operatorname{Nat}\left(\right),\; \forall f \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right),\; \operatorname{jet}\left(j, f\right) = \operatorname{iteratedDerivWithin}\left(j, f, \operatorname{unitInterval}\left(\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.jet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnOriginal.jet: The full one-sided endpoint convention is iteratedDerivWithin j f unitInterval, including j=0.

**Definition 1.5 (W).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{W}\left(n\right) = \{b: \operatorname{Fin}\left(n + 1\right) \to \operatorname{Real}\left(\right) \mid \exists f \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right),\; \left(\left(\operatorname{ContDiffOn}\left(\operatorname{Real}\left(\right), \operatorname{NatToWithTopNatInfinity}\left(n\right), f, \operatorname{unitInterval}\left(\right)\right) \land \operatorname{MonotoneOn}\left(\operatorname{jet}\left(n, f\right), \operatorname{unitInterval}\left(\right)\right)\right) \land \left(\exists x \in \operatorname{Real}\left(\right),\; x \in \operatorname{unitInterval}\left(\right) \land \left(\exists y \in \operatorname{Real}\left(\right),\; y \in \operatorname{unitInterval}\left(\right) \land \operatorname{jet}\left(n, f, x\right) \ne \operatorname{jet}\left(n, f, y\right)\right)\right)\right) \land \left(\forall j \in \operatorname{Fin}\left(n + 1\right),\; \operatorname{jet}\left(\operatorname{val}\left(j\right), f, 0\right) = 0 \land \operatorname{jet}\left(\operatorname{val}\left(j\right), f, 1\right) = b\left(j\right)\right)\}$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.W` (`✓ std3`).

*Citation.* Maxim R. Burke; Maleeha Haris; Madhavendra (2025). *Repeated integrals of increasing functions*. DOI: [10.48550/arXiv.2512.02151](https://doi.org/10.48550/arXiv.2512.02151). URL: <https://arxiv.org/abs/2512.02151v1>.

*Commentary.*

PnOriginal.W: The source defines W_n using f in C^n[0,1], increasing and nonconstant D^n f, and all endpoint jets from 0 through n. Increasing means nondecreasing. NatToWithTopNatInfinity denotes the actual natural-order coercion in ContDiffOn. No strict input monotonicity or absolute continuity is assumed.

**Definition 1.6 (P).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{P}\left(n\right) = \left(\operatorname{IsOpen}\left(\operatorname{W}\left(n\right)\right) \land \left(\forall b \in \operatorname{Fin}\left(n + 1\right) \to \operatorname{Real}\left(\right),\; b \in \operatorname{W}\left(n\right) \Rightarrow \left(\exists f \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right),\; \left(\left(\left(\left(\operatorname{ContDiffOn}\left(\operatorname{Real}\left(\right), \infty, f, \operatorname{unitInterval}\left(\right)\right) \land \left(\forall j \in \operatorname{Fin}\left(n + 1\right),\; \operatorname{jet}\left(\operatorname{val}\left(j\right), f, 0\right) = 0 \land \operatorname{jet}\left(\operatorname{val}\left(j\right), f, 1\right) = b\left(j\right)\right)\right) \land \left(\forall x \in \operatorname{Real}\left(\right),\; x \in \operatorname{Ioo}\left(0, 1\right) \Rightarrow 0 < \operatorname{jet}\left(n + 1, f, x\right)\right)\right) \land \operatorname{jet}\left(n + 1, f, 0\right) = 1\right) \land \operatorname{jet}\left(n + 1, f, 1\right) = 1\right) \land \left(\forall j \in \operatorname{Nat}\left(\right),\; n + 1 < j \Rightarrow \left(\operatorname{jet}\left(j, f, 0\right) = 0 \land \operatorname{jet}\left(j, f, 1\right) = 0\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.P` (`✓ std3`).

*Citation.* Maxim R. Burke; Maleeha Haris; Madhavendra (2025). *Repeated integrals of increasing functions*. DOI: [10.48550/arXiv.2512.02151](https://doi.org/10.48550/arXiv.2512.02151). URL: <https://arxiv.org/abs/2512.02151v1>.

*Commentary.*

PnOriginal.P: The source's (P_n) requires openness of W_n and one C-infinity witness for each b in W_n, with all original finite endpoint jets, positive order n+1 derivative in (0,1), value 1 at both endpoints at that order, and zero at both endpoints at every higher order.

**Definition 1.7 (clamp).**

$$\forall x \in \operatorname{Real}\left(\right),\; \operatorname{clamp}\left(x\right) = \operatorname{max}\left(0, \operatorname{min}\left(1, x\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.clamp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnOriginal.clamp: Clamp to the original closed interval.

**Definition 1.8 (extend).**

$$\forall g \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right),\; \operatorname{extend}\left(g\right) = g \circ \operatorname{clamp}\left(\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.extend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnOriginal.extend: Compose g with clamp.

**Definition 1.9 (Vec).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{Vec}\left(n\right) = \left(\operatorname{Fin}\left(n + 1\right) \to \operatorname{Real}\left(\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.Vec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.Vec: The actual finite real-coordinate carrier.

**Definition 1.10 (Center).**

$$\operatorname{Center}\left(\right) = \operatorname{Subtype}\left(\operatorname{Icc}\left(0, 1\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.Center` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.Center: Center is the subtype of the closed real interval, so endpoints are retained.

**Definition 1.11 (Width).**

$$\operatorname{Width}\left(\right) = \operatorname{Subtype}\left(\operatorname{Ioi}\left(0\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.Width` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.Width: Width is the subtype of positive real numbers.

**Definition 1.12 (Param).**

$$\operatorname{Param}\left(\right) = \operatorname{Prod}\left(\operatorname{Center}\left(\right), \operatorname{Width}\left(\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.Param` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.Param: The center-width product subtype.

**Definition 1.13 (gamma).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall t \in \operatorname{Real}\left(\right),\; \operatorname{gamma}\left(n, t\right) = \lambda k: \operatorname{Fin}\left(n + 1\right), \left(1 - t\right)^{\operatorname{val}\left(k\right)}$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.gamma: Every finite index is coerced to its natural value before exponentiation.

**Definition 1.14 (raw).**

$$\forall xi \in \operatorname{Real}\left(\right),\; \forall sigma \in \operatorname{Real}\left(\right),\; \forall t \in \operatorname{Real}\left(\right),\; \operatorname{raw}\left(xi, sigma, t\right) = \operatorname{expNegInvGlue}\left(t\right) \cdot \operatorname{expNegInvGlue}\left(1 - t\right) \cdot \operatorname{exp}\left(-\frac{\left(t - xi\right)^{2}}{sigma^{2}}\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.raw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.raw: The explicit flat smooth weight times the Gaussian factor; exp is Real.exp.

**Definition 1.15 (z).**

$$\forall xi \in \operatorname{Real}\left(\right),\; \forall sigma \in \operatorname{Real}\left(\right),\; \operatorname{z}\left(xi, sigma\right) = \int_{t \in \operatorname{Icc}\left(0, 1\right)} \operatorname{raw}\left(xi, sigma, t\right) \operatorname{dt}\left(\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.z` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.z: The Lean definition is the interval integral 0..1; the Icc volume integral is equal on these ordered endpoints.

**Definition 1.16 (density).**

$$\forall xi \in \operatorname{Real}\left(\right),\; \forall sigma \in \operatorname{Real}\left(\right),\; \forall t \in \operatorname{Real}\left(\right),\; \operatorname{density}\left(xi, sigma, t\right) = \frac{\operatorname{raw}\left(xi, sigma, t\right)}{\operatorname{z}\left(xi, sigma\right)}$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.density` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.density: Division is real division.

**Definition 1.17 (moment).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall xi \in \operatorname{Real}\left(\right),\; \forall sigma \in \operatorname{Real}\left(\right),\; \operatorname{moment}\left(n, xi, sigma\right) = \int_{t \in \operatorname{Icc}\left(0, 1\right)} \operatorname{smul}\left(\operatorname{density}\left(xi, sigma, t\right), \operatorname{gamma}\left(n, t\right)\right) \operatorname{dt}\left(\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.moment: The actual Bochner moment vector over the closed interval.

**Definition 1.18 (component).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall q \in \operatorname{Param}\left(\right),\; \operatorname{component}\left(n, q\right) = \operatorname{moment}\left(n, \operatorname{SubtypeToReal}\left(\operatorname{fst}\left(q\right)\right), \operatorname{SubtypeToReal}\left(\operatorname{snd}\left(q\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.component` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.component: Both subtype projections are explicitly coerced to real numbers.

**Definition 1.19 (S).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{S}\left(n\right) = \operatorname{PointedConeHull}\left(\operatorname{Real}\left(\right), \operatorname{range}\left(\lambda t: \operatorname{Center}\left(\right), \operatorname{gamma}\left(n, \operatorname{SubtypeToReal}\left(t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.S: PointedConeHull is PointedCone.hull, with nonnegative scalar coefficients.

**Definition 1.20 (T).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{T}\left(n\right) = \operatorname{PointedConeHull}\left(\operatorname{Real}\left(\right), \operatorname{range}\left(\operatorname{component}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.T: The cone generated by the actual density components.

**Definition 1.21 (mixture).**

$$\forall c \in \operatorname{Finsupp}\left(\operatorname{Param}\left(\right), \operatorname{Subtype}\left(\lambda a: \operatorname{Real}\left(\right), 0 \le a\right)\right),\; \forall t \in \operatorname{Real}\left(\right),\; \operatorname{mixture}\left(c, t\right) = \sum_{q \in \operatorname{support}\left(c\right)} \operatorname{SubtypeToReal}\left(c\left(q\right)\right) \cdot \operatorname{density}\left(\operatorname{SubtypeToReal}\left(\operatorname{fst}\left(q\right)\right), \operatorname{SubtypeToReal}\left(\operatorname{snd}\left(q\right)\right), t\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.mixture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.mixture: q is bound by the finite support sum; each nonnegative coefficient and parameter subtype is coerced to Real.

**Definition 1.22 (endpointCut).**

$$\forall delta \in \operatorname{Real}\left(\right),\; \forall t \in \operatorname{Real}\left(\right),\; \operatorname{endpointCut}\left(delta, t\right) = \operatorname{smoothTransition}\left(2 - \frac{2 \cdot t}{delta}\right) + \operatorname{smoothTransition}\left(2 - \frac{2 \cdot \left(1 - t\right)}{delta}\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.endpointCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.endpointCut: The two reflected smooth transitions give the endpoint correction.

**Definition 1.23 (cutMoment).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall delta \in \operatorname{Real}\left(\right),\; \operatorname{cutMoment}\left(n, delta\right) = \int_{t \in \operatorname{Icc}\left(0, 1\right)} \operatorname{smul}\left(\operatorname{endpointCut}\left(delta, t\right), \operatorname{gamma}\left(n, t\right)\right) \operatorname{dt}\left(\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.cutMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.cutMoment: The moment vector of the endpoint correction.

**Definition 1.24 (rho).**

$$\forall delta \in \operatorname{Real}\left(\right),\; \forall c \in \operatorname{Finsupp}\left(\operatorname{Param}\left(\right), \operatorname{Subtype}\left(\lambda a: \operatorname{Real}\left(\right), 0 \le a\right)\right),\; \forall t \in \operatorname{Real}\left(\right),\; \operatorname{rho}\left(delta, c, t\right) = \operatorname{endpointCut}\left(delta, t\right) + \operatorname{mixture}\left(c, t\right)$$

*Formalization.* `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PnActualMixtureConsumer.rho: One density combines the endpoint correction with a finite nonnegative mixture.

**Theorem 1.25 (The original all-order assertion).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{P}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Maxim R. Burke; Maleeha Haris; Madhavendra (2025). *Repeated integrals of increasing functions*. DOI: [10.48550/arXiv.2512.02151](https://doi.org/10.48550/arXiv.2512.02151). URL: <https://arxiv.org/abs/2512.02151v1>.

*Commentary.*

Conjecture 1.2, arXiv:2512.02151v1, p. 2: '(P_n) is true for all nonnegative integers n.' The mathematical source proves exactly forall n : Nat, PnOriginal.P n.

The source's W and P use their original closed-interval derivatives. The Stieltjes argument retains singular continuous and flat input derivatives and arbitrary positive mass. Reversed factorial coordinates connect all endpoint jets to one moment vector. The single witness is repeatedIntegral (n+1) rho; the same rho realizes every coordinate and every endpoint condition.

The coordinate-transform function sends each endpoint-jet vector b to its reversed factorial coordinates:

$\lambda n: \operatorname{Nat}\left(\right), \lambda b: \operatorname{Fin}\left(n + 1\right) \to \operatorname{Real}\left(\right), \lambda k: \operatorname{Fin}\left(n + 1\right), \operatorname{NatToReal}\left(\operatorname{factorial}\left(\operatorname{val}\left(k\right)\right)\right) \cdot b\left(\operatorname{rev}\left(k\right)\right)$

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.Center`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.P`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.Param`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.S`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.T`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.Vec`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.W`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.Width`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.clamp`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.component`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.cutMoment`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.density`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.endpointCut`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.extend`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.gamma`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.jet`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.mixture`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.moment`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.primitive`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.raw`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.repeatedIntegral`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.result`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.rho`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.unitInterval`
- Truth anchor: `D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets.z`
