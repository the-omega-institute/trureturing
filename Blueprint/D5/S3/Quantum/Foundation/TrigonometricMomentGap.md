# The entire trigonometric moment body and its effects

## Abstract

The original second trigonometric moment body has an attained one-tenth comparison gap over its entire proper-effect interval.

The model is the universal Caratheodory orbitope C2 of Sanyal, Sottile and Sturmfels, Orbitopes, arXiv:0911.5436v4, section 5.1, Theorem 5.2 and Corollary 5.4. The construction and neighborly face structure are established mathematics. The present theorem implements this same full model and its explicit comparison obstruction; it makes no literature novelty claim.

Use four real coordinates in the order cos(theta), sin(theta), cos(2 theta), sin(2 theta). The homogeneous carrier is their product with the original mass coordinate. The angle parameter ranges over all real numbers. Repeated periodic labels denote the same actual point; no angle inequality is used as a point-distinctness assumption.

**Definition 1.1 (Four real coordinates).**

$$\operatorname{Coordinates}\left(\right) = \operatorname{Fin}\left(4\right)\to \mathbb{R}$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.Coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Functions on Fin 4 with real values, using indices 0 through 3.

**Definition 1.2 (The original homogeneous carrier).**

$$\operatorname{Carrier}\left(\right) = \mathbb{R}\times\operatorname{Coordinates}\left(\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.Carrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first coordinate is mass, and the remaining four coordinates are unnormalized moments.

**Definition 1.3 (The complete moment curve).**

$$\forall theta \in \mathbb{R},\; \operatorname{momentCurve}\left(theta\right) = \operatorname{tuple}\left(\operatorname{cos}\left(theta\right), \operatorname{sin}\left(theta\right), \operatorname{cos}\left(2\cdot theta\right), \operatorname{sin}\left(2\cdot theta\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.momentCurve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full real parameter domain is retained.

**Definition 1.4 (The original convex body).**

$$\operatorname{body}\left(\right) = \operatorname{convexHull}\left(\mathbb{R}, \operatorname{range}\left(\operatorname{momentCurve}\left(\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.body` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The convex hull of the entire curve, with no finite approximation.

**Definition 1.5 (Normalization at mass one).**

$$\forall w \in \operatorname{Coordinates}\left(\right),\; \operatorname{apply}\left(\operatorname{lift}\left(\right), w\right) = \operatorname{pair}\left(1, w\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.lift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is an affine map into the original homogeneous carrier.

**Definition 1.6 (Normalized original curve).**

$$\forall theta \in \mathbb{R},\; \operatorname{curve}\left(theta\right) = \operatorname{apply}\left(\operatorname{lift}\left(\right), \operatorname{momentCurve}\left(theta\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.curve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The homogeneous state with mass one and the four original moments.

**Definition 1.7 (The entire normalized state set).**

$$\operatorname{states}\left(\right) = \operatorname{convexHull}\left(\mathbb{R}, \operatorname{range}\left(\operatorname{curve}\left(\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.states` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Affine images commute with convex hull, so this is exactly lift applied to body.

**Definition 1.8 (The original full homogeneous cone).**

$$\operatorname{cone}\left(\right) = \operatorname{radialHull}\left(\operatorname{states}\left(\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.cone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

radialHull(S) means precisely the set of t times w, for every real t>=0 and every w in S. It includes zero. Closure under addition uses convexity of the entire state set; scalar closure uses every nonnegative real scalar.

**Definition 1.9 (The unchanged original unit).**

$$\forall w \in \operatorname{Carrier}\left(\right),\; \operatorname{apply}\left(\operatorname{unit}\left(\right), w\right) = \operatorname{fst}\left(w\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.unit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first-coordinate real-linear map. It is strictly positive at every nonzero element of the cone.

**Definition 1.10 (Every real-linear original effect).**

$$\forall a \in \mathbb{R},\; \forall b \in \operatorname{Coordinates}\left(\right),\; \forall w \in \operatorname{Carrier}\left(\right),\; \operatorname{apply}\left(\operatorname{effect}\left(a, b\right), w\right) = a\cdot \operatorname{fst}\left(w\right)+\operatorname{dot}\left(b, \operatorname{snd}\left(w\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.effect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dot product sums all four coordinates. Every real-linear map from Carrier to the reals has this form; properness is not assumed in this representation.

**Definition 1.11 (The full degree-two restriction).**

$$\forall a \in \mathbb{R},\; \forall b \in \operatorname{Coordinates}\left(\right),\; \forall theta \in \mathbb{R},\; \operatorname{trigonometric}\left(a, b, theta\right) = a+\operatorname{apply}\left(b, 0\right)\cdot \operatorname{cos}\left(theta\right)+\operatorname{apply}\left(b, 1\right)\cdot \operatorname{sin}\left(theta\right)+\operatorname{apply}\left(b, 2\right)\cdot \operatorname{cos}\left(2\cdot theta\right)+\operatorname{apply}\left(b, 3\right)\cdot \operatorname{sin}\left(2\cdot theta\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.trigonometric` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original proper interval is exactly the set of these polynomials whose values lie in [0,1] at every real angle. Both implications are proved on the entire cone.

**Definition 1.12 (The full exposed two-point zero face).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall theta \in \mathbb{R},\; \operatorname{apply}\left(\operatorname{pairSupport}\left(a, b\right), \operatorname{curve}\left(theta\right)\right) = (1-\operatorname{cos}\left(theta-a\right))\cdot(1-\operatorname{cos}\left(theta-b\right))$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.pairSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real-linear coefficients are mass 1+cos(a-b)/2 and moments (-cos(a)-cos(b), -sin(a)-sin(b), cos(a+b)/2, sin(a+b)/2). The functional is nonnegative on the entire original cone. Its whole normalized zero face is exactly the segment of the two actual curve points. This equality also holds for coincident periodic labels, when the segment is a singleton. The entire original minimal cone-face base equals this segment. Distinct actual points give an injective affine chart of the closed one-dimensional ball.

**Definition 1.13 (The reference pure point).**

$$\operatorname{p}\left(\right) = \operatorname{curve}\left(0\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.p` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reference point is proved extreme in the entire original base.

**Definition 1.14 (The first excluded mixed state).**

$$\operatorname{x}\left(\right) = \frac{1}{2}\cdot (\operatorname{curve}\left(\operatorname{pi}\left(\right)/2\right)+\operatorname{curve}\left(-\operatorname{pi}\left(\right)/2\right))$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.x` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mean of the two quarter-turn curve points.

**Definition 1.15 (The second excluded state).**

$$\operatorname{y}\left(\right) = \operatorname{curve}\left(\operatorname{pi}\left(\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.y` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The half-turn pure point.

**Definition 1.16 (The midpoint of the two excluded states).**

$$\operatorname{mixed}\left(\right) = \frac{1}{2}\cdot (\operatorname{x}\left(\right)+\operatorname{y}\left(\right))$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.mixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

It has mass one and moment coordinates (-1/2,0,0,0).

**Definition 1.17 (The angle of the lower-bound decomposition).**

$$\operatorname{angle}\left(\right) = \operatorname{arccos}\left(-\frac{2}{3}\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.angle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Its cosine is exactly -2/3.

**Definition 1.18 (An actual original mixed state).**

$$\operatorname{z}\left(\right) = \frac{1}{2}\cdot (\operatorname{curve}\left(\operatorname{angle}\left(\right)\right)+\operatorname{curve}\left(-\operatorname{angle}\left(\right)\right))$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.z` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two actual original curve states average to moments (-2/3,0,-1/9,0). The original mixed state equals (1/10)p+(9/10)z.

**Definition 1.19 (A globally proper attaining effect).**

$$\operatorname{attainer}\left(\right) = \operatorname{effect}\left(\frac{17}{50}, \operatorname{tuple}\left(\frac{12}{25}, 0, \frac{9}{50}, 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/TrigonometricMomentGap.attainer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On every curve point its value is ((3 cos(theta)+2)/5)^2. It lies in [0,1] on the whole curve and hence on the whole base. Its homogeneous extension is proper on the whole cone.

**Theorem 1.20 (An attained gap over all original confirming effects).**

$$\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\operatorname{base}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right) = \operatorname{image}\left(\operatorname{lift}\left(\right), \operatorname{body}\left(\right)\right) \land \operatorname{pure}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right) = \operatorname{range}\left(\operatorname{curve}\left(\right)\right)\right) \land \operatorname{IsCompact}\left(\operatorname{base}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right)\right)\right) \land \operatorname{IsCompact}\left(\operatorname{body}\left(\right)\right)\right) \land \operatorname{affineSpan}\left(\mathbb{R}, \operatorname{body}\left(\right)\right) = \operatorname{top}\left(\right)\right) \land \operatorname{finrank}\left(\mathbb{R}, \operatorname{vectorSpan}\left(\mathbb{R}, \operatorname{body}\left(\right)\right)\right) = 4\right) \land \operatorname{IsClosed}\left(\operatorname{carrier}\left(\operatorname{cone}\left(\right)\right)\right)\right) \land \operatorname{Salient}\left(\operatorname{cone}\left(\right)\right)\right) \land \operatorname{span}\left(\mathbb{R}, \operatorname{carrier}\left(\operatorname{cone}\left(\right)\right)\right) = \operatorname{top}\left(\right)\right) \land \left(\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall w \in \operatorname{Carrier}\left(\right),\; \left(w\in \operatorname{base}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right) \land \operatorname{apply}\left(\operatorname{pairSupport}\left(a, b\right), w\right) = 0\right) \Leftrightarrow w\in \operatorname{segment}\left(\mathbb{R}, \operatorname{curve}\left(a\right), \operatorname{curve}\left(b\right)\right)\right)\right) \land \left(\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \operatorname{pairBase}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right), \operatorname{curve}\left(a\right), \operatorname{curve}\left(b\right)\right) = \operatorname{segment}\left(\mathbb{R}, \operatorname{curve}\left(a\right), \operatorname{curve}\left(b\right)\right)\right)\right) \land \operatorname{wholePairBalls}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right)\right) \land \neg \operatorname{allAntipodes}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right)\right) \land \left(\forall f \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{Carrier}\left(\right), \mathbb{R}\right),\; \exists a \in \mathbb{R},\; \exists b \in \operatorname{Coordinates}\left(\right),\; f = \operatorname{effect}\left(a, b\right)\right)\right) \land \left(\forall a \in \mathbb{R},\; \forall b \in \operatorname{Coordinates}\left(\right),\; \operatorname{proper}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right), \operatorname{effect}\left(a, b\right)\right) \Leftrightarrow \left(\forall theta \in \mathbb{R},\; 0\leq \operatorname{trigonometric}\left(a, b, theta\right) \land \operatorname{trigonometric}\left(a, b, theta\right)\leq 1\right)\right)\right) \land \left(\forall w \in \operatorname{Carrier}\left(\right),\; w\in \operatorname{cone}\left(\right) \Rightarrow \left(w\neq 0 \Rightarrow 0< \operatorname{apply}\left(\operatorname{unit}\left(\right), w\right)\right)\right)\right) \land \operatorname{p}\left(\right)\in \operatorname{base}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right)\right) \land \operatorname{x}\left(\right)\in \operatorname{base}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right)\right) \land \operatorname{y}\left(\right)\in \operatorname{base}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right)\right) \land \operatorname{mixed}\left(\right)\in \operatorname{base}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right)\right) \land \operatorname{z}\left(\right)\in \operatorname{base}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right)\right) \land \left(0< \operatorname{angle}\left(\right) \land \operatorname{angle}\left(\right)< \operatorname{pi}\left(\right)\right)\right) \land \operatorname{cos}\left(\operatorname{angle}\left(\right)\right) = -\frac{2}{3}\right) \land \left(\forall f \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{Carrier}\left(\right), \mathbb{R}\right),\; \operatorname{confirms}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right), \operatorname{p}\left(\right), f\right) \Rightarrow \frac{1}{10}\leq \operatorname{apply}\left(f, \operatorname{mixed}\left(\right)\right)\right)\right) \land \operatorname{confirms}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right), \operatorname{p}\left(\right), \operatorname{attainer}\left(\right)\right)\right) \land \operatorname{apply}\left(\operatorname{attainer}\left(\right), \operatorname{mixed}\left(\right)\right) = \frac{1}{10}\right) \land \operatorname{comparison}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right), \operatorname{p}\left(\right), \operatorname{mixed}\left(\right)\right) = \frac{1}{10}\right) \land \left(\exists f \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{Carrier}\left(\right), \mathbb{R}\right),\; \operatorname{confirms}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right), \operatorname{p}\left(\right), f\right) \land \operatorname{apply}\left(f, \operatorname{x}\left(\right)\right) = 0\right)\right) \land \left(\exists f \in \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{Carrier}\left(\right), \mathbb{R}\right),\; \operatorname{confirms}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right), \operatorname{p}\left(\right), f\right) \land \operatorname{apply}\left(f, \operatorname{y}\left(\right)\right) = 0\right)\right) \land \neg \operatorname{zeroGluing}\left(\operatorname{cone}\left(\right), \operatorname{unit}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TrigonometricMomentGap.attained_full_effect_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base equals lift(body), and its entire extreme-point set equals the range of the complete normalized curve. Every linear effect has the stated five coefficients, and properness is equivalent to the global [0,1] trigonometric bounds. The body is compact and has full affine span in its four coordinates; the original homogeneous cone is closed, salient and generating, and the unit is strict. The entire minimal face of every pair is its segment, so all distinct original pure pairs satisfy wholePairBalls. Original global allAntipodes fails. All five displayed states belong to the original base. Every original proper confirmer of p reads at least 1/10 at mixed. The displayed attainer is itself an original proper confirmer and reads exactly 1/10 there. Thus the original sInf comparison equals 1/10, with its minimum attained. Proper cos-squared and half-one-plus-cos effects respectively exclude x and y. No original confirmer excludes their midpoint, so the original zeroGluing law fails.

For each real angle a, the first harmonic cos(theta-a) has a unique maximizing actual curve point. A strict supporting inequality extends through convex hull, and the pinned exposedPoints_subset_extremePoints theorem makes its unique maximizer extreme. Conversely, the pinned extremePoints_convexHull_subset theorem excludes all other extreme points. The continuous periodic curve has compact range. Caratheodory gives a representation by at most five points; the compact simplex and the finite product of the whole compact curve then give compactness of the whole hull. Five actual curve evaluations force any vanishing linear functional to vanish identically, proving full affine span and cone generation. Strict positivity gives salience, and compactness of the normalized base gives cone closedness by subsequential limits. The product support has zeros precisely at the two actual curve points; its zero-face equality extends through the entire hull and the intersection of all cone faces. The segment is affinely parametrized by the full closed one-dimensional ball. Global effect bounds extend by convexity and nonnegative homogeneous scaling. Values at five curve points bound every proper effect coefficient, giving a common modulus of variation near curve(0). A sufficiently close distinct curve point cannot be excluded by any original proper confirmer of curve(0). The explicit segment chart makes these two pure endpoints antipodes, contradicting the original allAntipodes predicate. The actual decomposition mixed=(1/10)p+(9/10)z yields the lower bound for every proper confirmer. The attaining polynomial gives equality, and the existing attained_comparison theorem identifies the original lower envelope.

The predecessor VII98.7 positive theorem in dimensions at most three is not supplied or reused here. Consequently this theorem does not certify the exact lowest-dimensional qualification in VII99.9.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.Carrier`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.Coordinates`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.angle`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.attained_full_effect_gap`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.attainer`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.body`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.cone`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.curve`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.effect`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.lift`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.mixed`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.momentCurve`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.p`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.pairSupport`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.states`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.trigonometric`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.unit`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.x`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.y`
- Truth anchor: `D5/S3/Quantum/Foundation/TrigonometricMomentGap.z`
- Dependency: [D5/S3/Quantum/Foundation/WeightedRelationConfirmation](WeightedRelationConfirmation.md)
- Dependency: [D5/S3/Quantum/Foundation/WholePairBallConfirmation](WholePairBallConfirmation.md)
