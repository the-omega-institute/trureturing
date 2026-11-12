# Whole pair balls and global least confirmation

## Abstract

Entire minimal-face balls and one common positive support per pure point construct reciprocal least confirming effects on the original cone.

Let V be a finite dimensional real normed space and C the original closed cone. Its real span is V, and the original real-linear unit u is strictly positive on every nonzero point of C. The entire base K, all global pure points P and the entire proper-effect interval are precisely CircuitBalancedConfirmation.base, pure and proper. Strict positivity excludes nonzero lines. The theorem also holds for the zero carrier, and hence includes every original nonzero carrier. Neither a proper upper bound for the supplied supports, least confirmation, reciprocity, effect extension, projectivity, spectrality nor a Jordan representation is assumed.

**Definition 1.1 (The entire smallest cone-face base).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall p \in V,\; \forall q \in V,\; \forall x \in V,\; x\in \operatorname{pairBase}\left(C, u, p, q\right) \Leftrightarrow \left(x\in \operatorname{base}\left(C, u\right) \land \left(\forall F \in \operatorname{Face}\left(C\right),\; p\in F \Rightarrow \left(q\in F \Rightarrow x\in F\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/WholePairBallConfirmation.pairBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Membership requires normalized positivity and membership in every original cone face containing p and q. This is the intersection defining the smallest cone face; no selected patch, section or exposed-face replacement is used.

**Definition 1.2 (All entire pair bases are finite balls).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{wholePairBalls}\left(C, u\right) \Leftrightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall q \in \operatorname{pure}\left(C, u\right),\; p\neq q \Rightarrow \operatorname{Nonempty}\left(\operatorname{BallChart}\left(C, u, p, q\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/WholePairBallConfirmation.wholePairBalls` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A BallChart has a natural dimension d greater than zero, an affine map from EuclideanSpace R (Fin d) to the original V, injectivity on that entire Euclidean space, and equality of the image of the entire closed unit ball with pairBase(C,u,p,q). These are its only fields. Sphere purity, properness and leastness are conclusions. The dimension may vary with the pair; d=1, including classical segments, is retained.

**Definition 1.3 (One global positive support for all local antipodes).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{commonSupport}\left(C, u\right) \Leftrightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \exists g \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \left(\forall x \in V,\; x\in C \Rightarrow 0\leq \operatorname{apply}\left(g, x\right)\right) \land \left(0< \operatorname{apply}\left(g, p\right) \land \left(\forall q \in \operatorname{pure}\left(C, u\right),\; p\neq q \Rightarrow \left(\forall b \in \operatorname{BallChart}\left(C, u, p, q\right),\; \forall n \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(\operatorname{dim}\left(b\right)\right)\right),\; \Vert n\Vert = 1 \Rightarrow \left(\operatorname{apply}\left(\operatorname{param}\left(b\right), n\right) = p \Rightarrow \operatorname{apply}\left(g, \operatorname{apply}\left(\operatorname{param}\left(b\right), -n\right)\right) = 0\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/WholePairBallConfirmation.commonSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same real-linear g for p is nonnegative on the entire original cone, is strictly positive at p, and vanishes at p's antipode in every admissible chart for every distinct pure q. Quantification over all admissible charts avoids dependence on a chosen coordinate system. No upper bound by u is supplied. In a singleton base the pair quantifier is empty.

**Definition 1.4 (Normalize the single global support).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall h \in \operatorname{commonSupport}\left(C, u\right),\; \forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{supportEffect}\left(h, p\right) = \operatorname{inverse}\left(\operatorname{apply}\left(\operatorname{choose}\left(\operatorname{apply}\left(h, p\right)\right), p\right)\right)\cdot\operatorname{choose}\left(\operatorname{apply}\left(h, p\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/WholePairBallConfirmation.supportEffect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose the support given by h at p once and divide that same functional by its strictly positive reading at p. All local restrictions belong to this one global functional. Its properness is proved subsequently.

**Definition 1.5 (The original binary zero relation).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall p \in V,\; \forall x \in V,\; \operatorname{excludes}\left(C, u, p, x\right) \Leftrightarrow \left(\exists f \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{confirms}\left(C, u, p, f\right) \land \operatorname{apply}\left(f, x\right) = 0\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/WholePairBallConfirmation.excludes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exists one original globally proper effect f confirming p and vanishing at x. This definition is used on normalized mixed x and on positive nonnormalized vectors; the latter extension does not impose normalization.

**Definition 1.6 (Zero midpoint closure for all mixed states).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{zeroMidpoint}\left(C, u\right) \Leftrightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall x \in V,\; \forall y \in V,\; x\in \operatorname{base}\left(C, u\right) \Rightarrow \left(y\in \operatorname{base}\left(C, u\right) \Rightarrow \left(\operatorname{excludes}\left(C, u, p, x\right) \Rightarrow \left(\operatorname{excludes}\left(C, u, p, y\right) \Rightarrow \operatorname{excludes}\left(C, u, p, \frac{1}{2}\cdot(x+y)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/WholePairBallConfirmation.zeroMidpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two initial mixed states may have different exclusion witnesses. The midpoint obtains a single confirming witness from the constructed least effect.

**Definition 1.7 (Every pure point in every entire pair ball).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{allAntipodes}\left(C, u\right) \Leftrightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall q \in \operatorname{pure}\left(C, u\right),\; p\neq q \Rightarrow \left(\forall b \in \operatorname{BallChart}\left(C, u, p, q\right),\; \forall n \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(\operatorname{dim}\left(b\right)\right)\right),\; \Vert n\Vert = 1 \Rightarrow \left(\operatorname{apply}\left(\operatorname{param}\left(b\right), n\right)\in \operatorname{pure}\left(C, u\right) \Rightarrow \operatorname{excludes}\left(C, u, \operatorname{apply}\left(\operatorname{param}\left(b\right), n\right), \operatorname{apply}\left(\operatorname{param}\left(b\right), -n\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/WholePairBallConfirmation.allAntipodes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every unit-sphere point in every entire pair ball, including pure points other than the original p and q, globally excludes its antipode. The proof also establishes that all sphere points are global pure points, so the explicit purity premise discards no sphere point.

**Theorem 1.8 (Construct reciprocal least confirmation).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{wholePairBalls}\left(C, u\right) \Rightarrow \left(\forall h \in \operatorname{commonSupport}\left(C, u\right),\; \operatorname{reciprocalLeast}\left(C, u\right) \land \left(\operatorname{fullMixture}\left(C, u\right) \land \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall x \in V,\; x\in \operatorname{base}\left(C, u\right) \Rightarrow \left(\operatorname{excludes}\left(C, u, p, x\right) \Leftrightarrow \operatorname{apply}\left(\operatorname{supportEffect}\left(h, p\right), x\right) = 0\right)\right) \land \left(\operatorname{zeroMidpoint}\left(C, u\right) \land \left(\operatorname{allAntipodes}\left(C, u\right) \land \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall n \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(n\right)\to V,\; \forall w \in \operatorname{Fin}\left(n\right)\to \mathbb{R},\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{apply}\left(x, i\right)\in \operatorname{base}\left(C, u\right)\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; 0\leq \operatorname{apply}\left(w, i\right)\right) \Rightarrow \left(\operatorname{sum}\left(w\right) = 1 \Rightarrow \left(\operatorname{excludes}\left(C, u, p, \operatorname{weightedSum}\left(w, x\right)\right) \Leftrightarrow \left(\forall i \in \operatorname{Fin}\left(n\right),\; 0< \operatorname{apply}\left(w, i\right) \Rightarrow \operatorname{excludes}\left(C, u, p, \operatorname{apply}\left(x, i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/WholePairBallConfirmation.whole_pair_ball_confirmation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the original closed generating cone and strict unit, all entire pair balls B and the common-support condition H. Then reciprocalLeast and fullMixture hold on the original carrier. For every pure p and every mixed x in K, binary exclusion is equivalent to the constructed effect vanishing at x. The zero midpoint property and all-quantifier antipodal exclusion hold. For every natural n, arbitrary original mixed list x indexed by Fin n, and nonnegative weights summing to one, exclusion of their weighted sum is equivalent to exclusion of each positive-weight term. Repeated labels and zero weights are retained. weightedSum denotes the sum of w(i) times x(i).

For a nonnegative affine scalar function on a closed ball, write its linear part as inner(v,s). Evaluation at minus the normalized v yields a>=norm(v), including v=0. Zero at minus the unit n forces a=inner(v,n)=norm(v), so the Cauchy-Schwarz equality criterion gives v=a n. Normalizing the global support therefore yields (1+inner(n,s))/2 on every entire pair ball. These bounds at every global pure point extend to properness on the entire cone through the original cone_bound. Applying the same scalar argument to one minus any proper confirmer shows domination on each ball; nonneg_on_cone extends it to whole-cone leastness. Interchanging endpoints in the same chart gives reciprocity. The original circuit/mixture equivalence supplies fullMixture.

A cone face cuts out an extreme subset of the original base. Affine transport and the extreme-point theorem for Euclidean closed balls identify all sphere points as global pure points. For any such a and its antipode r, their midpoint is the ball center. Any cone face containing a and r contains this center; writing the center as the midpoint of any x in the ball and its opposite forces that face to contain every x. Thus the entire pair base of a,r equals the original entire ball. H applied to this pair gives the full antipodal conclusion. Leastness and the least effect itself give both directions of the mixed-state zero characterization. Nonnegative finite sums give the positive-weight characterization; the midpoint is its direct linear consequence.

For the singleton base, the global support normalized at its only pure point still works: the construction never chooses a distinct pair in the equal-point branch. Zero effects, zero vectors and zero weights are retained in cone inequalities and finite sums. The theorem proves the forward construction of Quantum Origin V 88.10 and its stated zero consequences. It does not prove the converse from S to the ball conditions, the general finite EJA bridge, 88.3, 88.11 or any physical source, PRE, CP, H13/C13 or other chapter 87 consumer. No literature priority is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/WholePairBallConfirmation.allAntipodes`
- Truth anchor: `D5/S3/Quantum/Foundation/WholePairBallConfirmation.commonSupport`
- Truth anchor: `D5/S3/Quantum/Foundation/WholePairBallConfirmation.excludes`
- Truth anchor: `D5/S3/Quantum/Foundation/WholePairBallConfirmation.pairBase`
- Truth anchor: `D5/S3/Quantum/Foundation/WholePairBallConfirmation.supportEffect`
- Truth anchor: `D5/S3/Quantum/Foundation/WholePairBallConfirmation.wholePairBalls`
- Truth anchor: `D5/S3/Quantum/Foundation/WholePairBallConfirmation.whole_pair_ball_confirmation`
- Truth anchor: `D5/S3/Quantum/Foundation/WholePairBallConfirmation.zeroMidpoint`
- Dependency: [D5/S3/Quantum/Foundation/CircuitBalancedConfirmation](CircuitBalancedConfirmation.md)
