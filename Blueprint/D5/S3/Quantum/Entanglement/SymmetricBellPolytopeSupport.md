# Sharp half-circle sign sums and signed rotations

## Abstract

A maximizing sign vector on an equally spaced half-circle has one threshold. The sharp cosecant bound and its equality cases identify the signed rotations used to expose Bell-polytope vertices.

**Definition 1.1 (Real sign vectors).**

$$\forall n \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \operatorname{IsSign}\left(a\right) \Leftrightarrow (\forall i \in \operatorname{Fin}\left(n\right),\; (a\left(i\right) = 1) \lor (a\left(i\right) = -1))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.IsSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coordinate is exactly one or minus one.

**Definition 1.2 (Equally spaced half-circle directions).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{phase}\left(n, i\right) = \operatorname{Complex.exp}\left(\operatorname{Complex.ofReal}\left(\frac{\operatorname{Real.pi}}{n} \cdot \operatorname{val}\left(i\right)\right) \cdot \operatorname{Complex.I}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.phase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index i runs from zero through n-1. Real quotients are ordinary real division.

**Definition 1.3 (The primitive half-step phase).**

$$\forall n \in \mathbb{N},\; \operatorname{zeta}\left(n\right) = \operatorname{Complex.exp}\left(\operatorname{Complex.ofReal}\left(\frac{\operatorname{Real.pi}}{n}\right) \cdot \operatorname{Complex.I}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.zeta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This phase advances by pi/n.

**Definition 1.4 (The sharp radius).**

$$\forall n \in \mathbb{N},\; \operatorname{radius}\left(n\right) = \frac{1}{\operatorname{Real.sin}\left(\frac{\operatorname{Real.pi}}{2 \cdot n}\right)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.radius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The half-angle cosecant is the maximal signed-sum radius.

**Theorem 1.5 (A half-period gives minus one).**

$$\forall n \in \mathbb{N},\; (0 < n) \Rightarrow \operatorname{zeta}\left(n\right)^{n} = -1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.zeta_pow_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential completes a half-turn.

**Definition 1.6 (Frequency index reduction).**

$$\forall j \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(17\right),\; \operatorname{freqIndex}\left(j, x\right) = \operatorname{Fin.mk}\left(\operatorname{Nat.mod}\left(j \cdot \operatorname{val}\left(x\right), 17\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.freqIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Fin.mk proof that the residue is below seventeen is suppressed.

**Definition 1.7 (Frequency antiperiodic sign).**

$$\forall j \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(17\right),\; \operatorname{freqSign}\left(j, x\right) = (-1:\mathbb{R})^{\operatorname{Nat.div}\left(j \cdot \operatorname{val}\left(x\right), 17\right)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.freqSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.div is natural-number integer division.

**Definition 1.8 (Frequency directions).**

$$\forall j \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(17\right),\; \operatorname{freqPhase}\left(j, x\right) = \operatorname{zeta}\left(17\right)^{j \cdot \operatorname{val}\left(x\right)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.freqPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The odd frequencies below seventeen permute the half-circle directions up to sign.

**Theorem 1.9 (Reduced frequency directions).**

$$\forall j \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(17\right),\; \operatorname{freqPhase}\left(j, x\right) = \operatorname{Complex.ofReal}\left(\operatorname{freqSign}\left(j, x\right)\right) \cdot \operatorname{phase}\left(17, \operatorname{freqIndex}\left(j, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.freqPhase_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient supplies the sign and the remainder supplies the half-circle index.

**Theorem 1.10 (Frequency weights are signs).**

$$\forall j \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(17\right),\; (\operatorname{freqSign}\left(j, x\right) = 1) \lor (\operatorname{freqSign}\left(j, x\right) = -1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.freqSign_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An integer power of minus one is a sign.

**Theorem 1.11 (Sharp odd-frequency bound).**

$$\forall j \in \operatorname{Fin}\left(8\right),\; \forall a \in \operatorname{Fin}\left(17\right) \to \mathbb{R},\; (\operatorname{IsSign}\left(a\right)) \Rightarrow \Vert \operatorname{dotProduct}\left(\lambda i \mapsto \operatorname{Complex.ofReal}\left((a)\left(i\right)\right), \operatorname{freqPhase}\left(2 \cdot \operatorname{val}\left(j\right) + 1\right)\right)\Vert \le \operatorname{radius}\left(17\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.odd_frequency_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A maximizing sign vector is aligned with its sum. The half-circle ordering excludes alternating signs at three ordered directions; the signs have one threshold, whose geometric sum attains the cosecant radius.

**Definition 1.12 (Single-frequency sign patterns).**

$$\forall j \in \operatorname{Fin}\left(8\right),\; \forall x \in \operatorname{Fin}\left(17\right),\; \operatorname{baseSigns}\left(j, x\right) = \operatorname{Real.sign}\left(\operatorname{Real.cos}\left(\frac{\operatorname{Real.pi} \cdot \left(2 \cdot \operatorname{val}\left(j\right) + 1\right) \cdot \operatorname{val}\left(x\right)}{17}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.baseSigns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These real signs are the signs of the relevant cosines.

**Definition 1.13 (Signed input rotations).**

$$\forall j \in \operatorname{Fin}\left(8\right),\; \forall t \in \operatorname{Fin}\left(34\right),\; \forall x \in \operatorname{Fin}\left(17\right),\; \operatorname{rotatedSigns}\left(j, t, x\right) = \left(-1\right)^{\operatorname{Nat.div}\left(\operatorname{val}\left(x\right) + \operatorname{val}\left(t\right), 17\right)} \cdot \operatorname{baseSigns}\left(j, \operatorname{Fin.mk}\left(\operatorname{Nat.mod}\left(\operatorname{val}\left(x\right) + \operatorname{val}\left(t\right), 17\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.rotatedSigns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Thirty-four signed rotations combine seventeen cyclic shifts and sign reversal.

**Theorem 1.14 (Full signed period).**

$$\forall j \in \operatorname{Fin}\left(8\right),\; \forall t \in \mathbb{N},\; (\operatorname{zeta}\left(17\right)^{\left(2 \cdot \operatorname{val}\left(j\right) + 1\right) \cdot t} = 1) \Rightarrow 34 \mid t$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.frequency_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The odd frequencies one through fifteen are coprime to thirty-four.

**Theorem 1.15 (The base strategy attains the radius).**

$$\forall j \in \operatorname{Fin}\left(8\right),\; \operatorname{dotProduct}\left(\lambda i \mapsto \operatorname{Complex.ofReal}\left((\lambda (x:\operatorname{Fin}\left(17\right)) \mapsto (\operatorname{baseSigns}\left(j, x\right):\mathbb{R}))\left(i\right)\right), \operatorname{freqPhase}\left(2 \cdot \operatorname{val}\left(j\right) + 1\right)\right) = \operatorname{Complex.ofReal}\left(\operatorname{radius}\left(17\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.baseSigns_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing turns the base signs into a threshold at nine; its geometric sum is positive real.

**Theorem 1.16 (Phase of a signed rotation).**

$$\forall j \in \operatorname{Fin}\left(8\right),\; \forall t \in \operatorname{Fin}\left(34\right),\; \operatorname{dotProduct}\left(\lambda i \mapsto \operatorname{Complex.ofReal}\left((\lambda (x:\operatorname{Fin}\left(17\right)) \mapsto (\operatorname{rotatedSigns}\left(j, t, x\right):\mathbb{R}))\left(i\right)\right), \operatorname{freqPhase}\left(2 \cdot \operatorname{val}\left(j\right) + 1\right)\right) \cdot \operatorname{zeta}\left(17\right)^{\left(2 \cdot \operatorname{val}\left(j\right) + 1\right) \cdot \operatorname{val}\left(t\right)} = \operatorname{Complex.ofReal}\left(\operatorname{radius}\left(17\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.rotation_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A signed input rotation changes only the evaluation phase.

**Theorem 1.17 (All maximizers are signed rotations).**

$$\forall j \in \operatorname{Fin}\left(8\right),\; \forall a \in \operatorname{Fin}\left(17\right) \to \mathbb{R},\; (\operatorname{IsSign}\left(a\right)) \Rightarrow \left((\Vert \operatorname{dotProduct}\left(\lambda i \mapsto \operatorname{Complex.ofReal}\left((a)\left(i\right)\right), \operatorname{freqPhase}\left(2 \cdot \operatorname{val}\left(j\right) + 1\right)\right)\Vert = \operatorname{radius}\left(17\right)) \Rightarrow \left(\exists t \in \operatorname{Fin}\left(34\right),\; a = \lambda (x:\operatorname{Fin}\left(17\right)) \mapsto (\operatorname{rotatedSigns}\left(j, t, x\right):\mathbb{R})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.norm_maximizers_are_rotations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sharp half-circle equality characterization identifies every maximizing strategy with one of the thirty-four signed rotations.

**Theorem 1.18 (Positive radius).**

$$0 < \operatorname{radius}\left(17\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.radius17_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sine in the denominator is positive.

**Theorem 1.19 (Antiperiodic power reduction).**

$$\forall z \in \mathbb{C},\; \forall t \in \mathbb{N},\; (z^{17} = -1) \Rightarrow z^{t} = (-1:\mathbb{C})^{\operatorname{Nat.div}\left(t, 17\right)} \cdot z^{\operatorname{Nat.mod}\left(t, 17\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.root_reduce` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Natural division and remainder split the exponent into complete half-periods and a residue.

**Theorem 1.20 (Reflection of real power coordinates).**

$$\forall z \in \mathbb{C},\; \forall r \in \mathbb{N},\; (z^{17} = -1) \Rightarrow \left((\Vert z\Vert = 1) \Rightarrow \left((r \le 17) \Rightarrow \operatorname{Complex.re}\left(z^{17 - r}\right) = -\operatorname{Complex.re}\left(z^{r}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.root_reflect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit-norm antiperiodic root turns reflected powers into negative conjugates. Subtraction of natural exponents is truncated subtraction.

**Theorem 1.21 (Cosine signs on the half-circle).**

$$\forall x \in \operatorname{Fin}\left(17\right),\; ((\operatorname{val}\left(x\right) < 9) \Rightarrow 0 < \operatorname{Real.cos}\left(\frac{\operatorname{Real.pi}}{17} \cdot \operatorname{val}\left(x\right)\right)) \land ((\neg (\operatorname{val}\left(x\right) < 9)) \Rightarrow \operatorname{Real.cos}\left(\frac{\operatorname{Real.pi}}{17} \cdot \operatorname{val}\left(x\right)\right) < 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.halfcircle_cos_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first nine half-circle directions have positive cosine; the remaining eight have negative cosine.

**Theorem 1.22 (A point outside a finite candidate hull forces another extreme point).**

$$\forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)] [\operatorname{TopologicalSpace}\left(E\right)] [\operatorname{IsTopologicalAddGroup}\left(E\right)] [\operatorname{ContinuousSMul}\left(\mathbb{R}, E\right)] [\operatorname{T2Space}\left(E\right)] [\operatorname{LocallyConvexSpace}\left(\mathbb{R}, E\right)] \forall T \in \operatorname{Set}\left(E\right),\; \forall V \in \operatorname{Set}\left(E\right),\; \forall p \in E,\; (\operatorname{Set.Finite}\left(T\right)) \Rightarrow \left((p \in \operatorname{convexHull}\left(\mathbb{R}, T\right)) \Rightarrow \left((\neg (p \in \operatorname{convexHull}\left(\mathbb{R}, V\right))) \Rightarrow \left(\exists q \in E,\; (q \in \operatorname{Set.extremePoints}\left(\mathbb{R}, \operatorname{convexHull}\left(\mathbb{R}, T\right)\right)) \land (\neg (q \in V))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.extra_extreme_of_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite convex hull is the convex hull of its extreme points. Separation from the candidate hull therefore forces an extreme point outside the candidates.

**Theorem 1.23 (Nineteen extreme points exclude a nine-dimensional cross-polytope).**

$$\forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)] \forall S \in \operatorname{Set}\left(E\right),\; \forall g \in \operatorname{Fin}\left(19\right) \to E,\; (\operatorname{Convex}\left(\mathbb{R}, S\right)) \Rightarrow \left((\operatorname{Function.Injective}\left(g\right)) \Rightarrow \left((\forall i \in \operatorname{Fin}\left(19\right),\; g\left(i\right) \in \operatorname{Set.extremePoints}\left(\mathbb{R}, S\right)) \Rightarrow \left(\neg (\exists f \in E \to^{a}[\mathbb{R}]\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(9\right)\right),\; (\operatorname{Set.InjOn}\left(f, S\right)) \land (\operatorname{Set.image}\left(f, S\right) = \operatorname{convexHull}\left(\mathbb{R}, \operatorname{Set.range}\left(\lambda (i:\operatorname{Fin}\left(9\right)) \mapsto \operatorname{EuclideanSpace.single}\left(i, 1\right)\right)\cup\operatorname{Set.range}\left(\lambda (i:\operatorname{Fin}\left(9\right)) \mapsto -\operatorname{EuclideanSpace.single}\left(i, 1\right)\right)\right)))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.not_affine_cross_of_many_extreme` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An affine map injective on a convex set preserves extreme points. The cross-polytope has at most eighteen extreme points.

**Theorem 1.24 (Unique maximizers expose a singleton).**

$$\forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)] [\operatorname{TopologicalSpace}\left(E\right)] \forall T \in \operatorname{Set}\left(E\right),\; \forall l \in E \to_{\mathbb{R}}^{L}\mathbb{R},\; \forall v \in E,\; (v \in T) \Rightarrow \left((\forall x \in E,\; (x \in T) \Rightarrow \left((l\left(x\right) \le l\left(v\right)) \land ((l\left(x\right) = l\left(v\right)) \Rightarrow x = v)\right)) \Rightarrow \operatorname{IsExposed}\left(\mathbb{R}, \operatorname{convexHull}\left(\mathbb{R}, T\right), \operatorname{Set.singleton}\left(v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.exposed_hull_of_unique_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A linear functional with a unique maximum on the generating set has the same unique maximum on its convex hull.

**Theorem 1.25 (A cubic product bound).**

$$\forall R \in \mathbb{R},\; \forall x \in \mathbb{C},\; \forall y \in \mathbb{C},\; \forall z \in \mathbb{C},\; (0 < R) \Rightarrow \left((\Vert x\Vert \le R) \Rightarrow \left((\Vert y\Vert \le R) \Rightarrow \left((\Vert z\Vert \le R) \Rightarrow \operatorname{Complex.re}\left(x \cdot y \cdot z\right) \le R^{3}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.triple_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real part is bounded by the product of the three norms.

**Theorem 1.26 (Equality fixes all three norms and the product).**

$$\forall R \in \mathbb{R},\; \forall x \in \mathbb{C},\; \forall y \in \mathbb{C},\; \forall z \in \mathbb{C},\; (0 < R) \Rightarrow \left((\Vert x\Vert \le R) \Rightarrow \left((\Vert y\Vert \le R) \Rightarrow \left((\Vert z\Vert \le R) \Rightarrow \left((\operatorname{Complex.re}\left(x \cdot y \cdot z\right) = R^{3}) \Rightarrow \left((\Vert x\Vert = R) \land ((\Vert y\Vert = R) \land ((\Vert z\Vert = R) \land (x \cdot y \cdot z = \operatorname{Complex.ofReal}\left(R^{3}\right))))\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.triple_max_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality forces every norm to reach its upper bound and the product to be positive real.

**Theorem 1.27 (Sign reversal preserves unique maximization).**

$$\forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)] \forall T \in \operatorname{Set}\left(E\right),\; \forall l \in E \to_{\mathbb{R}}\mathbb{R},\; \forall v \in E,\; (\forall x \in E,\; (x \in T) \Rightarrow -x \in T) \Rightarrow \left((\forall x \in E,\; (x \in T) \Rightarrow \left((l\left(x\right) \le l\left(v\right)) \land ((l\left(x\right) = l\left(v\right)) \Rightarrow x = v)\right)) \Rightarrow \left(\forall x \in E,\; (x \in T) \Rightarrow \left((\left(-l\right)\left(x\right) \le \left(-l\right)\left(-v\right)) \land ((\left(-l\right)\left(x\right) = \left(-l\right)\left(-v\right)) \Rightarrow x = -v)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.negative_unique_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a centrally symmetric generating set, negating a maximizing functional negates its unique maximizer.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.IsSign`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.baseSigns`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.baseSigns_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.exposed_hull_of_unique_max`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.extra_extreme_of_separation`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.freqIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.freqPhase`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.freqPhase_decomposition`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.freqSign`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.freqSign_sign`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.frequency_order`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.halfcircle_cos_sign`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.negative_unique_max`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.norm_maximizers_are_rotations`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.not_affine_cross_of_many_extreme`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.odd_frequency_norm_le`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.phase`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.radius`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.radius17_pos`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.root_reduce`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.root_reflect`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.rotatedSigns`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.rotation_eval`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.triple_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.triple_max_value`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.zeta`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.zeta_pow_card`
