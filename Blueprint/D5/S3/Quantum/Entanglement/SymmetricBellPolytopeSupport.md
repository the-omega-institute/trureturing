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

**Definition 1.3 (The sharp radius).**

$$\forall n \in \mathbb{N},\; \operatorname{radius}\left(n\right) = \frac{1}{\operatorname{Real.sin}\left(\frac{\operatorname{Real.pi}}{2 \cdot n}\right)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.radius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The half-angle cosecant is the maximal signed-sum radius.

**Theorem 1.4 (A half-period gives minus one).**

$$\forall n \in \mathbb{N},\; (0 < n) \Rightarrow \operatorname{ErewGoldsteinSICStabilizerRefutation.zeta}\left(n\right)^{n} = -1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.zeta_pow_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential completes a half-turn.

**Theorem 1.5 (A point outside a finite candidate hull forces another extreme point).**

$$\forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)] [\operatorname{TopologicalSpace}\left(E\right)] [\operatorname{IsTopologicalAddGroup}\left(E\right)] [\operatorname{ContinuousSMul}\left(\mathbb{R}, E\right)] [\operatorname{T2Space}\left(E\right)] [\operatorname{LocallyConvexSpace}\left(\mathbb{R}, E\right)] \forall T \in \operatorname{Set}\left(E\right),\; \forall V \in \operatorname{Set}\left(E\right),\; \forall p \in E,\; (\operatorname{Set.Finite}\left(T\right)) \Rightarrow \left((p \in \operatorname{convexHull}\left(\mathbb{R}, T\right)) \Rightarrow \left((\neg (p \in \operatorname{convexHull}\left(\mathbb{R}, V\right))) \Rightarrow \left(\exists q \in E,\; (q \in \operatorname{Set.extremePoints}\left(\mathbb{R}, \operatorname{convexHull}\left(\mathbb{R}, T\right)\right)) \land (\neg (q \in V))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.extra_extreme_of_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite convex hull is the convex hull of its extreme points. Separation from the candidate hull therefore forces an extreme point outside the candidates.

**Theorem 1.6 (Unique maximizers expose a singleton).**

$$\forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)] [\operatorname{TopologicalSpace}\left(E\right)] \forall T \in \operatorname{Set}\left(E\right),\; \forall l \in E \to_{\mathbb{R}}^{L}\mathbb{R},\; \forall v \in E,\; (v \in T) \Rightarrow \left((\forall x \in E,\; (x \in T) \Rightarrow \left((l\left(x\right) \le l\left(v\right)) \land ((l\left(x\right) = l\left(v\right)) \Rightarrow x = v)\right)) \Rightarrow \operatorname{IsExposed}\left(\mathbb{R}, \operatorname{convexHull}\left(\mathbb{R}, T\right), \operatorname{Set.singleton}\left(v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.exposed_hull_of_unique_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A linear functional with a unique maximum on the generating set has the same unique maximum on its convex hull.

**Theorem 1.7 (A cubic product bound).**

$$\forall R \in \mathbb{R},\; \forall x \in \mathbb{C},\; \forall y \in \mathbb{C},\; \forall z \in \mathbb{C},\; (0 < R) \Rightarrow \left((\Vert x\Vert \le R) \Rightarrow \left((\Vert y\Vert \le R) \Rightarrow \left((\Vert z\Vert \le R) \Rightarrow \operatorname{Complex.re}\left(x \cdot y \cdot z\right) \le R^{3}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.triple_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real part is bounded by the product of the three norms.

**Theorem 1.8 (Equality fixes all three norms and the product).**

$$\forall R \in \mathbb{R},\; \forall x \in \mathbb{C},\; \forall y \in \mathbb{C},\; \forall z \in \mathbb{C},\; (0 < R) \Rightarrow \left((\Vert x\Vert \le R) \Rightarrow \left((\Vert y\Vert \le R) \Rightarrow \left((\Vert z\Vert \le R) \Rightarrow \left((\operatorname{Complex.re}\left(x \cdot y \cdot z\right) = R^{3}) \Rightarrow \left((\Vert x\Vert = R) \land ((\Vert y\Vert = R) \land ((\Vert z\Vert = R) \land (x \cdot y \cdot z = \operatorname{Complex.ofReal}\left(R^{3}\right))))\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.triple_max_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality forces every norm to reach its upper bound and the product to be positive real.

**Theorem 1.9 (Sign reversal preserves unique maximization).**

$$\forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)] \forall T \in \operatorname{Set}\left(E\right),\; \forall l \in E \to_{\mathbb{R}}\mathbb{R},\; \forall v \in E,\; (\forall x \in E,\; (x \in T) \Rightarrow -x \in T) \Rightarrow \left((\forall x \in E,\; (x \in T) \Rightarrow \left((l\left(x\right) \le l\left(v\right)) \land ((l\left(x\right) = l\left(v\right)) \Rightarrow x = v)\right)) \Rightarrow \left(\forall x \in E,\; (x \in T) \Rightarrow \left((\left(-l\right)\left(x\right) \le \left(-l\right)\left(-v\right)) \land ((\left(-l\right)\left(x\right) = \left(-l\right)\left(-v\right)) \Rightarrow x = -v)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.negative_unique_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a centrally symmetric generating set, negating a maximizing functional negates its unique maximizer.

**Definition 1.10 (Signed thresholds).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall s \in \mathbb{R},\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{threshold}\left(n, k, s\right)\left(i\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) < k, s, -s\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.threshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A cut k gives the constant sign s before the cut and its negative after it.

**Theorem 1.11 (Half-circle phases as powers).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{phase}\left(n, i\right) = \operatorname{D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation.zeta}\left(n\right)^{\operatorname{val}\left(i\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.phase_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The half-circle phase is a power of the half-period root.

**Theorem 1.12 (The threshold sum).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall s \in \mathbb{R},\; (0 < n) \Rightarrow \left((k \le n) \Rightarrow \operatorname{dotProduct}\left(\lambda (i:\operatorname{Fin}\left(n\right)) \mapsto \operatorname{Complex.ofReal}\left(\operatorname{threshold}\left(n, k, s\right)\left(i\right)\right), \operatorname{phase}\left(n\right)\right) = \operatorname{Complex.ofReal}\left(s\right) \cdot \frac{2 \cdot \operatorname{D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation.zeta}\left(n\right)^{k}}{\operatorname{D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation.zeta}\left(n\right) - 1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.threshold_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two geometric sums reduce to a single root power.

**Theorem 1.13 (Every threshold attains the radius).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall s \in \mathbb{R},\; (2 \le n) \Rightarrow \left((k \le n) \Rightarrow \left(((s = 1) \lor (s = -1)) \Rightarrow \operatorname{norm}\left(\operatorname{dotProduct}\left(\lambda (i:\operatorname{Fin}\left(n\right)) \mapsto \operatorname{Complex.ofReal}\left(\operatorname{threshold}\left(n, k, s\right)\left(i\right)\right), \operatorname{phase}\left(n\right)\right)\right) = \operatorname{radius}\left(n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.threshold_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The denominator has norm twice the sine of the half angle.

**Theorem 1.14 (Sharp half-circle bound).**

$$\forall n \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; (2 \le n) \Rightarrow \left((\operatorname{IsSign}\left(a\right)) \Rightarrow \operatorname{norm}\left(\operatorname{dotProduct}\left(\lambda (i:\operatorname{Fin}\left(n\right)) \mapsto \operatorname{Complex.ofReal}\left(a\left(i\right)\right), \operatorname{phase}\left(n\right)\right)\right) \le \operatorname{radius}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.sharp_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complex argument alignment turns the norm into a real projection. PeritoUnitCircleSum.abs_cos_sum_le bounds the resulting absolute cosine sum.

**Theorem 1.15 (Sharp half-circle equality characterization).**

$$\forall n \in \mathbb{N},\; \forall a \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; (2 \le n) \Rightarrow \left((\operatorname{IsSign}\left(a\right)) \Rightarrow \left(\operatorname{norm}\left(\operatorname{dotProduct}\left(\lambda (i:\operatorname{Fin}\left(n\right)) \mapsto \operatorname{Complex.ofReal}\left(a\left(i\right)\right), \operatorname{phase}\left(n\right)\right)\right) = \operatorname{radius}\left(n\right) \Leftrightarrow (\exists k \in \mathbb{N},\; (k \le n) \land (\exists s \in \mathbb{R},\; ((s = 1) \lor (s = -1)) \land (\forall i \in \operatorname{Fin}\left(n\right),\; a\left(i\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) < k, s, -s\right))))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.sharp_norm_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A maximizing sign vector has positive alignment with every signed phase. Positive interpolation between three directions excludes alternation; the first sign change supplies the cut. Conversely, every signed threshold attains the radius.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.IsSign`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.exposed_hull_of_unique_max`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.extra_extreme_of_separation`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.negative_unique_max`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.phase`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.phase_pow`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.radius`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.sharp_norm_eq_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.sharp_norm_le`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.threshold`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.threshold_norm`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.threshold_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.triple_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.triple_max_value`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.zeta_pow_card`
- Dependency: [D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation](../Magic/ErewGoldsteinSICStabilizerRefutation.md)
- Dependency: [D5/S3/QuantumBounds/PeritoUnitCircleSum](../../QuantumBounds/PeritoUnitCircleSum.md)
