# Global Integer Character Coercivity

## Abstract

A finite integer character defect controls squared Euclidean distance to its full periodic zero set.

**Theorem 1.1 (Uniform quadratic distance bound).**

$$\forall q \in \mathbb{N},\; \forall I \in \operatorname{FiniteType}\left(\right),\; \forall lambda \in I \Rightarrow \operatorname{Fin}\left(q\right) \Rightarrow \mathbb{Z},\; \exists c \in \mathbb{R},\; 0 < c \land \left(\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(q\right)\right),\; c \cdot \operatorname{infDist}\left(x, \left\{y \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(q\right)\right) \mid \forall a \in I,\; \exists k \in \mathbb{Z},\; \sum_{i\in \operatorname{Fin}\left(q\right)} \operatorname{lambda}\left(a, i\right) \cdot \operatorname{coord}\left(y, i\right) = 2 \cdot \operatorname{pi}\left(\right) \cdot k\right\}\right)^{2} \le \sum_{a\in I} (1 - \operatorname{cos}\left(\sum_{i\in \operatorname{Fin}\left(q\right)} \operatorname{lambda}\left(a, i\right) \cdot \operatorname{coord}\left(x, i\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/IntegerCharacterCoercivity.integer_character_global_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural dimension q, every finite index type I, and every integer row family lambda indexed by I and Fin(q), there is a positive real constant c that works for every vector x in the actual Euclidean space. Each phase is the real sum of lambda(a,i) times x(i). The set inside infDist contains every vector whose phases are all integral multiples of 2 pi; the integer may depend on the row.

No nonemptiness, rank, injectivity, or primitive-image assumption is required. The assertion includes dimension zero, an empty family, zero rows, rank deficiency, and all disconnected periodic components. For the one-dimensional charge 2, pi is a zero as well as 2 pi.

A bounded preimage for the linear phase map gives a uniform distance bound to each affine kernel fiber. In a uniform neighborhood of any periodic zero y, the scalar cosine inequality bounds the sum of squared phases of x - y. On the part of the compact cube at least a fixed positive distance from the full zero set, continuity gives a uniform positive lower bound for the defect, vacuously when that part is empty. Translations by 2 pi times integer coordinate vectors preserve both the defect and distance to the full zero set, extending the bound to every vector.

This is a deterministic analytic inequality for the explicitly displayed periodic zero set. It does not identify that set with a Markov model's gauge subgroup or prove Gaussian decay of Markov powers. Actual-path synchronization and the gauge identification are separate obligations.

## References

- Truth anchor: `D5/S3/Fourier/IntegerCharacterCoercivity.integer_character_global_coercivity`
