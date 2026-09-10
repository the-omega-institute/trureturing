# The centered Euclidean lower endpoint

## Abstract

Increasing coordinates cannot lower the mean-minus-centered-Euclidean-spread endpoint.

Let k be a natural number at least two. Coordinates are arbitrary real numbers, indexed by Fin(k), and every norm below is the Euclidean norm. Write e_i for the vector with coordinate one at i and zero elsewhere. Scalar multiplication and vector addition have their usual real meanings.

**Definition 1.1 (The Euclidean carrier).**

$$\forall k \in \mathbb{N}, \operatorname{E}\left(k\right) = \mathbb{R}^{k}$$

*Formalization.* `D5/S3/ArithSums/CenteredEuclideanEndpoint.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is EuclideanSpace over the reals. Its squared norm is the sum of coordinate squares, with no averaging factor.

**Definition 1.2 (The constant unit vector).**

$$\forall k \in \mathbb{N}, \forall j \in \operatorname{Fin}\left(k\right), \mathbf{1}_{j} = 1$$

*Formalization.* `D5/S3/ArithSums/CenteredEuclideanEndpoint.ones` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The symbol one denotes the vector whose every coordinate equals one.

**Definition 1.3 (The coordinate mean).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \operatorname{m}\left(x\right) = \frac{\sum_{j} x_{j}}{k}$$

*Formalization.* `D5/S3/ArithSums/CenteredEuclideanEndpoint.mean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mean is the finite arithmetic average of all k coordinates.

**Definition 1.4 (Centering removes the mean).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \operatorname{C}\left(x\right) = x - \operatorname{m}\left(x\right) \cdot \mathbf{1}$$

*Formalization.* `D5/S3/ArithSums/CenteredEuclideanEndpoint.center` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At coordinate j, C(x)_j=x_j-m(x). Thus C is the action of the matrix Id-(1/k) one one-transpose. It is linear and sends every constant vector to zero.

**Definition 1.5 (The positive normalizing denominator).**

$$\forall k \in \mathbb{N}, 2 \le k \implies d = \sqrt{k \cdot (k - 1)}$$

*Formalization.* `D5/S3/ArithSums/CenteredEuclideanEndpoint.denom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bound k>=2 gives k>0 and k-1>0, hence d>0. All divisions in the norm estimates therefore have positive denominators.

**Definition 1.6 (Mean minus centered spread).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \ell\left(x\right) = \operatorname{m}\left(x\right) - \frac{\Vert \operatorname{C}\left(x\right) \Vert}{d}$$

*Formalization.* `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The centered sum of squares is not divided by k inside the norm. The functional is defined here only with the stated dimension bound.

**Theorem 1.7 (The mean increment).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \forall i \in \operatorname{Fin}\left(k\right), \forall u \in \mathbb{R}, \operatorname{m}\left(x + u \cdot e_{i}\right) = \operatorname{m}\left(x\right) + \frac{u}{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.mean_add_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This algebraic identity holds for every real increment, including negative increments.

**Theorem 1.8 (The centered increment).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \forall i \in \operatorname{Fin}\left(k\right), \forall u \in \mathbb{R}, \operatorname{C}\left(x + u \cdot e_{i}\right) = \operatorname{C}\left(x\right) + u \cdot \operatorname{C}\left(e_{i}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.center_add_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Linearity of the finite average gives linearity of centering.

**Theorem 1.9 (The coordinate square calculation).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall i \in \operatorname{Fin}\left(k\right), \Vert \operatorname{C}\left(e_{i}\right) \Vert^{2} = (1 - \frac{1}{k})^{2} + \frac{k - 1}{k^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.norm_center_single_sq_expanded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distinguished coordinate is 1-1/k; each of the other k-1 coordinates is -1/k.

**Theorem 1.10 (The centered basis norm).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall i \in \operatorname{Fin}\left(k\right), \Vert \operatorname{C}\left(e_{i}\right) \Vert^{2} = \frac{k - 1}{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.norm_center_single_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalizing the expanded square sum gives a positive value, so C(e_i) is nonzero.

**Theorem 1.11 (The exact normalized basis length).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall i \in \operatorname{Fin}\left(k\right), \frac{\Vert \operatorname{C}\left(e_{i}\right) \Vert}{d} = \frac{1}{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.norm_center_single_div` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both sides have the required nonnegative signs. The square identity and d>0 give the exact ratio; no sign is lost by squaring.

**Theorem 1.12 (The kernel consists of constant vectors).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, (\operatorname{C}\left(x\right) = 0) \iff (\exists a \in \mathbb{R}, x = a \cdot \mathbf{1})$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.center_eq_zero_iff_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If centering vanishes, x=m(x) one. Conversely, a constant vector has its constant coordinate as mean and has zero centered norm.

**Theorem 1.13 (The exact endpoint increment).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \forall i \in \operatorname{Fin}\left(k\right), \forall u \in \mathbb{R}, \ell\left(x + u \cdot e_{i}\right) - \ell\left(x\right) = \frac{u}{k} - \frac{\Vert \operatorname{C}\left(x\right) + u \cdot \operatorname{C}\left(e_{i}\right) \Vert - \Vert \operatorname{C}\left(x\right) \Vert}{d}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_add_single_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This identity isolates the change in Euclidean norm and holds for every real u.

**Theorem 1.14 (A nonnegative coordinate increment cannot lower the endpoint).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \forall i \in \operatorname{Fin}\left(k\right), \forall u \in \mathbb{R}, 0 \le u \implies (\ell\left(x\right) \le \ell\left(x + u \cdot e_{i}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_le_add_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The triangle inequality bounds the norm increment by the norm of u C(e_i). For u>=0 this is u times the basis norm, whose ratio to d is 1/k. The mean increment therefore compensates for the entire possible norm increase.

**Theorem 1.15 (Zero increment gives equality for every vector).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \forall i \in \operatorname{Fin}\left(k\right), \ell\left(x + 0 \cdot e_{i}\right) = \ell\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_add_zero_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is no ray condition when u=0.

**Theorem 1.16 (Positive-increment equality is a nonnegative centered ray).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \forall i \in \operatorname{Fin}\left(k\right), \forall u \in \mathbb{R}, 0 < u \implies ((\ell\left(x + u \cdot e_{i}\right) = \ell\left(x\right)) \iff (\exists t \in \mathbb{R}, 0 \le t \land \operatorname{C}\left(x\right) = t \cdot \operatorname{C}\left(e_{i}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_add_single_eq_iff_centered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For u>0, the vector w=u C(e_i) is nonzero. Equality in the endpoint estimate is exactly equality in the triangle inequality for v=C(x) and w. In a real inner product space this is equivalent to v being a nonnegative multiple of w. The vector v may be zero, and the ray coefficient may be zero.

**Theorem 1.17 (Lifting the centered ray to a free translation).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \forall i \in \operatorname{Fin}\left(k\right), (\exists t \in \mathbb{R}, 0 \le t \land \operatorname{C}\left(x\right) = t \cdot \operatorname{C}\left(e_{i}\right)) \iff (\exists a \in \mathbb{R}, \exists t \in \mathbb{R}, 0 \le t \land x = a \cdot \mathbf{1} + t \cdot e_{i})$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.centered_ray_iff_translated_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting t e_i gives a vector in the centering kernel. Thus the same nonnegative coefficient t is retained, and x=a one+t e_i with a=m(x)-t/k. Conversely, the mean of that translated vector is a+t/k, so its centered part is t C(e_i). The offset a is any real number.

**Theorem 1.18 (The exact translated equality condition).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \forall i \in \operatorname{Fin}\left(k\right), \forall u \in \mathbb{R}, 0 < u \implies ((\ell\left(x + u \cdot e_{i}\right) = \ell\left(x\right)) \iff (\exists a \in \mathbb{R}, \exists t \in \mathbb{R}, 0 \le t \land x = a \cdot \mathbf{1} + t \cdot e_{i}))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_add_single_eq_iff_translated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining the centered equality criterion with the kernel characterization gives this equivalence. Taking t=0 includes every constant vector, including constants with negative coordinates.

**Theorem 1.19 (Coordinate order implies endpoint order).**

$$\forall k \in \mathbb{N}, 2 \le k \implies \forall x \in \mathbb{R}^{k}, \forall y \in \mathbb{R}^{k}, (\forall j \in \operatorname{Fin}\left(k\right), x_{j} \le y_{j}) \implies (\ell\left(x\right) \le \ell\left(y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_le_of_pointwise_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Insert the nonnegative coordinate increments y_j-x_j one at a time. The insertion criterion for finite-set monotonicity orders the partial sums, and the sum over all coordinates reconstructs y. This can supply lower bounds on arithmetic boxes without imposing arithmetic restrictions on this theorem.

The geometric ingredients are the real inner-product Cauchy-Schwarz bound, the squared norm expansion, the triangle inequality and its equality criterion. The equality criterion requires only the second vector to be nonzero; it does not exclude zero variance in x. No strict coordinate monotonicity is asserted.

## References

- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.E`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.center`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.center_add_single`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.center_eq_zero_iff_constant`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.centered_ray_iff_translated_single`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.denom`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_add_single_eq_iff_centered`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_add_single_eq_iff_translated`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_add_single_sub`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_add_zero_single`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_le_add_single`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.lower_le_of_pointwise_le`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.mean`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.mean_add_single`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.norm_center_single_div`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.norm_center_single_sq`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.norm_center_single_sq_expanded`
- Truth anchor: `D5/S3/ArithSums/CenteredEuclideanEndpoint.ones`
