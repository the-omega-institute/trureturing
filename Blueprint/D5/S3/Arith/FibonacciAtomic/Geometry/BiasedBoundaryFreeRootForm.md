# Actual Covariance and the Free-Root Form

## Abstract

The infinite path trace on the fixed biased boundary has compact covariance. The original free-root energy infimum is attained in the effective increment space, and its weak variational graph is determined by the actual covariance.

**Definition 1.1 (v).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.v`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector v is the adjoint of the actual bounded path trace J applied to the constant one in G=L2(M). The biased product measure and the infinite square-summable increment space are fixed throughout.

**Definition 1.2 (Sigma).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.Sigma`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.Sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sigma=C* C acts on the original infinite increment space H, where C=Pi J is included in the original ambient G. Taking this ambient adjoint is the same as extending the adjoint from the mean-zero boundary subspace by zero on constants.

**Definition 1.3 (K).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.K`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K is the orthogonal complement of the kernel of Sigma. Vectors in the edge kernel are excluded from this effective increment space.

**Theorem 1.4 (Compact Trace and Actual Covariance).**

$$(\operatorname{IsCompactOperator}\left(J\right))\land(\operatorname{IsCompactOperator}\left(C\right))\land(\operatorname{IsCompactOperator}\left(Sigma\right))\land(Sigma=\operatorname{compose}\left(\operatorname{adjoint}\left(J\right), J\right)-\operatorname{rankOne}\left(v, v\right))\land(\forall z: H, (\forall w: H, (\operatorname{inner}\left(z, \operatorname{Sigma}\left(w\right)\right)=\operatorname{inner}\left(\operatorname{C}\left(z\right), \operatorname{C}\left(w\right)\right))))\land(\forall z: H, (\operatorname{inner}\left(z, \operatorname{Sigma}\left(z\right)\right)=(\Vert \operatorname{C}\left(z\right) \Vert)^{2}))\land(\operatorname{ker}\left(Sigma\right)=\operatorname{ker}\left(C\right))\land(\forall p: Edge, (\forall q: Edge, (\operatorname{inner}\left(\operatorname{single}\left(2, p, 1\right), \operatorname{Sigma}\left(\operatorname{single}\left(2, q, 1\right)\right)\right)=\operatorname{Mreal}\left(\operatorname{intersection}\left(\operatorname{cylinder}\left(p\right), \operatorname{cylinder}\left(q\right)\right)\right)-\operatorname{product}\left(\operatorname{Mreal}\left(\operatorname{cylinder}\left(p\right)\right), \operatorname{Mreal}\left(\operatorname{cylinder}\left(q\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.actual_compact_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive epsilon, choose a stopping threshold at most both one half and epsilon squared divided by four times the golden ratio. The all-vector stopping residual bounds the operator norm of C minus Qt C by epsilon over two. The actual stopping range is finite dimensional, so norm closure of compact operators gives compactness of C. The difference J-C factors through the one-dimensional constant space; consequently J is compact too, and composing C with its bounded adjoint makes Sigma compact.

Self-adjoint centering and its idempotence give Sigma=J* J-v tensor v. For all z,w in H the bilinear covariance equals the inner product of their actual centered traces. In particular its quadratic form is the squared centered trace norm, and its kernel is exactly the kernel of C. On every pair of original unit edge vectors p,q, its entry is M([p] intersect [q])-M([p])M([q]).

**Theorem 1.5 (Centering Has Zero Mean).**

$$\forall F: G, (\operatorname{mean}\left(\operatorname{Pi}\left(F\right)\right)=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.mean_Pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Orthogonal centering subtracts the original integral mean, so every centered boundary vector has mean zero.

This is the mean-zero codomain condition for the actual centered trace.

The original BiasedBoundaryCentering.Pi_const identity removes every actual constant. In the free-root form, constants therefore require no effective increment.

**Theorem 1.6 (Idempotent Centering).**

$$\forall F: G, (\operatorname{Pi}\left(\operatorname{Pi}\left(F\right)\right)=\operatorname{Pi}\left(F\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.Pi_idem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A centered vector already has zero mean, so centering it again leaves it fixed.

This identity identifies covariance graph coordinates with centered boundary vectors.

**Theorem 1.7 (The Adjoint Lies in the Effective Edge Space).**

$$\forall h: G, (\operatorname{adjoint}\left(C, h\right)\in K)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.adjoint_mem_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every vector C*h is orthogonal to the original covariance kernel because pairing it with an edge vector z equals pairing h with Cz.

This effective-space inclusion is consumed by the positive eigenspace identification of the original boundary operator.

**Theorem 1.8 (Pairing with a Mean-Zero Vector).**

$$\forall h: G, (\forall F: G, (\operatorname{mean}\left(h\right)=0\implies (\operatorname{inner}\left(h, \operatorname{Pi}\left(F\right)\right)=\operatorname{inner}\left(h, F\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.inner_centered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A vector with zero mean is orthogonal to constants. Its inner product with any centered test vector equals its inner product with the original test vector.

The identity applies to every test vector in the original boundary L2 space.

**Definition 1.9 (D).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.D`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The domain D is exactly the subspace of all F=c times the constant one plus Jz, with arbitrary real root value c and arbitrary z in the original infinite H. No finite-level restriction or replacement measure enters this domain.

**Definition 1.10 (energy).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.energy`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an ambient F in G, energy(F) is the real infimum of the set of squared increment norms over all original representations F=constG(c)+Jz. Its asserted energy interpretation is restricted to F in D, where the set is nonempty and the infimum is attained.

**Definition 1.11 (lift).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.lift`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.lift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each F in D, lift(F) is the unique z in K such that Cz=Pi F. Orthogonal projection onto K removes exactly the redundant edge kernel.

**Theorem 1.12 (Attainment of the Original Energy).**

$$\forall F: D, ((\operatorname{lift}\left(F\right)\in K)\land(\operatorname{C}\left(\operatorname{lift}\left(F\right)\right)=\operatorname{Pi}\left(F\right))\land(F=\operatorname{constG}\left(\operatorname{mean}\left(F\right)-\operatorname{mean}\left(\operatorname{J}\left(\operatorname{lift}\left(F\right)\right)\right)\right)+\operatorname{J}\left(\operatorname{lift}\left(F\right)\right))\land(\operatorname{energy}\left(F\right)=(\Vert \operatorname{lift}\left(F\right) \Vert)^{2})\land(\forall c: \mathbb{R}, (\forall z: H, (F=\operatorname{constG}\left(c\right)+\operatorname{J}\left(z\right)\implies ((\operatorname{lift}\left(F\right)=\operatorname{starProjection}\left(K, z\right))\land((\Vert \operatorname{lift}\left(F\right) \Vert)^{2}\leq(\Vert z \Vert)^{2})))))\land(\forall z: H, ((z\in K)\land(\operatorname{C}\left(z\right)=\operatorname{Pi}\left(F\right))\implies z=\operatorname{lift}\left(F\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.free_root_least_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any representation F=constG(c)+Jz, the least increment is the orthogonal projection of z onto K. Projection leaves its centered trace unchanged and decreases its norm. Injectivity of C on K makes this increment independent of the chosen representation and unique in K.

The root coefficient is restored as mean(F)-mean(J lift(F)). This is an actual original representation and attains the infimum, so energy(F)=the squared norm of lift(F). Every other representation is included in the comparison.

**Definition 1.13 (form).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.form`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.form` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The form pairing of F and T in D is the real inner product of their least increments. Its diagonal is the original infimum energy, and its value is one quarter of energy(F+T)-energy(F-T), so it is the polarization of that original energy.

**Definition 1.14 (weakGraph).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.weakGraph`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.weakGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pair (u,h) lies in the weak graph when u belongs to the original D and the form pairing of u with every F in D equals the G inner product of h with F.

**Definition 1.15 (formSpace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.formSpace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.formSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The form domain in graph coordinates consists exactly of pairs (F,z) in G times the original H with z in K and Cz=Pi F. It is the closed graph of the unique least increment, hence is complete for the inherited product norm. Its increment norm squared is the original energy.

**Definition 1.16 (formInclusion).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.formInclusion`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.formInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inclusion of the original form domain into G is the first-coordinate map on formSpace. Its second-coordinate map is the unique least increment.

**Theorem 1.17 (The Entire Weak Variational Graph).**

$$(\forall F: D, (\operatorname{form}\left(F, F\right)=\operatorname{energy}\left(F\right)))\land(\forall F: D, (\forall T: D, (\operatorname{form}\left(F, T\right)=\frac{\operatorname{energy}\left(F+T\right)-\operatorname{energy}\left(F-T\right)}{4})))\land(\operatorname{IsClosed}\left(\operatorname{range}\left((F:D\mapsto\operatorname{pair}\left(F, \operatorname{lift}\left(F\right)\right))\right)\right))\land(\forall x: formSpace, (\exists F:D, (x=\operatorname{pair}\left(F, \operatorname{lift}\left(F\right)\right))\land(\operatorname{energy}\left(F\right)=(\Vert \operatorname{snd}\left(x\right) \Vert)^{2})))\land(\operatorname{IsCompactOperator}\left(formInclusion\right))\land(\forall u: G, (\forall h: G, (\operatorname{weakGraph}\left(u, h\right)\iff(\operatorname{mean}\left(h\right)=0)\land(u=\operatorname{constG}\left(\operatorname{mean}\left(u\right)\right)+\operatorname{C}\left(\operatorname{apply}\left(\operatorname{adjoint}\left(C\right), h\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.free_root_variational_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The form diagonal equals the original free-root energy on every element of D. Uniqueness of the effective lift makes it additive and subtractive; the real inner-product polarization identity identifies this pairing with the polarization of the original infimum. The graph of F mapped to (F,lift(F)) is closed in G times H: it is exactly the closed constraint set z in K and Cz=Pi F. In these complete graph coordinates, the actual inclusion equals the compact map C applied to the increment coordinate plus the constant map applied to the mean of the trace coordinate. Thus the original form-domain inclusion is compact. The weak equation holds for all original traces exactly when mean(h)=0 and u=constG(mean(u))+CC*h. Testing constants forces mean(h)=0; testing every Jz identifies the least increment of u with C*h. Conversely C*h belongs to K, and the stated covariance representation satisfies the equation against every F in D.

This module characterizes the entire weak graph without assuming an operator realization. BiasedBoundaryOperator constructs its dense self-adjoint realization, compact resolvent and positive covariance eigenspace identification. The complete ordered spectral sequence, the unitary polar map, its two range-domain identities and global eigenvalue counting require additional arguments.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.D`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.K`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.Pi_idem`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.Sigma`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.actual_compact_covariance`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.adjoint_mem_K`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.energy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.form`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.formInclusion`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.formSpace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.free_root_least_energy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.free_root_variational_graph`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.inner_centered`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.lift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.mean_Pi`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.v`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.weakGraph`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping](BiasedBoundaryStopping.md)
