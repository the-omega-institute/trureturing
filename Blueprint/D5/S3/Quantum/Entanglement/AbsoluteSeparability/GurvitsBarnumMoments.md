# Corrected finite fourth moments

## Abstract

Finite fourth roots of unity, corrected by standard basis vectors, reproduce the two pairings of fourth moments.

For z indexed by Fin d, let q(T,z) be the sum of conjugate(z_i) z_j T_ij. Let L_d(f) be the sum of f over all vectors with coordinates in {1,i,-1,-i}, plus 4^d times the sum of f over the standard basis vectors. The basis term supplies the additional contribution when all four indices coincide. These formulas include d = 0.

**Definition 1.1 (The corrected phase sum).**

$$\forall (d:\mathbb{N}), \forall (f:(Fin\left(d\right) \to \mathbb{C}) \to \mathbb{C}), (designSum\left(f\right):\mathbb{C})=(\sum_{(z:(Fin\left(d\right) \to Fin\left(4\right)))} f\left((\lambda (i:Fin\left(d\right)) \mapsto phase\left(z\left(i\right)\right))\right))+(4:\mathbb{C})^{d}\cdot (\sum_{(a:Fin\left(d\right))} f\left((\lambda (i:Fin\left(d\right)) \mapsto if i=a then 1 else 0)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.designSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The corrected phase sum evaluates f at every phase vector indexed by a function Fin d to Fin 4, then adds 4^d times its sum over standard basis vectors. Here phase(s) is Complex.I raised to s.val. Both evaluation sums include all elements of their indicated finite types.

**Theorem 1.2 (Finite additivity).**

$$\forall (d:\mathbb{N}), \forall (J:Type), [Fintype\left(J\right)], \forall (f:J\to ((Fin\left(d\right)\to \mathbb{C})\to \mathbb{C})), L\left(d, \Lambda z, \sum_{a:J} f\left(a, z\right)\right)=\sum_{a:J} L\left(d, f\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.designSum_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both finite sums defining L commute with an additional finite sum.

**Theorem 1.3 (Real monotonicity).**

$$\forall (d:\mathbb{N}), \forall (f:(Fin\left(d\right)\to \mathbb{C})\to \mathbb{C}), \forall (g:(Fin\left(d\right)\to \mathbb{C})\to \mathbb{C}), (\forall (z:Fin\left(d\right)\to \mathbb{C}), Re\left(f\left(z\right)\right)\leq Re\left(g\left(z\right)\right))\Rightarrow Re\left(L\left(d, f\right)\right)\leq Re\left(L\left(d, g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.re_designSum_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every weight in L is nonnegative, so it preserves pointwise inequalities of real parts.

**Definition 1.4 (A finite complex quadratic form).**

$$\forall (d:\mathbb{N}), \forall (T:Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{C}\right)), \forall (z:Fin\left(d\right) \to \mathbb{C}), (quadratic\left(T, z\right):\mathbb{C})=\sum_{(i:Fin\left(d\right))} \sum_{(j:Fin\left(d\right))} conj\left(z\left(i\right)\right)\cdot z\left(j\right)\cdot T\left(i, j\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.quadratic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quadratic form contracts a vector on Fin d against a complex matrix by summing conjugate(z_i) z_j T_ij over both indices.

**Theorem 1.5 (Two quadratic forms).**

$$\forall (d:\mathbb{N}), \forall (T:Fin\left(d\right)\to Fin\left(d\right)\to \mathbb{C}), \forall (U:Fin\left(d\right)\to Fin\left(d\right)\to \mathbb{C}), L\left(d, \Lambda z, q\left(T, z\right)\cdot q\left(U, z\right)\right)=4^{d}\cdot (tr\left(T\right)\cdot tr\left(U\right)+\sum_{i:Fin\left(d\right)} \sum_{j:Fin\left(d\right)} T\left(i, j\right)\cdot U\left(j, i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.quadratic_product_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rotating one phase coordinate by i makes every unbalanced fourth moment vanish. The balanced terms give the product of traces and the crossed matrix product. The standard basis correction removes the double-counting deficit at coincident indices.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.designSum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.designSum_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.quadratic`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.quadratic_product_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments.re_designSum_mono`
