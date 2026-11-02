# Finite oriented anchor rigidity

## Abstract

Finite oriented anchors determine an arbitrary complete actual output.

**Theorem 1.1 (Complete intensity and one-sided anchor comparisons force linear isometry).**

$$\forall d \in \mathbb{N},\; (1 \le d) \Rightarrow (\forall H \in Type,\; ((\operatorname{NormedAddCommGroup}\left(H\right)) \land ((\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)) \land (\operatorname{FiniteDimensional}\left(\mathbb{C}, H\right)))) \Rightarrow (\forall E \in Type,\; (\operatorname{Fintype}\left(E\right)) \Rightarrow (\forall W \in (E) \to (Type),\; (\forall e \in E,\; (\operatorname{NormedAddCommGroup}\left(W\left(e\right)\right)) \land ((\operatorname{InnerProductSpace}\left(\mathbb{C}, W\left(e\right)\right)) \land (\operatorname{FiniteDimensional}\left(\mathbb{C}, W\left(e\right)\right)))) \Rightarrow (\forall a \in \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(d\right), \mathbb{C}, H\right),\; \forall F \in (H) \to (\operatorname{PiLp}\left(2, W\right)),\; ((\forall x \in H,\; \sum_{e:E} \Vert F\left(x\right)\left(e\right) \Vert^{2} = \Vert x \Vert^{2}) \land ((\forall j \in \operatorname{Fin}\left(d\right),\; \forall k \in \operatorname{Fin}\left(4\right),\; \forall e \in E,\; F\left(\operatorname{smul}\left(i^{\operatorname{val}\left(k\right)}, a\left(j\right)\right)\right)\left(e\right) = \operatorname{smul}\left(i^{\operatorname{val}\left(k\right)}, F\left(a\left(j\right)\right)\left(e\right)\right)) \land (\forall x \in H,\; \forall j \in \operatorname{Fin}\left(d\right),\; \forall k \in \operatorname{Fin}\left(4\right),\; \sum_{e:E} \Vert (F\left(x\right)\left(e\right)) - (F\left(\operatorname{smul}\left(i^{\operatorname{val}\left(k\right)}, a\left(j\right)\right)\right)\left(e\right)) \Vert^{2} \le \Vert (x) - (\operatorname{smul}\left(i^{\operatorname{val}\left(k\right)}, a\left(j\right)\right)) \Vert^{2}))) \Rightarrow (\exists V \in \operatorname{LinearIsometry}\left(\mathbb{C}, H, \operatorname{PiLp}\left(2, W\right)\right),\; ((\forall x \in H,\; F\left(x\right) = V\left(x\right)) \land (\operatorname{comp}\left(\operatorname{adjoint}\left(V\right), \operatorname{toLinearMap}\left(V\right)\right) = \operatorname{id}\left(H\right))) \land (\forall U \in \operatorname{LinearIsometry}\left(\mathbb{C}, H, \operatorname{PiLp}\left(2, W\right)\right),\; ((\forall x \in H,\; F\left(x\right) = U\left(x\right)) \land (\operatorname{comp}\left(\operatorname{adjoint}\left(U\right), \operatorname{toLinearMap}\left(U\right)\right) = \operatorname{id}\left(H\right))) \Rightarrow (U = V)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteOrientedAnchorRigidity.finite_oriented_anchor_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a complex Hilbert space of dimension d at least one, with a specified orthonormal basis a indexed by Fin d. Let E be the finite complete outcome menu, and let W_e be finite-dimensional complex Hilbert spaces. The output PiLp 2 W is their Hilbert direct sum, so its squared norm is the sum of the squared channel norms. Write F_e(x)=(F(x))_e for a single arbitrary function F on all of H. No additivity, homogeneity, continuity, linearity, output-anchor orthogonality or input-dependent phase convention is assumed.

For every x in H, require sum_e ||F_e(x)||^2=||x||^2. For each basis index j and k in {0,1,2,3}, require F_e(i^k a_j)=i^k F_e(a_j) in every channel, and sum_e ||F_e(x)-F_e(i^k a_j)||^2 <= ||x-i^k a_j||^2 for every input x. The k=0 calibration is the identity. Thus the calibration is exactly the three nonzero orientations in Definition 3.1, and the comparisons use exactly the four anchors in Definition 3.2 of AURIC v80. Neither condition is extended to arbitrary phase rotations or arbitrary comparison pairs.

The inner product is conjugate linear in its first slot and linear in its second slot. Expanding the two squared distances with equal diagonal norms bounds the real part of <F(x),i^k F(a_j)> from below by that of <x,i^k a_j>. The opposite orientations give both inequalities for the real coordinate, and the two quarter turns give both inequalities for the imaginary coordinate. Consequently <F(x),F(a_j)>=<x,a_j> for every x and j. Conjugation gives the source convention <F(a_j),F(x)>=<a_j,x>. Taking x=a_i proves orthonormality of the output anchors.

Define L by sending a_j to F(a_j), using basis extension. The orthonormality just proved makes L a complex linear isometry V. Basis reconstruction and the anchor-coordinate equalities give <F(x),V(x)>=<x,x>. Together with the two equal norms this gives ||F(x)-V(x)||^2=0. Hence F(x)=V(x) on all inputs, including zero and arbitrary unnormalized vectors. Pointwise agreement makes V unique. The finite Hilbert adjoint satisfies V* V=I.

This is Theorem 5.1 with the complete-record interpretation of Definitions 2.1 through 3.2. The Hilbert-space and shared-reference interface is a premise; the theorem supplies no construction of that interface from physical history. Every outcome, including failure and stopping records, must be included in E. A Hilbert direct sum represents the complete record mathematically and does not grant actual coherent control between different outcome labels. The same F is used throughout, without postselection or separate phase choices for different inputs.

Full pairwise complex inner products and distances, complex linearity and continuity follow from F=V and the standard linear-isometry properties. The conclusion is on all of H, rather than only the unit sphere of Proposition 5.3. The dimension d is a natural number with the literal premise 1<=d; no dimension truncation is used. The norm expansion, basis reconstruction, orthonormal-basis isometry constructor and adjoint identity use Mathlib's existing results. The finite-anchor argument supplies their geometric hypotheses; no separate novelty claim is made for those general results.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteOrientedAnchorRigidity.finite_oriented_anchor_rigidity`
