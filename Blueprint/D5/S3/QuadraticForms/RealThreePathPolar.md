# Original finite readout and real polarization

## Abstract

The original real-scalar three-path law derives a positive real bilinear polar without assuming additivity of the marker or regularity of the readout.

**Definition 1.1 (The unchanged original relation).**

$$\forall (V : \operatorname{Type}\left(\right)), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)], \forall (U : (V \to V)), \forall (q : (V \to \mathbb{R})), \operatorname{Balance}\left(U, q\right) \iff (\forall (x : V), \forall (y : V), \forall (t : \mathbb{R}), (\operatorname{q}\left(x + t \cdot y\right) - \operatorname{q}\left(0\right)) + (\operatorname{q}\left(x + t \cdot \operatorname{U}\left(y\right)\right) - \operatorname{q}\left(0\right)) + (\operatorname{q}\left(t \cdot \operatorname{U}\left(x\right) + y\right) - \operatorname{q}\left(0\right)) = 2 \cdot (\operatorname{q}\left(x\right) - \operatorname{q}\left(0\right)) + (\operatorname{q}\left(y\right) - \operatorname{q}\left(0\right)) + (\operatorname{q}\left(t \cdot x\right) - \operatorname{q}\left(0\right)) + 2 \cdot (\operatorname{q}\left(t \cdot y\right) - \operatorname{q}\left(0\right)))$$

*Formalization.* `D5/S3/QuadraticForms/RealThreePathPolar.Balance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V is an arbitrary real vector space. U is an arbitrary function, and q is finite real-valued. Q(x) abbreviates q(x)-q(0), using the same original baseline in every occurrence. In particular Q(tx) and Q(ty) remain original readouts, with no homogeneity assumption. No topology, U(0)=0, additivity, linearity, periodicity or norm is supplied.

**Theorem 1.2 (A derived positive real bilinear polar and actual radical).**

$$\forall (V : \operatorname{Type}\left(\right)), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)], \forall (U : (V \to V)), \forall (q : (V \to \mathbb{R})), ((\forall (x : V), 0 \le \operatorname{q}\left(x\right)) \land (\operatorname{Balance}\left(U, q\right))) \Rightarrow \exists (B : \operatorname{LinearMap}\left(\mathbb{R}, V, \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right)), (\forall (x : V), \forall (y : V), \operatorname{B}\left(x, y\right) = \frac{\operatorname{q}\left(x + y\right) - \operatorname{q}\left(x - y\right)}{4}) \land (\forall (x : V), \forall (y : V), \operatorname{B}\left(x, y\right) = \operatorname{B}\left(y, x\right)) \land (\forall (x : V), \operatorname{q}\left(x\right) = \operatorname{q}\left(0\right) + \operatorname{B}\left(x, x\right)) \land (\forall (x : V), 0 \le \operatorname{B}\left(x, x\right)) \land (\forall (x : V), \operatorname{B}\left(\operatorname{U}\left(x\right), \operatorname{U}\left(x\right)\right) = \operatorname{B}\left(x, x\right)) \land (\forall (x : V), \forall (y : V), \operatorname{B}\left(x, y\right) + \operatorname{B}\left(x, \operatorname{U}\left(y\right)\right) + \operatorname{B}\left(\operatorname{U}\left(x\right), y\right) = 0) \land (\forall (x : V), \forall (y : V), \operatorname{B}\left(\operatorname{U}\left(x\right), \operatorname{U}\left(y\right)\right) = \operatorname{B}\left(x, y\right)) \land (\forall (x : V), (\operatorname{B}\left(x, x\right) = 0) \iff x \in \operatorname{ker}\left(B\right)) \land (\forall (x : V), x + \operatorname{U}\left(x\right) + \operatorname{U}\left(\operatorname{U}\left(x\right)\right) \in \operatorname{ker}\left(B\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/RealThreePathPolar.raw_real_polar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

B ranges over real bilinear maps V by V to the real numbers, and ker(B) is the kernel of the real-linear map x mapped to B(x,-). All displayed properties hold for one and the same derived B. Thus its diagonal zero set is an actual real subspace, rather than an assumed quotient certificate.

Exchanging the original inputs cancels the two marker terms. The resulting scalar exchange relation separates an additive odd part A from an even part E. A finite sqrt(2) substitution gives E(2x)=4E(x); a finite translate recurrence gives the parallelogram identity. TauCeti.QuadraticMap.ofParallelogram is then applied directly, supplying the integer quadratic map and its existing bilinear polar companion.

The nonnegative original q bounds E below. Integer scaling and the Archimedean order force E to be nonnegative; on its zero set the same argument forces A to vanish. The scalar exchange relation gives b(x,ty)=b(tx,y). For each fixed x, the additive scalar function t mapped to b(tx,x) is nonnegative on nonnegative t by the square-root substitution. Monotonicity and rational sandwiches identify it with t b(x,x). Polarizing this identity proves actual real bilinearity on the original real vector space.

The original relation at x=y=0 makes U(0) invisible. It then gives Q(tU(x))=Q(tx), both even and odd invariance, and the three-direction bilinear relation. That relation forces additivity of U modulo the radical; diagonal invariance then yields full bilinear isometry. The orbit sum x+U(x)+U(U(x)) is radical. Since A vanishes there and is marker-invariant, 3A(x)=0. This proves the complete odd drift vanishes, not merely that it is additive.

The live non-finite step is the lower-bound and Archimedean scalar estimate used in raw_even_data and real_polar. Finite polynomial and phase identities are consumed proof helpers and carry no separate escape credit. This result supplies the original_visible_quotient theorem and the original real-linear Hilbert characterization. It asserts a mathematical representation of the original readouts, not that completion creates physical preparations.

## References

- Truth anchor: `D5/S3/QuadraticForms/RealThreePathPolar.Balance`
- Truth anchor: `D5/S3/QuadraticForms/RealThreePathPolar.raw_real_polar`
- Dependency: [D5/S3/QuadraticForms/ParallelogramConstruction](ParallelogramConstruction.md)
- Dependency: [D5/S3/QuadraticForms/ThreeWayPositiveKernel](ThreeWayPositiveKernel.md)
