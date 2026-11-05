# Three-way balance on the original group

## Abstract

Nonnegative three-way balance on an arbitrary abelian group forces an integer quadratic map and makes every orbit sum invisible in every background.

**Theorem 1.1 (Visible quadratic structure without scalar assumptions).**

$$\forall (A : \operatorname{Type}\left(\right)), [\operatorname{AddCommGroup}\left(A\right)], \forall (U : \operatorname{AddMonoidHom}\left(A, A\right)), \forall (q : (A \to \mathbb{R})), (\forall (x : A), 0 \le \operatorname{q}\left(x\right)) \Rightarrow (\forall (x : A), \forall (y : A), \operatorname{q}\left(x + y\right) + \operatorname{q}\left(x + \operatorname{U}\left(y\right)\right) + \operatorname{q}\left(x + \operatorname{U}\left(\operatorname{U}\left(y\right)\right)\right) = 3 \cdot \operatorname{q}\left(x\right) + 3 \cdot \operatorname{q}\left(y\right)) \Rightarrow (\forall (x : A), \operatorname{q}\left(\operatorname{U}\left(x\right)\right) = \operatorname{q}\left(x\right)) \land (\forall (z : A), \forall (y : A), \operatorname{q}\left(z + y + \operatorname{U}\left(y\right) + \operatorname{U}\left(\operatorname{U}\left(y\right)\right)\right) = \operatorname{q}\left(z\right)) \land (\forall (x : A), \operatorname{q}\left(-x\right) = \operatorname{q}\left(x\right)) \land (\forall (x : A), \forall (y : A), \operatorname{q}\left(x + y\right) + \operatorname{q}\left(x - y\right) = 2 \cdot \operatorname{q}\left(x\right) + 2 \cdot \operatorname{q}\left(y\right)) \land (\exists (Q : \operatorname{QuadraticMap}\left(\mathbb{Z}, A, \mathbb{R}\right)), \forall (x : A), \operatorname{Q}\left(x\right) = \operatorname{q}\left(x\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/ThreeWayBalance.three_way_quadratic_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be any additive commutative group, U any additive endomorphism and q any finite real-valued function. Assume pointwise nonnegativity and the displayed balance equation for every pair x,y. No topology, continuity, divisibility, faithfulness, evenness, quadratic law or invertibility of U is assumed. Integer scalar multiplication is the canonical action on the additive group.

For a fixed y, the forward sequence a(n)=q(U iterated n times at y) obeys a(n+2)+a(n+1)=2a(n). The quantity a(n+1)+2a(n) is constant, so nonnegativity bounds all differences. Their absolute values double at each step. An Archimedean growth argument forces the first difference to vanish, giving q(Uy)=q(y). This uses every finite forward iterate and imposes no depth cap.

Comparing balance at y and Uy makes U cubed minus the identity invisible in every background. For d=y+Uy+U squared y, both Ud-d and U squared d-d are invisible. Balance at d consequently gives q(z+d)=q(z)+q(d). The negative recipe -d and nonnegativity force q(d)=0. These are identities of readouts on the original group; no identity U squared plus U plus the identity is imposed on the original labels.

Balance at y,y now gives q(y+y)+2q(-y)=6q(y). Apply this relation to both signs and repeatedly double the group argument. The normalized sum stays bounded while the normalized difference doubles. Nonnegativity forces q(-y)=q(y), hence q(y+y)=4q(y). All division occurs in the real codomain.

Put L=U-U squared and let delta(x,y)=q(x+y)+q(x-y)-2q(x)-2q(y). Applying balance to x+y,x-y and using invisible orbit sums gives 4q(x)+q(x+Ly)+q(x-Ly)=3q(x+y)+3q(x-y). Therefore q(Ly)=3q(y) and delta(x,Ly)=3delta(x,y). Evenness makes delta symmetric, giving delta(Lx,Ly)=9delta(x,y). Additivity of L and q composed with L equal to 3q also give delta(Lx,Ly)=3delta(x,y). Thus the parallelogram defect vanishes.

The resulting parallelogram law is passed directly to TauCeti.QuadraticMap.ofParallelogram with the actual A, real codomain and integer scalar ring. Injective doubling is needed only in the real codomain. The returned quadratic map has underlying function q, so existing polarization and integer quadratic scaling apply without adding real operations to A.

This is the structural part of the original integer-interface representation problem. Positive Gram extension, identification of the null group with the radical, rational localization, real completion, the complex phase, minimality and label-preserving unitary uniqueness require further constructions. No completed Hilbert representation, physical realization, process supply or composite compatibility is asserted here.

## References

- Truth anchor: `D5/S3/QuadraticForms/ThreeWayBalance.three_way_quadratic_structure`
- Dependency: [D5/S3/QuadraticForms/ParallelogramConstruction](ParallelogramConstruction.md)
