# Multipliers of Matrix Fields Vanishing at Infinity

## Abstract

Double centralizers of the full algebra of matrix fields vanishing at infinity are precisely bounded continuous matrix fields, with both pointwise actions and equal norms.

**Theorem 1.1 (The full matrix multiplier equivalence).**

$$\exists (e: \operatorname{StarAlgEquiv}(C, \operatorname{Cb}(U, M), \operatorname{DC}(C, A))), \operatorname{Isometry}(e) \land (\forall (h: \operatorname{Cb}(U, M)), \forall (f: A), \forall (x: U), \operatorname{L}(\operatorname{e}(h), f, x) = \operatorname{h}(x)\operatorname{f}(x) \land \operatorname{R}(\operatorname{e}(h), f, x) = \operatorname{f}(x)\operatorname{h}(x)) \land (\forall (m: \operatorname{DC}(C, A)), \exists! (h: \operatorname{Cb}(U, M)), (\operatorname{Actions}(m, h) \land \Vert h \Vert  = \Vert m \Vert ))$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/C0Multipliers.source_multiplier_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U be the open real interval (0,1/4) with every point 1/n removed for natural n at least 5. The natural numbers are unbounded: all such reciprocals are removed. Let M be CStarMatrix (Fin 2) (Fin 2) C, the full two by two complex matrix algebra with its C-star operator norm, and let A be the entire complex algebra C0(U,M) of continuous fields vanishing at infinity. Cb(U,M) is the algebra of all bounded norm-continuous fields, with its uniform norm. DC(C,A) denotes the actual Mathlib DoubleCentralizer C A, consisting of bounded complex-linear left and right operators satisfying the centralizer identity.

There exists a complex star-algebra equivalence e from Cb(U,M) onto DC(C,A), and e is an isometry. Thus it preserves addition, multiplication, complex scalars, the unit and star. For every bounded continuous field h, every f in the whole algebra A and every x in U, the left operator of e(h) sends f at x to h(x)f(x), and the right operator sends f at x to f(x)h(x). No compact-support restriction is placed on f.

Conversely, for every double centralizer m there exists exactly one bounded continuous matrix field h having both these actions on every f in A and every x in U. The same field satisfies norm(h)=norm(m), where the first norm is the uniform field norm and the second is the multiplier operator norm. In the displayed formula Actions(m,h) abbreviates these two universally quantified identities. Uniqueness includes the same actions and norm equality.

A compactly supported scalar cutoff, equal to one on a compact neighborhood, gives a matrix section equal to the matrix unit there and of norm at most one. Evaluating a double centralizer on such sections recovers a field pointwise. The centralizer identity forces both actions, independence of the section and uniqueness. On each compact neighborhood the recovered field agrees with the image of one fixed continuous section, proving continuity. The operator estimate gives its uniform bound; the action on arbitrary vanishing fields gives the reverse norm inequality.

Multiplying any field vanishing at infinity by a bounded continuous field on either side again gives a field vanishing at infinity. These products define the bounded linear operators in the reverse construction. Associativity gives the centralizer identity. Pointwise calculations establish multiplication, scalar and star preservation. The reciprocals have zero as their only added accumulation point; adjoining zero makes them compact, which proves that U is open and locally compact.

This statement identifies the multiplier algebra of A. It asserts no zero-extension isomorphism onto an ideal of continuous fields on [0,1], no polynomial-plus-ideal model, no nonunitality theorem, no Gram or mass certificate, and no annihilator, norm-ratio or cone counterexample. Those require additional mathematical statements.

## References

- Truth anchor: `D5/S3/ContinuousObservables/C0Multipliers.source_multiplier_certificate`
