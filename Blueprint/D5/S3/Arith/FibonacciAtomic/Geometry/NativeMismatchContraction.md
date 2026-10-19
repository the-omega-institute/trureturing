# Native First-Disagreement Contraction

## Abstract

Two native substitution steps contract the discounted first-disagreement mass of every finite source pair.

**Definition 1.1 (Discounted Frontier Mass).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction.mass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source is the existing free magma on Bool: true is alpha, false is beta, and multiplication is the ordered binary branch. The substitution rho sends alpha to beta, beta to the branch (beta,alpha), and acts on both children of a branch.

For a rational q and source trees s,t, mass(q,s,t) is the finite sum of q to the length of p over p in frontier(s,t). This is the existing binary first-disagreement frontier, with false denoting the left direction and true the right. Equal subtrees contribute nothing; different root replies contribute the empty address; a common branch prefixes the two child frontiers. Matching terminated leaves are deleted.

Write E(s)=rho squared applied to s. E(alpha)=(beta,alpha), E(beta)=((beta,alpha),beta), and E(s,u)=(E(s),E(u)). Thus every E-image has a branch at its root.

For rational discounts, the canonical ordered-field embedding into the reals preserves this finite sum, its powers, products and inequalities. The rational mass therefore represents the same binary real-valued discounted frontier quantity at rational q. No statement about a tuple of more than two sources is asserted.

**Theorem 1.2 (Complete Root Cases).**

$$\forall q: \mathbb{Q}, ((0 < q) \Rightarrow ((q \leq \frac{1}{2}) \Rightarrow ((\forall s: \operatorname{Source}\left(\right), (\forall t: \operatorname{Source}\left(\right), ((s = t) \Rightarrow (\operatorname{mass}\left(q, \operatorname{E}\left(s\right), \operatorname{E}\left(t\right)\right) = 0)))) \land ((\forall b: \operatorname{Bool}\left(\right), (\forall c: \operatorname{Bool}\left(\right), ((b \neq c) \Rightarrow (\operatorname{mass}\left(q, \operatorname{E}\left(\operatorname{of}\left(b\right)\right), \operatorname{E}\left(\operatorname{of}\left(c\right)\right)\right) = (2) \cdot (q))))) \land ((\forall b: \operatorname{Bool}\left(\right), (\forall u: \operatorname{Source}\left(\right), (\forall v: \operatorname{Source}\left(\right), ((\operatorname{mass}\left(q, \operatorname{E}\left(\operatorname{of}\left(b\right)\right), \operatorname{E}\left(\operatorname{mul}\left(u, v\right)\right)\right) \leq (2) \cdot (q)) \land (\operatorname{mass}\left(q, \operatorname{E}\left(\operatorname{mul}\left(u, v\right)\right), \operatorname{E}\left(\operatorname{of}\left(b\right)\right)\right) \leq (2) \cdot (q)))))) \land (\forall s: \operatorname{Source}\left(\right), (\forall u: \operatorname{Source}\left(\right), (\forall t: \operatorname{Source}\left(\right), (\forall v: \operatorname{Source}\left(\right), (\operatorname{mass}\left(q, \operatorname{E}\left(\operatorname{mul}\left(s, u\right)\right), \operatorname{E}\left(\operatorname{mul}\left(t, v\right)\right)\right) = (q) \cdot ((\operatorname{mass}\left(q, \operatorname{E}\left(s\right), \operatorname{E}\left(t\right)\right)) + (\operatorname{mass}\left(q, \operatorname{E}\left(u\right), \operatorname{E}\left(v\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction.root_cases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four conjuncts include equal sources, both orders of distinct leaves, both orders of a leaf against any branch, and arbitrary pairs of branches. The endpoint q=1/2 is included.

Induction on a source, with the other source arbitrary, bounds every child-pair mass by one: a root disagreement has mass one, equality has mass zero, and a common branch has mass at most q times (1+1). Every transformed root branches, so its two child masses give the mixed-root bound. The distinct-leaf frontier consists precisely of the one-letter left and right addresses.

**Theorem 1.3 (Two-Step Native Contraction).**

$$\forall q: \mathbb{Q}, ((0 < q) \Rightarrow ((q \leq \frac{1}{2}) \Rightarrow (\forall s: \operatorname{Source}\left(\right), (\forall t: \operatorname{Source}\left(\right), (\operatorname{mass}\left(q, \operatorname{E}\left(s\right), \operatorname{E}\left(t\right)\right) \leq ((2) \cdot (q)) \cdot (\operatorname{mass}\left(q, s, t\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction.two_step_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite nonempty native source pair and every rational 0<q<=1/2, applying rho twice reduces the mass by a factor at most 2q. For 0<q<1/2 this factor is strictly below one; at the endpoint the estimate is nonexpansive.

Structural induction handles both trees without a height bound. At distinct leaves or a mixed root, the original mass is one and the complete root cases apply. At common branches, multiply the sum of the two child induction estimates by q and use the original and transformed branch recursions. Equal inputs have mass zero on both sides.

**Theorem 1.4 (All Even Iterates).**

$$\forall q: \mathbb{Q}, ((0 < q) \Rightarrow ((q \leq \frac{1}{2}) \Rightarrow (\forall n: \mathbb{N}, (\forall s: \operatorname{Source}\left(\right), (\forall t: \operatorname{Source}\left(\right), (\operatorname{mass}\left(q, \operatorname{iterate}\left(\operatorname{rho}\left(\right), (2) \cdot (n), s\right), \operatorname{iterate}\left(\operatorname{rho}\left(\right), (2) \cdot (n), t\right)\right) \leq (((2) \cdot (q))^{n}) \cdot (\operatorname{mass}\left(q, s, t\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction.even_iterates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The estimate holds for all natural n, including zero, and for equal as well as unequal inputs. It retains the same original finite sources throughout.

The zero-step estimate is equality. For a successor, apply the two-step estimate to the two actual images at time 2n, then multiply the induction estimate by the nonnegative factor 2q. Iteration addition and the power identity yield the factor (2q) to the power n+1.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction.even_iterates`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction.mass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction.root_cases`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction.two_step_contraction`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation](../ActualImageAlphaSeparation.md)
