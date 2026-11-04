# The length cost of a complete binary dependency tree

## Abstract

Complete binary dependency expansions have an exact additive and strict depth cost.

A DependencyTree Q has a labelled root at every leaf or branch, and a branch has two ordered child trees. Complete means that the two children of every branch have the same height. Admissible candidate relations record the positive flat-candidate inequality at every branch; repeated leaves remain repeated occurrences in the leaf sum.

Assume 1 < z(q) for every label and z(q) >= 1 + z(a) + z(b) whenever candidate(q,a,b). Expanding a complete tree gives one unit for every branch and retains every leaf occurrence. A complete tree of height h has 2^h leaves and 2^h-1 branches, so the root is at least (2^h-1) plus the repeated leaf total, and therefore strictly exceeds 2^(h+1)-1.

This formalization is the exact reusable content of CFMP_GEOMETRIC_REALIZATION, Section 46.2. It treats the full-tree hypothesis explicitly and makes no claim that an arbitrary acyclic candidate family admits such a complete expansion.

**Theorem 1.1 (Exact additive cost for a complete expansion).**

$$\forall Q \in Type,\; \forall z \in Function\left(Q, Real\right),\; \forall candidate \in Function\left(Q, Function\left(Q, Function\left(Q, Prop\right)\right)\right),\; \forall tree \in DependencyTree\left(Q\right),\; \left(\left(\forall q \in Q,\; 1 < z\left(q\right)\right) \land \left(\left(\forall q \in Q, a \in Q, b \in Q,\; candidate\left(q, a, b\right) \Rightarrow z\left(q\right) \ge 1 + z\left(a\right) + z\left(b\right)\right) \land \left(Complete\left(tree\right) \land Admissible\left(candidate, tree\right)\right)\right)\right) \Rightarrow z\left(root\left(tree\right)\right) \ge 2^{height\left(tree\right)} - 1 + leafTotal\left(z, tree\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FlatBranchDepthCost.full_binary_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the tree combines the two child bounds. Equal child heights rewrite the parent height as child height plus one, and the two powers combine with pow_succ. The branch inequality then yields the exact additive lower bound.

**Theorem 1.2 (Strict exponential depth cost).**

$$\forall Q \in Type,\; \forall z \in Function\left(Q, Real\right),\; \forall candidate \in Function\left(Q, Function\left(Q, Function\left(Q, Prop\right)\right)\right),\; \forall tree \in DependencyTree\left(Q\right),\; \left(\left(\forall q \in Q,\; 1 < z\left(q\right)\right) \land \left(\left(\forall q \in Q, a \in Q, b \in Q,\; candidate\left(q, a, b\right) \Rightarrow z\left(q\right) \ge 1 + z\left(a\right) + z\left(b\right)\right) \land \left(Complete\left(tree\right) \land Admissible\left(candidate, tree\right)\right)\right)\right) \Rightarrow 2^{height\left(tree\right) + 1} - 1 < z\left(root\left(tree\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FlatBranchDepthCost.full_binary_strict_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact bound is combined with the strict leaf estimate: every one of the 2^h leaf occurrences is greater than one. This gives z(root) > 2^(h+1)-1, with no distinctness requirement on the leaf labels.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FlatBranchDepthCost.full_binary_lower_bound`
- Truth anchor: `D5/S3/Geometry/Hyperideal/FlatBranchDepthCost.full_binary_strict_bound`
