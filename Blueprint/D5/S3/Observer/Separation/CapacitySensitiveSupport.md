# Capacity-sensitive supports and common extensions

## Abstract

The sensitive illegal cells are the least supports of active capacities, and their natural join characterizes the exact fixed-tree protocol budget.

Let U be a finite coordinate type, O u a value type for each coordinate, and c a function from complete dependent assignments to an arbitrary result type. A coordinate u belongs to sensitive c precisely when two assignments agree at every coordinate other than u and have unequal c values. DependsOn c S means that agreement on S forces equal c values. The coordinate value types and the result type may be empty or infinite.

**Theorem 1.1 (Sensitive coordinates form the least support).**

Lean statement: `D5/S3/Observer/Separation/CapacitySensitiveSupport.dependsOn_iff_sensitive_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/CapacitySensitiveSupport.dependsOn_iff_sensitive_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such c and every set S of coordinates, DependsOn c S holds if and only if sensitive c is contained in S. In particular the sensitive coordinates themselves support c, and every support contains all of them. Finiteness is required only of U.

For necessity, a sensitive pair differing outside S contradicts support on S. For sufficiency, change the finitely many coordinates one at a time. At a sensitive coordinate the two assignments already agree. At any other coordinate the single change preserves c by the definition of sensitivity. Induction over the finite coordinate set gives equality of the endpoints.

For the application, I is a finite coordinate index, X i is finite and nonempty, D is a nonempty set of complete assignments, and f maps D to O. The tree is the original vertex-labelled finite tree: its sibling subtrees have disjoint descendant-leaf sets, and its root contains every coordinate. Every original node, including the root and unary nodes, is counted. A zero-child constant node implements the empty-input case. No finiteness assumption on the output O is needed.

Take U to be the complement of D in the complete input space. An assignment h on U determines complete D f h: it equals f on D and h on U. These are exactly all total extensions of f. At an original node v, activeCapacity counts the image of complete response rows reached by inputs in D. Every response still tests all complementary assignments, including illegal ones. Counting the image over D is the same as counting it over the projection D at that cut, since every projected assignment has a representative in D. The subtype in responseMessage only records membership in the full response image.

Write c v h for sourceCost t D f v h, namely the active capacity of complete D f h at v. Its sensitive scope is Sigma v = sensitive (c v). The joint scope Sigma is the union of all Sigma v. The local relation localFeasible c k v contains a row s on Sigma v exactly when every total illegal-cell assignment extending s has c v at most k. sensitiveJoin c k consists of assignments on Sigma whose restrictions belong to all these local relations. The local quantifier is universal; the least-support theorem makes all extensions of one row have the same capacity.

**Theorem 1.2 (Least capacity supports and the exact tree budget).**

Lean statement: `D5/S3/Observer/Separation/CapacitySensitiveSupport.source_result`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/CapacitySensitiveSupport.source_result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original node v and every set S of illegal cells, DependsOn (c v) S holds exactly when Sigma v is contained in S. For every natural k, a correct original tree protocol with at most k reachable messages at each original node exists exactly when sensitiveJoin c k is nonempty. ProtocolBudget expresses this existence using the original Implementation, evaluate and reachable constructions. minimumPeak is the infimum of all such natural budgets. The nonempty budget set attains this infimum, so this is precisely the assertion that minimumPeak is at most k. The existing common-extension theorem supplies attained minima.

Restricting a jointly feasible extension to Sigma yields a join row: any other extension of its local restriction has the same capacity. Conversely, fill the cells outside Sigma arbitrarily. The nonempty promise supplies an output for this filling. The resulting single extension satisfies every local bound. These arguments also include empty sensitive scopes and k equal to zero.

FixedTreeCommonExtension.result turns every correct protocol into one total extension whose full capacities are bounded by that protocol's reachable counts. Active capacities are no larger than the full capacities. In the reverse direction the existing canonical response protocol has, at each node, exactly the active response image of the chosen extension. Hence the same extension and the same actual protocol meet all node bounds simultaneously; separately optimal extensions are never combined.

For the capacity-sensitive support theorem this identifies U with the illegal full input cells, c v with the active boundary capacity, Sigma v with its sensitivity set, and the local relations and natural join with their universal-extension definitions. This theorem concerns finite input alphabets and deterministic protocols. It gives neither a polynomial construction cost nor the separator-width bound or recursive running-intersection algorithm, which require their own statements.

## References

- Truth anchor: `D5/S3/Observer/Separation/CapacitySensitiveSupport.dependsOn_iff_sensitive_subset`
- Truth anchor: `D5/S3/Observer/Separation/CapacitySensitiveSupport.source_result`
- Dependency: [D5/S3/Observer/Separation/FixedTreeCommonExtension](FixedTreeCommonExtension.md)
