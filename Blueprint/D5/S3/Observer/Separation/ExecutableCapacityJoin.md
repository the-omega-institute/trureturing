# Executable capacity-sensitive tree gluing

## Abstract

Finite separator computation decides every original fixed-tree active peak budget.

I is finite, each coordinate alphabet X i is finite and nonempty, D is a nonempty promise subset of the full coordinate product and f maps D into the finite output alphabet O. The original implementation tree t is Full and its root contains every coordinate. Its constructor allows arbitrary finite branching, unary vertices and zero-child constant vertices. Nodes t is the entire original node carrier, including the root. A separate decidable SimpleGraph G on this carrier is a tree whose actual capacity-sensitive supports satisfy running intersection. G is not identified with t.

**Theorem 1.1 (Exact original-task solver with a finite global witness).**

$$(\forall d: SourceData, \operatorname{costTable}\left(d\right) = \operatorname{sourceCost}\left(d\right) \land (\forall k: Nat, \operatorname{isSome}\left(\operatorname{sourceSolve}\left(d, k\right)\right) = \operatorname{true}\left(\right) \iff \operatorname{minimumPeak}\left(d\right) \le k) \land (\forall k: Nat, (\forall j: \operatorname{UnionAssignment}\left(d\right), \operatorname{sourceSolve}\left(d, k\right) = \operatorname{some}\left(j\right) \to j \in \operatorname{rawJoin}\left(d, k\right))) \land (\forall k: Nat, (\forall e: \operatorname{Dart}\left(\operatorname{supportGraph}\left(d\right)\right), (\forall a: \operatorname{SeparatorAssignment}\left(d, e\right), a \in \operatorname{messageTable}\left(d, k, e\right) \iff a \in \operatorname{separatorMessages}\left(d, k, e\right)) \land \operatorname{card}\left(\operatorname{messageTable}\left(d, k, e\right)\right) \le \operatorname{power}\left(\operatorname{card}\left(\operatorname{output}\left(d\right)\right), \operatorname{card}\left(\operatorname{separator}\left(d, e\right)\right)\right) \land \operatorname{card}\left(\operatorname{separator}\left(d, e\right)\right) \le \operatorname{separatorWidth}\left(d\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/ExecutableCapacityJoin.source_solver_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SourceData abbreviates the full telescope of source_solver_spec: I, V, O, X, finite enumerations and equality decisions for the input and output alphabets, nonempty coordinate alphabets, t, Full t, full root support, D with decidable membership, its nonemptiness proof, f, a finite enumeration and equality on the actual Nodes t, G with decidable adjacency, its tree and original-sensitive-support running intersection proofs, a root of G, complete finite node and illegal-cell lists, and a complete finite output list. These are finite presentations of the original inputs; no extension or feasibility oracle is supplied.

costTable computes leaf coordinates structurally, fills legal cells using f and illegal cells using the supplied assignment h, enumerates all promised inputs, and counts distinct full complementary response functions. Complementary inputs range over their entire original product. Thus it counts precisely active capacity, rather than the capacity of all possible prefixes. The first equality identifies this finite table with CapacitySensitiveSupport.sourceCost on every original node and every illegal-cell assignment.

Finite pairs of assignments decide sensitive coordinates. localTable then enumerates local rows and checks the original universal-extension condition against all finite illegal-cell assignments. Its underlying set is exactly localFeasible for the computed cost. sourceSolve feeds these input-derived tables into the terminating general separator recurrence. A base value is read from the finite output list, whose nonemptiness follows from D and f. It does not select a desired extension.

For every natural budget k, sourceSolve returns Some exactly when the minimum actually reachable original-node peak is at most k. This uses CapacitySensitiveSupport.source_result for the same t, D and f. Every returned assignment belongs to the natural join on the exact union of sensitive supports. Each inward finite message equals the existing semantic separatorMessages relation and has at most card O raised to the separator cardinality entries. The last inequality places that cardinality below the actual support-separator width.

Empty coordinate products, zero-child constant roots, singleton alphabets, empty sensitive unions, empty separators and singleton support trees are included. The original nonempty promise and f already force a nonempty output alphabet. Separator width counts illegal-cell assignments for gluing constraints; response-state boundary width counts states in one observation process. No bound on total runtime, the sum of table sizes, total storage or certificate storage follows from a single separator-table bound.

**Theorem 1.2 (The empty-coordinate constant root has peak one).**

$$\operatorname{answer}\left(0\right) = \operatorname{false}\left(\right) \land \operatorname{answer}\left(1\right) = \operatorname{true}\left(\right) \land \operatorname{minimumPeak}\left(\operatorname{emptyTree}\left(\right), \operatorname{emptyPromise}\left(\right), \operatorname{constantTask}\left(\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/ExecutableCapacityJoin.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here emptyTree is the actual zero-child implementation root on Empty coordinates, emptyPromise is the nonempty singleton empty product, and constantTask has output Unit. The separate support graph is the singleton tree. answer is the executable sourceSolve success flag for these exact inputs. Kernel evaluation gives false at zero and true at one; the general source_solver_spec then identifies the original counted-root minimum peak as one. The computation includes no illegal cells or separators.

## References

- Truth anchor: `D5/S3/Observer/Separation/ExecutableCapacityJoin.result`
- Truth anchor: `D5/S3/Observer/Separation/ExecutableCapacityJoin.source_solver_spec`
- Dependency: [D5/S3/ConceptDynamics/Gluing/FiniteRunningIntersection](../../ConceptDynamics/Gluing/FiniteRunningIntersection.md)
- Dependency: [D5/S3/Observer/Separation/CapacitySensitiveSupport](CapacitySensitiveSupport.md)
