# Null frontier from contracting open covers

## Abstract

A whole interior cylinder can be removed from a finite contracting open cover of the frontier.

**Definition 1.1 (Varying branch words).**

Lean statement: `D5/S3/Topology/ContractingCoverNullBoundary.cylinderMap`

*Formalization.* `D5/S3/Topology/ContractingCoverNullBoundary.cylinderMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary types X and I and maps f from I to functions X to X, a word w of length N is a function Fin N to I. Its cylinder map F_w is the composition f(w(0)) after f(w(1)) after all remaining letters. The length-zero map is the identity. Equivalently, the successor recursion composes the head branch with the cylinder map of the tail. The first letter is outermost.

**Theorem 1.2 (An interior cylinder and an omitted frontier cover).**

Lean statement: `D5/S3/Topology/ContractingCoverNullBoundary.exists_interior_cylinder_frontier_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/ContractingCoverNullBoundary.exists_interior_cylinder_frontier_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be any metric space, I any type, and K a compact subset of X with nonempty interior. Let q be a nonnegative real number strictly less than one, and let every branch f_i be q-Lipschitz and open. Assume the union over all i of f_i(K) equals K. There exist N > 0 and a word w0 of length N such that F_w0(K) is contained in interior K and frontier K is contained in the union of F_w(frontier K) over all length-N words w distinct from w0. Finiteness of I is unnecessary here. Choose an interior ball about x. Since q^N times the diameter of K tends to zero, a sufficiently deep cylinder containing x lies wholly in that ball. Exact coverage provides such a cylinder and a preimage in K. For any frontier point, exact coverage also provides a depth-N preimage. An interior preimage would map to the interior because the cylinder is open and maps K into K. Thus its preimage is on the frontier, and its word cannot be w0. Images of the frontier need not themselves lie on the frontier.

**Theorem 1.3 (Strict loss of finite boundary mass).**

Lean statement: `D5/S3/Topology/ContractingCoverNullBoundary.measure_frontier_eq_zero_of_contracting_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/ContractingCoverNullBoundary.measure_frontier_eq_zero_of_contracting_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In addition to the preceding metric, compactness, interior, contraction, openness and exact-cover hypotheses, assume I is finite and X has a measurable-space structure. Let mu be a measure finite on compact sets. Suppose each branch has a strictly positive nonnegative-real weight a_i, their sum is one, and for every compact set S the equality mu(f_i(S)) = a_i mu(S) holds. Then mu(frontier K) = 0. A cylinder has weight A_w equal to the product of its letter weights. Summing over all words of length N gives total weight one. Deleting the interior cylinder leaves coefficient c < 1 because its weight is positive. The frontier is compact; the finite union bound on its omitted-cylinder cover gives mu(frontier K) at most c times itself. A positive finite mass would make that inequality impossible. No disjointness, separation, ambient completeness or measurable-set hypothesis on the compact images is required beyond the stated scaling law.

## References

- Truth anchor: `D5/S3/Topology/ContractingCoverNullBoundary.cylinderMap`
- Truth anchor: `D5/S3/Topology/ContractingCoverNullBoundary.exists_interior_cylinder_frontier_cover`
- Truth anchor: `D5/S3/Topology/ContractingCoverNullBoundary.measure_frontier_eq_zero_of_contracting_cover`
