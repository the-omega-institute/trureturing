# Actual Capped Exploration

## Abstract

Deterministic capped exploration gives an exact disjoint actual cylinder decomposition.

U(n) is the actual subtype of permutations of Fin(n) avoiding literal 2413 and 3142. J(t,n) forbids a proper cut of sign t. False denotes direct sum and true skew sum. The empty permutation remains in each small source under the no-proper-cut convention.

**Theorem 1.1 (Deterministic actual restricted-history fibers).**

$$\forall t,n,m,B,H,K, \operatorname{mass}\left(\operatorname{Allowed}\left(t\right) \land \operatorname{test}\left(\operatorname{literal}\left(B, m\right)\right)\right)=\operatorname{sum}\left(\operatorname{catalog}\left(t, n, m, B, H, K\right), \operatorname{CylinderMass}\left(test\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/CappedExploration.actual_capped_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source state t in Option(Bool), every natural source length n, target m, alphabet B, horizon H and endpoint cap K, including zero values, explore acts on each actual source member. It first stops when the target has been emitted, calling the stop good when the remaining length exceeds B and short otherwise. Before reaching the target it stops small below length two, or exhausted when the transition budget is zero. At every continued step recover determines the unique actual proper-cut sign and its minimum positive cut. The minimum-cut Cartesian equivalence recovers the actual unique two factors. The parent is U or J(not sign), never J(sign).

When the actual left length is at most K it emits that indecomposable left shape and recurses on the actual right U member, reducing the unmet target by the emitted length. Otherwise, when the right length is at most K, it records the actual right U shape as a pending suffix and recurses on the actual left J(sign) member with unchanged target. If both endpoint lengths exceed K it stops with cap failure, retaining the actual terminal minimum-cut certificate. Recursion constructs a typed history, terminal sample, exact reconstruction equation, endpoint-cap certificate, horizon bound and the indicated stopping law. The theorem proves its actual minimum-cut trace and removed <= H*K with removed+remaining = n.

The catalog is the finite image of this deterministic classifier on the actual source, not a catalog of arbitrary supplied histories. Every allowed actual permutation lies in exactly one catalog fiber; a nonmember lies in none. Thus all good, stopped and failure outcomes are exhaustive and pairwise disjoint. For every outcome (h,q), SelectedLeaf consists of precisely those terminal actual samples of h whose reconstruction is classified as (h,q). The restricted reconstruction is bijective onto the classifier fiber. Its exact cardinality is card(SelectedLeaf), and its actual full-class uniform mass is card(SelectedLeaf)/card(U(n)). Its cardinality is at most card(Leaf). Its actual probability conditional on the source is weight(h)*card(SelectedLeaf)/card(Leaf), where weight(h) is the supplied exact telescoping product. No unrestricted terminal count is substituted for this restricted count.

For every predicate on actual permutations, its intersection with the source has cardinality and actual mass equal to the finite sums of its intersections with these classifier fibers. For every predicate on List(Option(Fin B)), CylinderMass on a good outcome is its fiber mass when the test accepts the first m entries of h.word(B,0), and zero otherwise. On a non-good outcome it is the actual tested restricted fiber mass. Their finite sum equals the actual m-coordinate cylinder mass. The inherited word transport preserves both signs, literal low offsets and pending suffixes. When B=m, NoFixedMass gives the same exact sum for pi(i) != i at every zero-based actual position i<m, using NoFixedWord on good outcomes, not standardized equality.

For every actual input, if n > H*K+max(2*K,max(m,B)), its terminal length exceeds max(2*K,max(m,B)); small and short stops are impossible. Every continued parent has length greater than 2*K, so the two permitted endpoint choices cannot overlap. These are unbounded symbolic statements.

The catalog still depends on n. A fixed bounded code-to-history interface and equality with unrestricted supplied-history events are not conclusions. Actual count-ratio limits, sign-half and indecomposable cardinal interfaces, the infinite coupled law, horizon and cap tails, occupation, filtration, hitting and the full all-positive-length derangement-ratio limit remain separate obligations.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/CappedExploration.actual_capped_partition`
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointHistoryKernel](EndpointHistoryKernel.md)
