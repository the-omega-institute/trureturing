# Unsigned Star Lattices and Sparse Integral Recovery

## Abstract

Exact unsigned integer star lattices: common remainders, order-two localization, and original-source coefficient-one recovery.

The vertex type V indexes rows and X indexes individually identified original edges. An Edges value gives distinct endpoints left(i), right(i). Parallel original coordinates remain distinct. The exact integer linear map is f(a)(i)=a(left(i))+a(right(i)). Its image is not replaced by its saturation. graphAfterDeleting D first removes exactly the original indices in D, then uses existence of a remaining edge as the underlying simple adjacency. Thus deletion and support cardinalities never conflate parallel indices.

**Theorem 1.1 (Consumed Integer Injectivity).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.starMap_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.starMap_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a connected nonbipartite original graph, the exact integer star map is injective. Apply the existing private nonbipartite_potential proof to the difference of two potentials with equal images. Its constant has twice its value equal to zero, so it vanishes over the integers. This consumed corollary supplies injectivity to UnsignedStarFixedCokernel; it is a consumed helper, not a new generality claim or a new proof of the private potential theorem.

**Theorem 1.2 (Signed Root Normalization in a Bipartite Graph).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.integral_of_bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.integral_of_bipartite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a connected bipartite original graph, k>0 and actual integer k*z=f(a), there exists actual integer b with f(b)=z. Choose the two colors from bipartiteness and write e(v)=1 or -1 accordingly. For a root r, subtract e(v)*e(r)*a(r) from each a(v). This is a genuine integer kernel of the star map and makes the root zero. Walk propagation then makes every normalized coefficient zero modulo k. Only after proving divisibility do we divide and cancel k in the ambient integer coordinates.

**Theorem 1.3 (Integer Potential Remainders).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.potential_remainders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.potential_remainders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any connected nonbipartite original graph, positive natural k, integer vectors z on X and a on V satisfying k*z(i)=f(a)(i) for every original i, there exists an integer r with 0<=r<k, either r=0 or 2*r=k, and a(v) modulo k equals r for every vertex. Walk induction propagates residues as c or -c in ZMod k. If these differ they define a bipartition, contradicting nonbipartiteness. Integer remainder bounds then prove the two cases.

**Theorem 1.4 (The Exact Integral or Component-Total Alternative).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.integer_potential_alternative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.integer_potential_alternative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, either z=f(b) for actual integer b, or k is even, every actual a(v) is nonzero, and actual integer b satisfies z(i)=f(b)(i)+1 and f(2*b+1)(i)=2*z(i). In the second case z is not in the image and the graph after deleting support(z) is bipartite. The full component total is not an integer star combination: such a combination would give a potential 2*b-1 with opposite adjacent values, forcing an integer half. Thus the second case is an actual nonzero order-two class of the exact quotient. No quotient cancellation is used.

**Theorem 1.5 (Coefficient One from Nonbipartiteness after Support Deletion).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.integral_of_support_nonbipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.integral_of_support_nonbipartite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a connected original graph and actual k*z=f(a), k>0, if deletion of the original support of z leaves a nonbipartite graph, there exists integer b with f(b)=z. In the half case, all a(v) are nonzero and each undeleted edge has the exact equation a(u)+a(v)=0. Positive and negative potentials therefore color the entire deleted graph, including all pieces created by deletion. Connectedness after deletion is not a premise. In the zero case divisibility is proved before division, and k is cancelled only in the ambient integer coordinate group.

**Theorem 1.6 (Actual Original-Source Integer Coefficients).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.source_coefficients_of_sparse_multiple`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.source_coefficients_of_sparse_multiple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V,X,H be finite, and fix q. Assume the original graph is connected and every deletion of at most q original indexed edges leaves a nonbipartite graph. Source rows rows(T) are integer vectors on X. Explicit integer d(T,v) give f(d(T))=rows(T), and explicit c(v,T) give starRow(v)(i)=sum_T c(v,T)*rows(T)(i). For any original z with support size at most q, positive k, and actual h(T) with k*z(i)=sum_T h(T)*rows(T)(i), the theorem returns integer b with f(b)=z and z(i)=sum_T (sum_v b(v)*c(v,T))*rows(T)(i). It first constructs a(v)=sum_T h(T)*d(T,v) and applies the new integral recovery. Both directions of the source lattice identification are explicit, and all original source rows participate; larger Boolean rows are not omitted. The left-hand coefficient is exactly one.

For the original unit e_i or original difference e_i-e_j, the transient exact application uses q=2 on the literal X coordinates and the displayed original-H coefficient formula. No support-two bound is asserted after partial pivot maps. The connected original model is the retained scope; componentwise classification, unrestricted exact integral full-blocker, unrestricted Good and AM remain open. The supplied finite-free/PID and IntegerStrongOrdering chain is not reproved or retained as a wrapper.

Attribution: formalization of the caller-supplied completed argument, Exact Private Pivots, Original Primitive Torsion, and a Mixed Cyclic Core, Sections 6-7, SHA256 f776b4a6cba72126daf67658b7c846279a39d61cbdd41f6e2cfdd400f8e487f8. Its independent native review is mathematical guidance, not kernel evidence or official acceptance. Existing signed-incidence total unimodularity concerns endpoint differences and does not supply this unsigned nonbipartite inference. No literature-priority or unrestricted Good claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.integer_potential_alternative`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.integral_of_bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.integral_of_support_nonbipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.potential_remainders`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.source_coefficients_of_sparse_multiple`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion.starMap_injective`
