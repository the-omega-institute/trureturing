# Tree Peak and Height Frontier

## Abstract

The first-rejection task has an exact binary-tree peak and height frontier.

Let n=k+1 be positive. The input is the full product of the five-window alphabet at coordinates zero through k. The first-rejection task returns the first failed seam, the terminal failure, or acceptance, with the same fixed order on every input. T ranges over all full binary trees whose leaves are labelled bijectively by these coordinates. Leaf order is unrestricted.

An implementation sends complete discrete messages, uses one coordinate at each terminal, and applies a fixed binary function at every fork. A fixed root decoder must return the task on every input. There are no other input channels. P(T) is the minimum peak number of reachable messages over accurate implementations, including the root. Capacity(A) counts the distinct completion responses of a coordinate subset A. Height counts task edges. Write H=clog(2,n), and let E be one when n is at least four and n=2^H, and zero otherwise.

**Theorem 1.1 (Exact Attainable Frontier).**

$$\operatorname{P}\left(T\right) = \operatorname{maxNodeCapacity}\left(T\right) \land \operatorname{minPeak}\left(n\right) = n + 1 \land \operatorname{minHeight}\left(n\right) = H \land \operatorname{minHeightAtMinPeak}\left(n\right) = H + E \land \operatorname{minPeakAtMinHeight}\left(n\right) = n + 1 + E \land {\operatorname{excludesZero}\left(A\right) \land \operatorname{card}\left(A\right) \ge 2 \implies \operatorname{capacity}\left(A\right) \ge 2\cdot\operatorname{card}\left(A\right) + 2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/TreePeakHeightFrontier.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality for P holds for every full all-coordinate tree. Each minimum consists of an attaining tree and a lower bound for every tree in its stated class. Thus all trees have peak at least n+1 and height at least H. Among trees with peak n+1, the least height is H+E. Among trees of height H, the least peak is n+1+E. The subset inequality holds for every subset excluding zero and containing at least two coordinates, with no interval assumption.

For n at least three, split the root into a leading interval of length ceil((n+1)/2) and its trailing complement. Recursively bisect both intervals with the larger half first. Every nonprefix node has length at most floor((n-1)/2), so the interval capacity formulas bound every node by n+1. The resulting height is clog(2,n+1). Ordinary balanced bisection attains height H with peak at most n+2.

Any full binary tree of edge height h has at most 2^h labelled leaves. At n=2^H and height H, both root children must have n/2 leaves. Disjointness forces one child block to exclude zero; the arbitrary-subset bound then forces peak at least n+2. This also excludes height H among peak-minimal trees. Outside the exceptional case, the biased construction attains both minima. A single terminal and a two-terminal fork handle the two smallest sizes.

Peak is a single node's message alphabet size, not simultaneous storage. Height counts dependencies, not an unconditional running time. Input access, control, precision, storage, total work and available parallel resources are separate quantities.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TreePeakHeightFrontier.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/BalancedIntervalTree](BalancedIntervalTree.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity](FirstRejectionCutCapacity.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/FourMessageTreeRigidity](FourMessageTreeRigidity.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TreeMessageRealization](TreeMessageRealization.md)
