# Four-Message Tree Rigidity

## Abstract

Four-message cut capacities force an arbitrary labelled binary tree to have two peeling spines.

Let n=k+1 with k>=2. Coordinates are numbered from zero through k. Every coordinate alphabet is the complete five-window alphabet, including the zero window. F is the Boolean End output after running all n windows from the state with both flags false. All words and all complementary assignments are included; no seam or terminal validity promise is imposed.

T is a finite full binary tree with leaves bijectively labelled by all coordinates. A(S) is the coordinate block of a subtree S and may be any subset. A small proper block is a nonempty global prefix, a nonempty global suffix, or an interior singleton. A prefix spine successively peels the largest remaining coordinate; a suffix spine successively peels the smallest. Both predicates allow an independent exchange of the two children at each fork. DoubleComb means that the root joins complementary prefix and suffix spines, in either child order. DoubleCombAt(j,T) fixes the split after coordinate j-1. An implementation m has arbitrary complete messages, leaf encoders and atomic child mergers; g reads the root message. Correct means g returns F on every input, and Peak includes every node including the root. Height counts parent-child edges, with leaf height zero.

**Theorem 1.1 (Arbitrary Leaf Labels).**

$$k \ge 2 \land \operatorname{Full}\left(T\right) \land \operatorname{A}\left(T\right) = \operatorname{coordinates}\left(k\right) \land \operatorname{Correct}\left(F, T, m, g\right) \land \operatorname{Peak}\left(m, T\right) \le 4 \implies \exists j, 0 < j < \operatorname{n}\left(k\right) \land \operatorname{DoubleCombAt}\left(j, T\right) \land \operatorname{height}\left(T\right) = \operatorname{max}\left(j, \operatorname{n}\left(k\right)-j\right) \land \operatorname{ceilHalf}\left(\operatorname{n}\left(k\right)\right) \le \operatorname{height}\left(T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FourMessageTreeRigidity.rigidity_from_implementation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every accurate implementation has at least the cut capacity many reachable messages at each subtree. Peak at most four therefore bounds all these capacities. The exact Boolean capacity is 2^d+epsilon. If epsilon is one, capacity at most four allows at most one crossing seam. Nonempty proper blocks with one crossing are prefixes or suffixes. If epsilon is zero, the block owns neither a terminal coordinate nor an internal seam. Two distinct owned coordinates would then produce three distinct crossing seams, exceeding the capacity bound. The remaining blocks are singletons.

No small proper block contains both endpoint coordinates. The root therefore separates the two endpoints, and the two root blocks are complementary prefix and suffix intervals. Within a proper prefix, one child contains zero and is again a prefix. The other child contains neither endpoint, hence is a singleton. Disjointness and union force this singleton to be the rightmost remaining coordinate. The suffix argument reverses the endpoint roles. Structural induction determines both spines. A j-coordinate prefix spine has height j-1, and its complementary suffix spine has height n-j-1. Their root merge has height max(j,n-j), which is at least the ceiling of n/2.

**Theorem 1.2 (Sharp Peak and Minimum Height).**

$$k \ge 2 \implies {{\forall A, \operatorname{nonemptyProper}\left(A\right) \implies {\operatorname{capacityF}\left(A\right) \le 4 \iff \operatorname{SmallBlock}\left(A\right)}} \land {\forall i, 0 < i < k \implies \operatorname{capacityF}\left(\operatorname{singleton}\left(i\right)\right) = 4} \land {\forall T, \operatorname{Full}\left(T\right) \land \operatorname{A}\left(T\right) = \operatorname{coordinates}\left(k\right) \implies \forall m, \forall g, \operatorname{Correct}\left(F, T, m, g\right) \implies {4 \le \operatorname{Peak}\left(m, T\right) \land {\operatorname{Peak}\left(m, T\right) \le 4 \implies \exists j, 0 < j < n \land \operatorname{DoubleCombAt}\left(j, T\right) \land \operatorname{height}\left(T\right) = \operatorname{max}\left(j, n-j\right) \land \operatorname{ceilHalf}\left(n\right) \le \operatorname{height}\left(T\right)}}} \land {\forall T, \operatorname{DoubleComb}\left(T\right) \implies \exists m, \exists g, \operatorname{Correct}\left(F, T, m, g\right) \land \operatorname{Peak}\left(m, T\right) = 4 \land \operatorname{Optimum}\left(F, T\right) = 4} \land {\forall T, \operatorname{Full}\left(T\right) \land \operatorname{A}\left(T\right) = \operatorname{coordinates}\left(k\right) \land \operatorname{Optimum}\left(F, T\right) \le 4 \implies \operatorname{ceilHalf}\left(n\right) \le \operatorname{height}\left(T\right)} \land {\exists T, \operatorname{Full}\left(T\right) \land \operatorname{A}\left(T\right) = \operatorname{coordinates}\left(k\right) \land \operatorname{Optimum}\left(F, T\right) = 4 \land \operatorname{height}\left(T\right) = \operatorname{ceilHalf}\left(n\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FourMessageTreeRigidity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty proper coordinate block, capacity is at most four exactly when the block is a global prefix, a global suffix, or an interior singleton. Each interior singleton has capacity exactly four. Endpoint intervals have one crossing seam; an interior singleton has two crossing seams and has neither an internal seam nor the terminal coordinate.

Every fully labelled tree contains an interior coordinate as a leaf, so every accurate implementation has peak at least four. Conversely each double comb is full, uses every coordinate once, and has capacity at most four at every subtree. Its proper subtree blocks are endpoint intervals or singletons; its root capacity is two. Simultaneous response-class realization therefore gives an accurate implementation with peak exactly four and Optimum(F,T)=4.

Every tree with Optimum(F,T)<=4 has height at least ceil(n/2). Choose the root split j=floor(n/2), build a prefix spine on the first j coordinates and a suffix spine on the remaining n-j coordinates, and join them at the root. The resulting full tree has optimum four and height max(j,n-j)=ceil(n/2). Thus the minimum peak over all accurate tree implementations is four, and the minimum height among trees with optimum at most four is the ceiling of n/2.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FourMessageTreeRigidity.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FourMessageTreeRigidity.rigidity_from_implementation`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity](FirstRejectionCutCapacity.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TreeMessageRealization](TreeMessageRealization.md)
