# Complete Messages on Binary Trees

## Abstract

Complete messages on a labelled binary tree have sharp completion-response capacities.

I is a finite coordinate set. Each X(i) is finite and nonempty; the task F maps the full dependent Cartesian product of these alphabets to an arbitrary output type. T is any finite full binary tree with distinct coordinate-labelled leaves. Every terminal reads only its coordinate. Every fork applies a fixed function to its two complete child messages. A fixed root decoder returns the output. Child order is arbitrary. There are no auxiliary input channels. Message types may differ at every node.

For a subtree S, A(S) is its leaf-label set. Its capacity is the number of distinct functions from all complementary assignments to task outputs obtained by varying the assignment on A(S). Reachable(m,S) counts the actual image of S's evaluated message over all raw global inputs. Peak(m,T) is the maximum of these counts, including the root. Optimum(F,T) is the infimum of peaks of accurate implementations. A one-leaf task tree has height zero, and each actual fork adds one edge to the longest dependency chain.

**Theorem 1.1 (Subtree Coordinate Blocks).**

$$\operatorname{Full}\left(T\right) \implies \forall S \in \operatorname{subtrees}\left(T\right), \operatorname{Full}\left(S\right) \land \operatorname{A}\left(S\right) \subseteq \operatorname{A}\left(T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/TreeMessageRealization.subtree_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every subtree is full and its coordinate block is contained in the ancestor block. At a fork, the two child blocks are disjoint. Induction follows the child containing the subtree and then includes its block in the parent union.

**Theorem 1.2 (Every Accurate Implementation).**

$$\operatorname{Full}\left(T\right) \land \operatorname{Correct}\left(F, T, m, g\right) \implies \forall S \in \operatorname{subtrees}\left(T\right), \operatorname{capacity}\left(F, \operatorname{A}\left(S\right)\right) \le \operatorname{reachable}\left(m, S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/TreeMessageRealization.implementation_lower_bound` (`✓ std3`). ∎

*Citation.* Hemant Kowshik and P. R. Kumar (2011). *Optimal Function Computation in Directed and Undirected Graphs*. DOI: [10.48550/arXiv.1105.0240](https://doi.org/10.48550/arXiv.1105.0240). URL: <https://arxiv.org/abs/1105.0240v2>.

*Commentary.*

A subtree message depends only on that subtree's coordinates. If two such messages agree, substituting them into the same complementary input preserves each ancestor message and hence the root output. Accurate computation therefore requires different messages for different completion responses. Choosing one representative of each response gives an injection into the reachable message image.

**Theorem 1.3 (Simultaneously Sharp Response Messages).**

$$\operatorname{Full}\left(T\right) \land \operatorname{A}\left(T\right) = I \implies \exists m,g, \operatorname{Correct}\left(F, T, m, g\right) \land \forall S \in \operatorname{subtrees}\left(T\right), \operatorname{reachable}\left(m, S\right) = \operatorname{capacity}\left(F, \operatorname{A}\left(S\right)\right) \land \operatorname{Peak}\left(m, T\right) = \operatorname{Optimum}\left(F, T\right) \land \operatorname{Optimum}\left(F, T\right) = \operatorname{maxCapacity}\left(F, T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/TreeMessageRealization.simultaneous_realization` (`✓ std3`). ∎

*Citation.* Hemant Kowshik and P. R. Kumar (2011). *Optimal Function Computation in Directed and Undirected Graphs*. DOI: [10.48550/arXiv.1105.0240](https://doi.org/10.48550/arXiv.1105.0240). URL: <https://arxiv.org/abs/1105.0240v2>.

*Commentary.*

Use each node's actual completion-response range as its message type. Fix a nominal representative for each message. At a fork, merge the two nominal representatives on their disjoint coordinate blocks, then send the parent's completion response. Replacing the two blocks successively preserves every external response. Induction proves that each evaluated message is the actual response of the input. Every response is reachable from its representative. At the root the complement is empty and the response evaluates to F. The lower bound holds for all accurate implementations, while this one attains every capacity simultaneously. Its peak attains the infimum, which equals the maximum of the subtree capacities.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TreeMessageRealization.implementation_lower_bound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TreeMessageRealization.simultaneous_realization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TreeMessageRealization.subtree_structure`
- Dependency: [D5/S3/Observer/Separation/SurjectiveColumnSharpWidth](../../Observer/Separation/SurjectiveColumnSharpWidth.md)
