# Actual Finite-Tree Markov Stability

## Abstract

Normalized Markov laws on arbitrary finite trees satisfy degree-weighted total-variation bounds with sharp edge coefficient one.

**Theorem 1.1 (Normalization, marginals, stability and conditional-row independence).**

$$\forall V:FiniteType,G:\operatorname{SimpleGraph}\left(V\right),X:V \to FiniteType,F,H:\operatorname{Family}\left(G, X\right),P,Q:\operatorname{Mass}\left(\operatorname{Configurations}\left(X\right)\right), ((\operatorname{IsTree}\left(G\right)) \land ((2 \le \operatorname{card}\left(V\right)) \land ((P = \operatorname{markovLaw}\left(G, F\right)) \land (Q = \operatorname{markovLaw}\left(G, H\right))))) \Rightarrow (((\forall x, 0 \le \operatorname{eval}\left(P, x\right)) \land (\sum_{x} \operatorname{eval}\left(P, x\right) = 1)) \land (((\forall x, 0 \le \operatorname{eval}\left(Q, x\right)) \land (\sum_{x} \operatorname{eval}\left(Q, x\right) = 1)) \land ((\forall i, \operatorname{pushforward}\left(\operatorname{coordinate}\left(i\right), P\right) = \operatorname{node}\left(F, i\right)) \land ((\forall i, \operatorname{pushforward}\left(\operatorname{coordinate}\left(i\right), Q\right) = \operatorname{node}\left(H, i\right)) \land ((\forall i,j, (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{pushforward}\left(\operatorname{coordinates}\left(i, j\right), P\right) = \operatorname{edge}\left(F, i, j\right))) \land ((\forall i,j, (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\operatorname{pushforward}\left(\operatorname{coordinates}\left(i, j\right), Q\right) = \operatorname{edge}\left(H, i, j\right))) \land (((\operatorname{TV}\left(P, Q\right) \le \operatorname{min}\left(1, \operatorname{edgeBudget}\left(F, H\right) + \operatorname{nodeBudget}\left(G, i\mapsto\operatorname{TV}\left(\operatorname{node}\left(F, i\right), \operatorname{node}\left(H, i\right)\right)\right)\right)) \land ((\forall i, \operatorname{node}\left(F, i\right) = \operatorname{node}\left(H, i\right)) \Rightarrow (\operatorname{TV}\left(P, Q\right) \le \operatorname{min}\left(1, \operatorname{edgeBudget}\left(F, H\right)\right)))) \land ((\forall root:V, \exists t:\operatorname{TreeOrder}\left(G\right), \operatorname{root}\left(t\right) = root) \land (\forall t:\operatorname{TreeOrder}\left(G\right),K:\operatorname{KernelFamily}\left(X\right), (\forall i,j, (\operatorname{Adj}\left(G, i, j\right)) \Rightarrow (\forall a,b, (\operatorname{eval}\left(\operatorname{node}\left(F, i\right), a\right) \neq 0) \Rightarrow (\operatorname{K}\left(i, j, a, b\right) = \operatorname{quotient}\left(\operatorname{eval}\left(\operatorname{edge}\left(F, i, j\right), a, b\right), \operatorname{eval}\left(\operatorname{node}\left(F, i\right), a\right)\right)))) \Rightarrow (\operatorname{factorMass}\left(t, F, K\right) = P))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/TreeMarkovStability.actual_tree_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Family on G and X assigns to each vertex i a nonnegative normalized real mass on the finite state space X(i), and to each actual edge ij a nonnegative coupling with exactly those two marginals. Reversing an edge transposes its coupling. The coordinate at a shared vertex is the same variable in every incident edge; equality of unrelated marginal values is not an identification of their sources. Nonedge coupling entries are unused.

A TreeOrder removes leaves until one actual edge remains. Every finite graph tree with at least two vertices has such an order at every prescribed root. Its joint mass starts with that edge coupling and adds each removed leaf through the quotient of its coupling by the parent marginal. A zero-mass parent row is completed with the child's normalized node law. The displayed P and Q are the resulting markovLaw masses; finite types may differ from vertex to vertex.

Both masses are nonnegative, have total one, and push forward to every prescribed node and oriented edge law. Here TV is half the sum of absolute mass differences. edgeBudget is half the sum of oriented-edge TVs, hence counts every undirected edge once. nodeBudget(G,d) is the sum over vertices i of (degree(i)-1)d(i), with real subtraction. The two displayed minima include the probability bound one.

The leaf extension inequality adds the edge TV and the parent-node TV. Deleting a leaf reduces precisely the corresponding degree charge, so induction gives the full bound. Equal node laws remove all node charges. No positive lower bound on node masses is needed.

KernelFamily(X) consists of real functions K(i,j,a,b). The quotient condition in the last conjunct fixes K only at nonzero parent masses; the values at zero mass may be arbitrary, so in particular every normalized probability completion is allowed. factorMass starts with a root node and its first conditional factor, followed by the leaf factors. The equality holds for every TreeOrder, including both orientations of its root edge. A zero node marginal forces the entire configuration fiber to have zero mass. On the remaining configurations, the square of the density is the product of squared node masses times the orientation-independent product of edge-to-node ratios. Nonnegativity then gives equality across all orders. Thus the Markov factorization class has a unique law; arbitrary joint laws with the same low-order marginals are not asserted to be unique.

**Theorem 1.2 (Universal sharpness).**

$$\neg(\exists c:\mathbb{R},(c < 1) \land (\forall V:FiniteType,G:\operatorname{SimpleGraph}\left(V\right),X:V \to FiniteType,F,H:\operatorname{Family}\left(G, X\right), ((\operatorname{IsTree}\left(G\right)) \land ((2 \le \operatorname{card}\left(V\right)) \land (\forall i, \operatorname{node}\left(F, i\right) = \operatorname{node}\left(H, i\right)))) \Rightarrow (\operatorname{TV}\left(\operatorname{markovLaw}\left(G, F\right), \operatorname{markovLaw}\left(G, H\right)\right) \le \operatorname{min}\left(1, c \cdot \operatorname{edgeBudget}\left(F, H\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/TreeMarkovStability.edge_coefficient_one_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SmallerEdgeCoefficient is the closed claim that there exists a real c<1 such that, for every finite tree with at least two vertices, every family of finite node spaces and every two consistent normalized families F,H with equal node laws, their actual markovLaw TV is at most min(1,c*edgeBudget(F,H)). Its negation excludes every smaller universal coefficient. On the two-vertex Bool tree, the diagonal and antidiagonal couplings have the same uniform node laws. Their actual constructed joint laws have TV one and edgeBudget one. Applying the proposed universal inequality to this member forces 1<=c, contradicting c<1.

## References

- Truth anchor: `D5/S3/TotalVariation/TreeMarkovStability.actual_tree_stability`
- Truth anchor: `D5/S3/TotalVariation/TreeMarkovStability.edge_coefficient_one_sharp`
- Dependency: [D5/S3/Divergence/ChainRule](../Divergence/ChainRule.md)
- Dependency: [D5/S3/Entropy/Forgetting/CompletionEntropyMinimality](../Entropy/Forgetting/CompletionEntropyMinimality.md)
- Dependency: [D5/S3/Entropy/Forgetting/PushforwardComposition](../Entropy/Forgetting/PushforwardComposition.md)
- Dependency: [D5/S3/TotalVariation/Metric](Metric.md)
