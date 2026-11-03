# RootComparability

## Abstract

Rooted comparability of pairs stranded by a small actual configuration cut.

**Theorem 1.1 (A stranded component contains no singleton).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.stranded_singletons`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.stranded_singletons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

If a component cannot reach a clean root and the cut is smaller than the host order, it cannot reach any singleton.

**Theorem 1.2 (Stranded pair labels have deleted singletons).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.stranded_pair_labels`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.stranded_pair_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

When no singleton is reachable, both labels of every reachable distinct pair have their singleton configurations in the cut.

**Theorem 1.3 (Actual mixed neighbors have one of two forms).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.outside_move_shape`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.outside_move_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

For a mixed neighbor containing a label outside the original set and otherwise contained in its one-label extension, the neighbor is either the extension itself or the result of deleting one original label adjacent to the new label.

**Theorem 1.4 (Root comparability under one small cut).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.stranded_pair_comparable`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.stranded_pair_comparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Let the host be any finite connected simple undirected graph. Fix one cut of its full mixed mutual-visibility reconfiguration graph whose size is smaller than minimum degree, a clean root, and a surviving pair that cannot reach the root singleton after that cut. Then one endpoint belongs to every shortest path from the other endpoint to the root. The direction can depend on the pair. No assumption on host order, girth, dominating sets, or ranks of other configurations is imposed.

Every surviving singleton belongs to the same component because the cut is smaller than the host order. A component stranded from the root therefore contains no singleton, and every label of each pair in that component has its singleton in the cut. Cleanliness rules out a visible triple consisting of such a pair and the root, and also rules out host edges from either endpoint to the root. Three-label nonvisibility leaves rooted comparability or mandatory passage through the root.

Suppose instead that a stranded pair has all its geodesics pass through the root. Among visible configurations containing that pair and having every pair face in the stranded component, choose one of maximum cardinality. If it has at least three labels, the root-hub lemma makes all its pairs pass through the root; at rank two this is the initial pair. All pair distances are at least four. Consequently an outside label is adjacent to at most one selected label, so at most one actual slide can use it.

Partition the selected configuration's neighbors by their unique outside label, together with internal deletions. Its cut singleton faces pay the internal deletions. For an outside label whose singleton is cut, that singleton pays the possible slide. A visible extension is either cut or fails pair completeness by maximality; deleting towards an outside pair then supplies a distinct nonsingleton cut for the addition. For a surviving outside singleton, a proper deletion chain pays a slide; if the extension is itself cut that payment is separate. If the extension survives, the distinct proper cyclic deletion chains give at least two cuts containing the outside label. These suffice for the one possible slide and one addition. The classes are disjoint for different outside labels and from internal cuts. The resulting degree is at most the same cut size, contradicting its size below minimum degree.

The model retains existential shortest paths in the original host, every feasible rank including zero, token addition and removal, and slides along actual host edges to unoccupied labels. This rooted restriction does not establish the full equality between vertex connectivity and minimum degree. The minimum-pair degree count and separator composition combine this restriction with the other cut bounds to prove the full equality.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.outside_move_shape`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.stranded_pair_comparable`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.stranded_pair_labels`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability.stranded_singletons`
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots](CleanRoots.md)
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/CyclicIntervals](CyclicIntervals.md)
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/SingletonCore](SingletonCore.md)
