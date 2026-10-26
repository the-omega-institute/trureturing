# PairPayments

## Abstract

Auxiliary finite cut-counting structure for mutual-visibility reconfiguration.

**Theorem 1.1 (A minimum rooted pair exists).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.minimal_pair_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.minimal_pair_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

For a nonempty family of distinct pairs reachable from one configuration after one cut, there is a pair minimizing the sum of endpoint distances to a fixed root.

**Theorem 1.2 (Exceptional triples have simultaneous disjoint payments).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.simultaneous_inward_payments`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.simultaneous_inward_payments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Fix a minimum rooted pair, its dominating orientation, and one inward predecessor. Every selected label adjacent to both endpoints with a visible triple in the same surviving component supplies one distinct member of the actual cut. These payments avoid the internal class and every class with a single outside label.

**Definition 1.3 (Cut classes for one outside label).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.localCutClass`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.localCutClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Take members of one cut which contain the designated label and have no other label outside the fixed base. Classes for distinct labels outside the base are disjoint.

**Theorem 1.4 (One simultaneous cut budget).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.joint_cut_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.joint_cut_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Fix one cut, one base, a finite family of labels outside the base, and a further family F of cut members. Assume F is disjoint from the internal cut class and from every selected local class. The cardinality of the internal class, the sum of the local cardinalities, and the cardinality of F together are at most the cardinality of that same cut. The proof takes their disjoint union and includes it into the actual cut.

Choose a pair of minimum root-distance sum in one actual surviving component. Every exceptional visible common-neighbor triple has an inward slide followed by a deletion to a pair of smaller sum, so one intermediate configuration is in the same cut. With one common predecessor p, its labels outside the original pair are exactly p and the exceptional label y. This distinguishes payments for different labels and separates them from every local cut class with just one outside label. A disjoint-union cardinality bound combines these payments with the internal and local classes. The cyclic high-rank cut bound, singleton-core connection, clean-root existence and clean-root pair exclusions are auxiliary results. The maximal sparse-slide argument establishes rooted comparability. The minimum-pair local count combines these payments with the singleton core and high-rank component bound to obtain the full separator equality.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.joint_cut_budget`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.localCutClass`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.minimal_pair_exists`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/PairPayments.simultaneous_inward_payments`
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity](Connectivity.md)
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics](Geodesics.md)
