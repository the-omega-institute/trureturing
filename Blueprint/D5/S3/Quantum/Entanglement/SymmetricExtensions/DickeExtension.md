# Dicke diagonal extension cones

## Abstract

Star and complete graph Bose symmetric fully PPT extensions of unnormalized Dicke diagonal operators.

The register set I and local alphabet L are finite; r is the cardinality of I. A computational basis index is a function from I to L, so matrices act on the actual tensor product of the local complex spaces. Two selected registers a and b are distinct and ordered. Every partial trace below is unnormalized.

The marginal-to-global support mechanism is prior Hansenne-Xu-Kraft-Guehne mathematics. The application note has byline Haobo Ma then Wenlin Zhang. Li-Huang-Ruan-Zeng, arXiv:1809.05641v1, Theorem 2, prove existence of a leaf-Bose extension for qubit leaves and arbitrary bipartite inputs by changing the witness. Their result does not assert the same individual witness or full Bose support including the root in arbitrary dimension.

**Definition 1.1 (Splitting the actual tensor factors).**

$$\operatorname{edgeSplit}\left(a, b\right) :   ( I \to L )   \equiv   ( L \times L ) \times ( \operatorname{Rest}\left(a, b\right) \to L )$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.edgeSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rest(a,b) is the subtype of registers different from both a and b. The equivalence sends x to ((x(a),x(b)), x restricted to Rest(a,b)). Its inverse fills a and b with the ordered pair and all other sites with the complement function. This is a bijection of the standard tensor basis, with no change of local basis.

**Definition 1.2 (The unnormalized two-register marginal).**

$$\operatorname{M}\left(a, b, E\right)_{u v} = \sum_{c} E_{\operatorname{fill}\left(u, c\right) \operatorname{fill}\left(v, c\right)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.edgeMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M(a,b,E) is partialTraceRight of E reindexed by the inverse factor split. The sum is over every computational basis label of the complement, including its single empty label when there are exactly two registers. There is no dimension factor.

**Definition 1.3 (The two-particle Dicke vectors).**

$$D_{i i} = \operatorname{tensor}\left(e_{i}, e_{i}\right)   ,   D_{i j} = \frac{\operatorname{tensor}\left(e_{i}, e_{j}\right) + \operatorname{tensor}\left(e_{j}, e_{i}\right)}{\sqrt {2}}   ( i \neq j )$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.dickeVector` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

Local labels are Fin(n), corresponding to the usual labels one through n. The diagonal vector has one unit entry. For distinct labels the only two entries are the positive real coefficient one over the square root of two.

**Definition 1.4 (The full unnormalized Dicke cone).**

$$\rho = \sum_{i \leq j} Y_{i j}   D_{i j} \left(D_{i j}\right)^{*}$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.dickeOperator` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

The coefficients are arbitrary real numbers at the definition level. The equivalence theorem restricts every upper-triangular coefficient to be nonnegative. Each summand is its coefficient times the outer product of the actual Dicke vector and its complex conjugate. No coefficient sum or trace is fixed; all coefficients may vanish.

**Definition 1.5 (Every proper nonempty PPT cut).**

$$\operatorname{FullyPPT}\left(E\right) \iff \forall   S \subseteq I ,   \emptyset \neq S \neq I \implies \operatorname{PSD}\left(E^{T_{S}}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.FullyPPT` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

S ranges over all subsets of the register set. The condition applies to each nonempty proper S. At the matrix-entry level partialTransposeOn exchanges the row and column labels exactly at the sites of S, in the standard tensor basis.

**Definition 1.6 (The symmetric leaf projector).**

$$\operatorname{leafProjector}\left(root\right) = P_{L} = \operatorname{tensor}\left(I, \pi_{r - 1}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.leafProjector` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

The distinguished root is fixed. The projector is the uniform permutation average over the setwise stabilizer of its singleton. Such permutations fix the root and permute all remaining registers. This is the identity on the root factor times the orthogonal projector onto the symmetric tensor power of the leaves.

**Definition 1.7 (The star extension predicate).**

$$\operatorname{StarExtension}\left(root, \rho, E\right) \iff \operatorname{PSD}\left(E\right) \land P_{L} E P_{L} = E \land ( \forall   i ,   i \neq root \implies   \operatorname{M}\left(root, i, E\right) = \rho ) \land \operatorname{FullyPPT}\left(E\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.StarExtension` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

E is positive semidefinite on all r registers, is fixed by the genuine leaf-projector sandwich, and has marginal rho on each ordered edge from the root to a distinct leaf. Every proper nonempty partial transpose of this same E is positive semidefinite.

**Definition 1.8 (The complete graph extension predicate).**

$$\operatorname{CompleteExtension}\left(\rho, E\right) \iff \operatorname{PSD}\left(E\right) \land \pi_{r} E \pi_{r} = E \land ( \forall   a , b ,   a \neq b \implies \operatorname{M}\left(a, b, E\right) = \rho ) \land \operatorname{FullyPPT}\left(E\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.CompleteExtension` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

E is positive semidefinite on the same r registers and is fixed by the full Bose-projector sandwich. Its marginal is rho on every ordered pair of distinct registers. All proper nonempty PPT cuts use this same E in the original standard basis.

**Definition 1.9 (The actual symmetric pair projector).**

$$\operatorname{pairSymmetricProjector}\left(\right) = \frac{1 + \operatorname{flip}\left(\right)}{2}$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.pairSymmetricProjector` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

The flip exchanges the two local tensor factors in the ordered product basis. This is the orthogonal projector onto their symmetric subspace. Bose support means the two-sided sandwich by this projector equals rho; mere conjugation invariance is weaker.

**Definition 1.10 (Star extensions without a PPT requirement).**

$$\operatorname{StarExtensionCore}\left(root, \rho, E\right) \iff \operatorname{PSD}\left(E\right) \land P_{L} E P_{L} = E \land ( \forall i \neq root , \operatorname{M}\left(root, i, E\right) = \rho )$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.StarExtensionCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This predicate requires positivity, the actual root-times-symmetric-leaves support sandwich, and rho on every ordered root-to-leaf marginal. It places no condition on partial transposes and fixes no trace. The original StarExtension predicate still includes FullyPPT.

**Definition 1.11 (Complete extensions without a PPT requirement).**

$$\operatorname{CompleteExtensionCore}\left(\rho, E\right) \iff \operatorname{PSD}\left(E\right) \land \pi_{r} E \pi_{r} = E \land ( \forall a \neq b , \operatorname{M}\left(a, b, E\right) = \rho )$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.CompleteExtensionCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This predicate requires positivity, the actual full Bose support sandwich, and rho on every ordered pair of distinct registers. It places no condition on partial transposes and fixes no trace. The original CompleteExtension predicate still includes FullyPPT.

**Theorem 1.12 (Connected graphs of supported marginals).**

$$\operatorname{Connected}\left(G\right) \land \operatorname{PSD}\left(E\right) \land \operatorname{BoseEdges}\left(G, E\right) \implies \operatorname{Bose}\left(E\right) \land \operatorname{AllOrderedMarginalsEqual}\left(E\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.support_of_connected_graph` (`✓ std3`). ∎

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

For every finite register type and finite local alphabet, each edge of a connected simple graph has its actual two-register marginal supported by the symmetric pair projector. Positivity then forces full Bose support. All ordered marginals are equal, including reversed pairs; the marginal values need not be supplied in advance. The proof inducts over actual graph walks to propagate transposition invariance of every column. This is the Hansenne-Xu-Kraft-Guehne support mechanism, with no new priority claim. Disconnected components, higher-body hypotheses and conjugation-only leaves require their separate bridges; this theorem does not assert them.

**Definition 1.13 (Permutations within connected components).**

$$\operatorname{componentGroup}\left(G\right) = \operatorname{ComponentPreservingPermutations}\left(G\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.componentGroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A permutation belongs to this subgroup exactly when every vertex is reachable from its image in G. Vertices cannot move between components; an isolated vertex is fixed. The definition applies also to the empty graph and the empty register type.

**Definition 1.14 (The component permutation projector).**

$$\pi_{G} = \operatorname{Average}\left(\operatorname{componentGroup}\left(G\right), Q\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.componentProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the uniform average of the actual tensor-register permutation matrices over componentGroup G. The tensor factorization into symmetric projectors on every connected component is proved in BoseComponentProjector.factorization. All singleton components remain present.

**Theorem 1.15 (Support on every graph component).**

$$\operatorname{PSD}\left(E\right) \land \operatorname{BoseEdges}\left(G, E\right) \implies \pi_{G} E \pi_{G} = E$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.component_support_of_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite simple graph, positive E with Bose-supported edge marginals is supported by the component permutation projector. The proof propagates column invariance along graph walks, generates all component-preserving permutations by reachable transpositions, and uses the existing finite-group averaging theorem. No factor or correlation between distinct components is discarded. The support propagation mechanism is attributed to Hansenne-Xu-Kraft-Guehne.

**Theorem 1.16 (Exact component support characterization).**

$$\operatorname{PSD}\left(E\right) \implies ( \operatorname{BoseEdges}\left(G, E\right) \iff \pi_{G} E \pi_{G} = E )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.edges_iff_component_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The characterization holds for every finite graph and every positive semidefinite E. The reverse direction uses the fact that each graph-edge transposition fixes the component projector, then computes the actual ordered marginal and its symmetric pair-projector sandwich. Connectedness and normalization are not assumed.

**Theorem 1.17 (Support from arbitrary Bose root marginals).**

$$\operatorname{PSD}\left(E\right) \land \operatorname{BosePair}\left(\rho\right) \land ( \forall i \neq root , \operatorname{M}\left(root, i, E\right) = \rho ) \implies \operatorname{Bose}\left(E\right) \land ( \forall a \neq b , \operatorname{M}\left(a, b, E\right) = \rho )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.support_of_bose_root_marginals` (`✓ std3`). ∎

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

The register type is any finite type with a chosen root and the local alphabet is any finite type. For a positive semidefinite E, Bose-supported root marginals force full Bose support and equality of all ordered marginals. No leaf support, PPT, strict positivity, inverse, or trace normalization is assumed. The proof lifts zero antisymmetric marginal weight through the existing tensor trace duality and zero-weight support-face theorem, then uses star transpositions and the existing ordered-marginal covariance proof. The marginal-to-global support mechanism is prior work of Hansenne-Xu-Kraft-Guehne, main page 4 and Appendix D Lemma 8 of arXiv:2108.02732v1. This formal generalization is not a priority claim.

**Theorem 1.18 (Conjugation invariance of leaves suffices).**

$$\operatorname{PSD}\left(E\right) \land \operatorname{LeafConjugationInvariant}\left(E\right) \land \operatorname{BosePair}\left(\operatorname{M}\left(root, leaf, E\right)\right) \implies \operatorname{Bose}\left(E\right) \land \operatorname{AllOrderedMarginalsEqual}\left(E\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.support_of_leaf_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose distinct root and leaf registers. Assume only that conjugating E by every register permutation fixing the root leaves E invariant, together with positivity and Bose support of that one root-leaf marginal. Relabeling the complement trace gives the same supported marginal at every root edge. The root support theorem then gives full Bose support and every ordered marginal equal to the original one. Leaf-subspace support is not a premise.

**Theorem 1.19 (The identical matrices without PPT).**

$$\operatorname{BosePair}\left(\rho\right) \implies ( \operatorname{StarExtensionCore}\left(root, \rho, E\right) \iff \operatorname{CompleteExtensionCore}\left(\rho, E\right) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.same_matrix_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every individual E, on any finite register set with a chosen root and finite local alphabet, the two no-PPT predicates are equivalent whenever rho is supported by the actual pair symmetric projector. The forward direction obtains full support and all ordered marginals from the root marginals; the reverse uses inclusion of the full symmetric subspace in the root-times-symmetric-leaves subspace. The theorem does not assert existence of an extension for every rho. It includes zero and singular rho, local dimension one, exactly two registers and arbitrary unnormalized traces.

**Theorem 1.20 (The identical matrices with fully PPT cuts).**

$$\operatorname{BosePair}\left(\rho\right) \implies ( \operatorname{StarExtension}\left(root, \rho, E\right) \iff \operatorname{CompleteExtension}\left(\rho, E\right) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.same_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same finite-type and actual Bose support hypotheses as same_matrix_core, the original fully PPT predicates select the same individual E. Every nonempty proper cut is retained on that E. This is a pointwise equality, so it preserves the witness, its trace and all singular boundary cases. It does not assert universal extendibility.

**Theorem 1.21 (Equality of the extension cones).**

$$\forall   n \geq 1 ,   \forall   r \geq 2 ,   \forall   Y ,   ( \forall   i , j ,   i \leq j \implies Y_{i j} \geq 0 ) \implies   ( ( \exists   E ,   \operatorname{StarExtension}\left(0, \rho, E\right) ) \iff ( \exists   E ,   \operatorname{CompleteExtension}\left(\rho, E\right) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.result` (`✓ std3`). ∎

*Resolves.* `Problems/gnp-2025-v4-question-8-20-dicke-extensions` (proved) by `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gnp-2025-v4-question-8-20-dicke-extensions","declaration_gid":"D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Here n and r are natural numbers, Y is an arbitrary real n by n array, and i and j range over Fin(n). The operator rho is the Dicke sum above. This is an equivalence of existence predicates for every register count at least two and every local dimension at least one. In the forward direction the complete graph witness is literally the star witness. The antisymmetric two-particle projector annihilates each Dicke vector. Trace duality lifts its zero marginal weight to zero weight of the actual tensor-placed projector on E. The zero_weight_support_face theorem gives both one-sided annihilations without requiring an inverse or trace normalization. Thus every root transposition fixes every column of E. Star transpositions generate all permutations, so the columns lie in the full symmetric subspace. The orthogonal projector and Hermiticity give the full sandwich, and relabeling actual complement indices makes all ordered edge marginals equal. Every PPT inequality is retained verbatim. Conversely the full symmetric subspace is contained in the root-times-symmetric-leaves subspace, and complete edges include all star edges. The argument includes zero coefficients, singular witnesses, n=1 and r=2. The resolution target is exactly Gulati-Nechita-Park, arXiv:2509.15201v4, Question 8.20; current journal question wording and worldwide absence of a prior solution are unverified.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.CompleteExtension`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.CompleteExtensionCore`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.FullyPPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.StarExtension`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.StarExtensionCore`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.componentGroup`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.componentProjector`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.component_support_of_edges`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.dickeOperator`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.dickeVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.edgeMarginal`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.edgeSplit`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.edges_iff_component_support`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.leafProjector`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.pairSymmetricProjector`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.same_matrix`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.same_matrix_core`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.support_of_bose_root_marginals`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.support_of_connected_graph`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.support_of_leaf_invariance`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor](../AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/QuantumStates/ZeroWeightSupportFace](../../../QuantumStates/ZeroWeightSupportFace.md)
