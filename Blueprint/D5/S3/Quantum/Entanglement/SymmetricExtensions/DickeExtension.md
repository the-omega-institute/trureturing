# Dicke diagonal extension cones

## Abstract

Star and complete graph Bose symmetric fully PPT extensions of unnormalized Dicke diagonal operators.

The register set I and local alphabet L are finite; r is the cardinality of I. A computational basis index is a function from I to L, so matrices act on the actual tensor product of the local complex spaces. Two selected registers a and b are distinct and ordered. Every partial trace below is unnormalized.

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

**Theorem 1.9 (Equality of the extension cones).**

$$\forall   n \geq 1 ,   \forall   r \geq 2 ,   \forall   Y ,   ( \forall   i , j ,   i \leq j \implies Y_{i j} \geq 0 ) \implies   ( ( \exists   E ,   \operatorname{StarExtension}\left(0, \rho, E\right) ) \iff ( \exists   E ,   \operatorname{CompleteExtension}\left(\rho, E\right) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.result` (`✓ std3`). ∎

*Resolves.* `Problems/gnp-2025-v4-question-8-20-dicke-extensions` (proved) by `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gnp-2025-v4-question-8-20-dicke-extensions","declaration_gid":"D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Here n and r are natural numbers, Y is an arbitrary real n by n array, and i and j range over Fin(n). The operator rho is the Dicke sum above. This is an equivalence of existence predicates for every register count at least two and every local dimension at least one. In the forward direction the complete graph witness is literally the star witness. The antisymmetric two-particle projector annihilates each Dicke vector. Trace duality lifts its zero marginal weight to zero weight of the actual tensor-placed projector on E. The zero_weight_support_face theorem gives both one-sided annihilations without requiring an inverse or trace normalization. Thus every root transposition fixes every column of E. Star transpositions generate all permutations, so the columns lie in the full symmetric subspace. The orthogonal projector and Hermiticity give the full sandwich, and relabeling actual complement indices makes all ordered edge marginals equal. Every PPT inequality is retained verbatim. Conversely the full symmetric subspace is contained in the root-times-symmetric-leaves subspace, and complete edges include all star edges. The argument includes zero coefficients, singular witnesses, n=1 and r=2. The resolution target is exactly Gulati-Nechita-Park, arXiv:2509.15201v4, Question 8.20; current journal question wording and worldwide absence of a prior solution are unverified.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.CompleteExtension`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.FullyPPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.StarExtension`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.dickeOperator`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.dickeVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.edgeMarginal`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.edgeSplit`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.leafProjector`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor](../AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/QuantumStates/ZeroWeightSupportFace](../../../QuantumStates/ZeroWeightSupportFace.md)
