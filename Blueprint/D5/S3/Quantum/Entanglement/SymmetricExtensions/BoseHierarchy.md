# The full Parrilo hierarchy and actual Bose extensions

## Abstract

The full Parrilo hierarchy and actual Bose extensions

The complete-graph characterization is prior Gulati-Nechita-Park Theorem 8.16. The star, companion and unnormalized optimization applications are from the note by Haobo Ma then Wenlin Zhang. No priority certification is asserted. The proofs use the full native sum-of-squares hierarchy at every level, including zero and singular matrices.

**Definition 1.1 (The positive polar of the actual all-level SOS cone).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.parriloPolar`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.parriloPolar` (`✓ std3`).

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

The positive polar consists of P whose ordinary real matrix pairing with every M in ParriloHierarchy.K at level k is nonnegative. That canonical K uses the unrestricted native sum-of-squares predicate for (sum of x_i squared)^k times sum M_ij x_i squared x_j squared.

**Theorem 1.2 (The complete-graph characterization).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.gnp_characterization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.gnp_characterization` (`✓ std3`). ∎

*Citation.* Aabhas Gulati, Ion Nechita and Sang-Jun Park (2025). *Positive maps and extendibility hierarchies from copositive matrices*. DOI: [10.48550/arXiv.2509.15201](https://doi.org/10.48550/arXiv.2509.15201).

*Commentary.*

For every register count r with two distinct selected sites and every real symmetric P, the actual LDUI(P,P) operator has a fully PPT full-Bose extension exactly when P belongs to the positive polar of K_n^(r-2). The proof uses actual tensor trace duality, diagonal twirling of dual witnesses, native homogeneous SOS cut certificates, DPS closedness and finite-dimensional bipolarity. It assumes no GNP theorem or additional axiom.

Normalized two-particle Dicke weights satisfy P_ii=Y_ii and P_ij=Y_ij/2. The same-individual-matrix theorem identifies these complete witnesses with star witnesses. Root partial transposition bijects fully PPT star witnesses for LDUI and its CLDUI companion, permuting all cuts by symmetric difference with the root. Full Bose support is asserted for the inverse-transposed companion witness.

Ordinary and adapted DPS use one root and t Bose-supported leaves, with r=t+1. Leaf permutations reduce their cuts to the paper's prefix conventions; full transposition supplies complementary cuts. The resulting comparison is adapted DPS = ordinary DPS intersect PSD of the two-particle symmetric subspace. The separate closed dual-sum theorem retains its closure. GNP Questions 8.7 and 8.21, general non-Bose graph extendibility, non-Bose CLDUI complete-graph comparisons, and unrestricted exact witness lifting remain outside these statements.

**Definition 1.3 (The actual unnormalized feasible objective set).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.objectiveValues`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.objectiveValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Attainable values are the real matrix pairings with symmetric P for which the actual LDUI operator has an ordinary DPS witness. No trace constraint is added.

**Theorem 1.4 (Attained unnormalized optimum zero).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.objective_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.objective_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every dimension n, every r with two distinct sites and every objective C in K_n^(r-2), the actual unnormalized ordinary DPS program on LDUI(P,P) has least objective value zero. Feasibility and the complete hierarchy characterization force every pairing to be nonnegative, and P=0 is feasible. In particular n=5,r=3 gives precisely the t=2 Britz-Laurent program. A trace-one or otherwise normalized program is not covered.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.gnp_characterization`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.objectiveValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.objective_minimum`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHierarchy.parriloPolar`
- Dependency: [D5/S3/QuadraticForms/ParriloHierarchy](../../../QuadraticForms/ParriloHierarchy.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseLDUI](BoseLDUI.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSDuality](BoseSOSDuality.md)
