# Tensor rules for the qubit Wigner distance

## Abstract

Using the compact minimum bridge in WignerDistanceMinimum, equatorial qubit states obey exact multiplicativity of one plus the Wigner distance. Nonpositive Bloch-product states obey self-tensor superadditivity.

**Definition 1.1 (Pauli expectation coordinates).**

$$\forall rho \in QubitMatrix,\; \forall p \in Pauli,\; \operatorname{bloch}\left(rho, p\right) = \operatorname{re}\left(\operatorname{trace}\left(rho \cdot \operatorname{pauliMatrix}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.bloch` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

bloch(rho,p) is the real part of tr(rho pauliMatrix(p)). For p = X,Y,Z these are the Bloch coordinates r_x,r_y,r_z. Page 7: "For a single-qubit state ρ with Bloch vector r⃗, write s(ρ) := sgn(r_x r_y r_z)." The nonpositive sign condition is exactly r_x r_y r_z ≤ 0.

**Definition 1.2 (Conjecture 5.6).**

$$(claimEquatorial) \Leftrightarrow (\forall rho \in QubitMatrix,\; \forall sigma \in QubitMatrix,\; (\operatorname{IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{IsDensity}\left(sigma\right)) \Rightarrow ((\operatorname{bloch}\left(rho, Z\right) = 0) \Rightarrow ((\operatorname{bloch}\left(sigma, Z\right) = 0) \Rightarrow (\operatorname{CTwo}\left(\operatorname{kronecker}\left(rho, sigma\right)\right) = \operatorname{COne}\left(rho\right) + \operatorname{COne}\left(sigma\right) + \operatorname{COne}\left(rho\right) \cdot \operatorname{COne}\left(sigma\right))))))$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.claimEquatorial` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 8, Conjecture 5.6 (Equatorial multiplicativity): "For ⟨Z⟩_ρ = ⟨Z⟩_σ = 0: C(ρ ⊗ σ) = C(ρ) + C(σ) + C(ρ)C(σ)." The quantifiers range over every complex two-by-two density matrix rho and sigma. IsDensity means positive semidefinite with trace one; the two Z expectations vanish separately. COne and CTwo denote WignerDistanceMinimum.COne and WignerDistanceMinimum.CTwo; COne_min and CTwo_min identify them with the source minimum on the corresponding Hilbert spaces.

**Definition 1.3 (Conjecture 5.7).**

$$(claimSelfTensor) \Leftrightarrow (\forall rho \in QubitMatrix,\; (\operatorname{IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{bloch}\left(rho, X\right) \cdot \operatorname{bloch}\left(rho, Y\right) \cdot \operatorname{bloch}\left(rho, Z\right) \le 0) \Rightarrow (\operatorname{CTwo}\left(\operatorname{kronecker}\left(rho, rho\right)\right) \ge 2 \cdot \operatorname{COne}\left(rho\right))))$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.claimSelfTensor` (`✓ std3`).

*Citation.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Page 8, Conjecture 5.7 (Self-tensor superadditivity, s ≤ 0 branch): "For any qubit state ρ with s(ρ)≤ 0: C(ρ ⊗ ρ) ≥ 2C(ρ)." Every density matrix is included, with the sign condition encoded by bloch(rho,X) bloch(rho,Y) bloch(rho,Z) ≤ 0. This includes zero coordinates and the stabilizer boundary.

**Definition 1.4 (Two-qubit Pauli labels).**

$$Word = \operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right)$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word records two Pauli labels, with 0,1,2,3 denoting I,X,Y,Z.

**Definition 1.5 (Independent commuting words).**

$$\forall u \in Word,\; \forall v \in Word,\; (\operatorname{commutingIndependent}\left(u, v\right)) \Leftrightarrow ((u \ne (0,0)) \land ((v \ne (0,0)) \land ((u \ne v) \land (\operatorname{mod}\left(\operatorname{phaseProduct}\left(\operatorname{fst}\left(u\right), \operatorname{fst}\left(v\right)\right) + \operatorname{phaseProduct}\left(\operatorname{snd}\left(u\right), \operatorname{snd}\left(v\right)\right), 2\right) = 0))))$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.commutingIndependent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both words are nonidentity and distinct. The sum of their local multiplication phases is even, which is exactly commutation.

**Definition 1.6 (Rational stabilizer Wigner coordinates).**

$$\forall u \in Word,\; \forall v \in Word,\; \forall epsilon \in \operatorname{Fin}\left(2\right),\; \forall delta \in \operatorname{Fin}\left(2\right),\; \forall a \in PhasePoint \times PhasePoint,\; \operatorname{candidate}\left(u, v, epsilon, delta, a\right) = \frac{(1 + (0 - 1)^{\operatorname{val}\left(epsilon\right)} \cdot \operatorname{character}\left(\operatorname{fst}\left(u\right), \operatorname{fst}\left(a\right)\right) \cdot \operatorname{character}\left(\operatorname{snd}\left(u\right), \operatorname{snd}\left(a\right)\right) + (0 - 1)^{\operatorname{val}\left(delta\right)} \cdot \operatorname{character}\left(\operatorname{fst}\left(v\right), \operatorname{fst}\left(a\right)\right) \cdot \operatorname{character}\left(\operatorname{snd}\left(v\right), \operatorname{snd}\left(a\right)\right) + (0 - 1)^{\operatorname{val}\left(epsilon\right) + \operatorname{val}\left(delta\right)} \cdot \operatorname{ite}\left(\operatorname{mod}\left(\operatorname{phaseProduct}\left(\operatorname{fst}\left(u\right), \operatorname{fst}\left(v\right)\right) + \operatorname{phaseProduct}\left(\operatorname{snd}\left(u\right), \operatorname{snd}\left(v\right)\right), 4\right) = 0, 1, 0 - 1\right) \cdot \operatorname{character}\left(\operatorname{labelProduct}\left(\operatorname{fst}\left(u\right), \operatorname{fst}\left(v\right)\right), \operatorname{fst}\left(a\right)\right) \cdot \operatorname{character}\left(\operatorname{labelProduct}\left(\operatorname{snd}\left(u\right), \operatorname{snd}\left(v\right)\right), \operatorname{snd}\left(a\right)\right))}{16}$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.candidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signs select the two generator eigenvalues. character gives the phase-point Pauli character; phaseProduct and labelProduct give the phase and label of Pauli multiplication.

**Definition 1.7 (The finite stabilizer Wigner set).**

$$candidates = \operatorname{Finsetimage}\left(\Lambda (k:Word \times Word \times \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \mapsto \operatorname{candidate}\left(\operatorname{fst}\left(\operatorname{fst}\left(k\right)\right), \operatorname{snd}\left(\operatorname{fst}\left(k\right)\right), \operatorname{fst}\left(\operatorname{snd}\left(k\right)\right), \operatorname{snd}\left(\operatorname{snd}\left(k\right)\right)\right), \operatorname{Finsetfilter}\left(\Lambda (k:Word \times Word \times \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \mapsto \operatorname{commutingIndependent}\left(\operatorname{fst}\left(\operatorname{fst}\left(k\right)\right), \operatorname{snd}\left(\operatorname{fst}\left(k\right)\right)\right), \operatorname{Finsetuniv}\left(Word \times Word \times \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.candidates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image contains the rational Wigner vectors of all independent commuting words with both binary eigenvalue signs. Finset enumeration removes repetitions.

**Definition 1.8 (Two-generator spectral projector).**

$$\forall u \in Word,\; \forall v \in Word,\; \forall epsilon \in \operatorname{Fin}\left(2\right),\; \forall delta \in \operatorname{Fin}\left(2\right),\; \operatorname{projector}\left(u, v, epsilon, delta\right) = \operatorname{smul}\left(\frac{1}{4}, (1 + \operatorname{smul}\left((0 - 1)^{\operatorname{val}\left(epsilon\right)}, \operatorname{word}\left(u\right)\right) + \operatorname{smul}\left((0 - 1)^{\operatorname{val}\left(delta\right)}, \operatorname{word}\left(v\right)\right) + \operatorname{smul}\left((0 - 1)^{\operatorname{val}\left(epsilon\right)}, \operatorname{word}\left(u\right)\right) \cdot \operatorname{smul}\left((0 - 1)^{\operatorname{val}\left(delta\right)}, \operatorname{word}\left(v\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.projector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

word(u) is the tensor product of the Pauli matrices labelled by u. The projector averages the identity, the two signed generators, and their product.

**Theorem 1.9 (Two-qubit stabilizer generators).**

$$\forall rho \in TwoQubitMatrix,\; (rho \in \operatorname{Stab}\left(pauliTwo\right)) \Rightarrow (\exists u \in Word,\; \exists v \in Word,\; \exists epsilon \in \operatorname{Fin}\left(2\right),\; \exists delta \in \operatorname{Fin}\left(2\right),\; (\operatorname{commutingIndependent}\left(u, v\right)) \land (rho = \operatorname{projector}\left(u, v, epsilon, delta\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.stabilizer_two_generators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every subgroup-defined two-qubit stabilizer projector has two independent commuting Pauli generators and binary signs.

**Theorem 1.10 (Projector coordinates in the finite set).**

$$\forall u \in Word,\; \forall v \in Word,\; \forall epsilon \in \operatorname{Fin}\left(2\right),\; \forall delta \in \operatorname{Fin}\left(2\right),\; (\operatorname{commutingIndependent}\left(u, v\right)) \Rightarrow (\operatorname{WignerTwo}\left(\operatorname{projector}\left(u, v, epsilon, delta\right)\right) = \Lambda (a:PhasePoint \times PhasePoint) \mapsto \operatorname{realCast}\left(\operatorname{candidate}\left(u, v, epsilon, delta, a\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.projector_wigner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For independent commuting words, the complex projector has exactly the real casts of the rational candidate coordinates.

**Theorem 1.11 (Candidate membership).**

$$\forall u \in Word,\; \forall v \in Word,\; \forall epsilon \in \operatorname{Fin}\left(2\right),\; \forall delta \in \operatorname{Fin}\left(2\right),\; (\operatorname{commutingIndependent}\left(u, v\right)) \Rightarrow (\operatorname{candidate}\left(u, v, epsilon, delta\right) \in candidates)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.candidate_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every independent commuting pair and binary sign choice gives an element of the finite candidate set.

**Theorem 1.12 (One-qubit stabilizer classification).**

$$\forall rho \in QubitMatrix,\; (rho \in \operatorname{Stab}\left(pauliSet\right)) \Rightarrow (\exists p \in Pauli,\; \exists epsilon \in \operatorname{Fin}\left(2\right),\; (p \ne I) \land (rho = \operatorname{smul}\left(\frac{1}{2}, (1 + \operatorname{smul}\left((0 - 1)^{\operatorname{val}\left(epsilon\right)}, \operatorname{pauliMatrix}\left(p\right)\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.stabilizer_one_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A one-qubit stabilizer projector is a spectral projector of X, Y, or Z with either eigenvalue sign.

**Theorem 1.13 (Attaining distance on the nonpositive branch).**

$$\forall rho \in QubitMatrix,\; (\operatorname{IsDensity}\left(rho\right)) \Rightarrow ((\operatorname{bloch}\left(rho, X\right) \cdot \operatorname{bloch}\left(rho, Y\right) \cdot \operatorname{bloch}\left(rho, Z\right) \le 0) \Rightarrow (\exists f \in PhasePoint \to \mathbb{R},\; (f \in \operatorname{Wfree}\left(phasePoint, pauliSet\right)) \land ((\operatorname{norm}\left(\operatorname{toLp}\left(1, f\right)\right) = 1) \land ((\operatorname{norm}\left(\operatorname{toLp}\left(1, \operatorname{WignerOne}\left(rho\right) - f\right)\right) = \operatorname{norm}\left(\operatorname{toLp}\left(1, \operatorname{WignerOne}\left(rho\right)\right)\right) - 1) \land (\operatorname{COne}\left(rho\right) = \operatorname{norm}\left(\operatorname{toLp}\left(1, \operatorname{WignerOne}\left(rho\right)\right)\right) - 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.distance_one_nonpositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a density matrix with nonpositive Bloch product, a free Wigner vector of L1 norm one attains the error equal to the state Wigner L1 norm minus one.

**Theorem 1.14 (Equatorial multiplicativity holds).**

$$claimEquatorial$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultEquatorial` (`✓ std3`). ∎

*Resolves.* `Problems/dutta-tushar-2026-wigner-distance-equatorial-multiplicativity` (proved) by `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultEquatorial`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dutta-tushar-2026-wigner-distance-equatorial-multiplicativity","declaration_gid":"D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultEquatorial","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

Every qubit Wigner vector has at most one negative coordinate. On the nonpositive Bloch-product branch an explicit stabilizer-edge mixture has error ‖W‖₁−1. A product sign functional is bounded by one on every actual two-qubit stabilizer, using subgroup generators and an exact rational certificate on sixty candidate vectors. Convex weak duality gives the lower bound ‖W_rho‖₁ ‖W_sigma‖₁−1. The product of the two nearest mixtures gives the matching upper bound. Equatorial states lie on the zero Bloch-product branch.

**Theorem 1.15 (Self-tensor superadditivity holds).**

$$claimSelfTensor$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultSelfTensor` (`✓ std3`). ∎

*Resolves.* `Problems/dutta-tushar-2026-wigner-distance-self-tensor-superadditivity` (proved) by `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultSelfTensor`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dutta-tushar-2026-wigner-distance-self-tensor-superadditivity","declaration_gid":"D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultSelfTensor","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Soumyojyoti Dutta; Tushar (2026). *A Phase-Space Geometric Measure of Magic in Qubit Systems*. DOI: [10.48550/arXiv.2603.20792](https://doi.org/10.48550/arXiv.2603.20792). URL: <https://arxiv.org/abs/2603.20792v3>.

*Commentary.*

On the nonpositive branch COne(rho) = ‖W_rho‖₁−1. Applying the same product dual bound to two copies of rho gives at least (1+COne(rho))²−1, which is at least 2 COne(rho). The free tensor mixture establishes nonemptiness of the two-qubit free set.

## References

- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.Word`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.bloch`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.candidate`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.candidate_mem`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.candidates`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.claimEquatorial`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.claimSelfTensor`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.commutingIndependent`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.distance_one_nonpositive`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.projector`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.projector_wigner`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultEquatorial`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultSelfTensor`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.stabilizer_one_classification`
- Truth anchor: `D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.stabilizer_two_generators`
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](../Information/BinaryStabilizerLocalInequivalence.md)
- Dependency: [D5/S3/Quantum/Magic/WignerDistanceMinimum](WignerDistanceMinimum.md)
- Dependency: [D5/S3/Quantum/Magic/WignerSimplexNearestEdge](WignerSimplexNearestEdge.md)
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](../../QuantumBounds/CHSHWitness.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
