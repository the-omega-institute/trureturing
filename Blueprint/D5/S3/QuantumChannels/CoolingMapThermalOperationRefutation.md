# A cooling transition with no ground-space thermal realization

## Abstract

A four-level cooling-map transition cannot be realized by any finite ancilla in its normalized ground-space state and any energy-conserving unitary.

**Definition 1.1 (Cooling Kraus operators).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(K: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.IsCoolingKraus}\left(K\right)\right) \Leftrightarrow \left(\left(\operatorname{Matrix.IsDiag}\left(K\right)\right) \lor \left(\exists \left(j: \operatorname{Fin}\left(d\right)\right), \left(\exists \left(k: \operatorname{Fin}\left(d\right)\right), \left(\left(j < k\right) \land \left(\exists \left(c: \mathbb{C}\right), \left(K = \left(c\right) \cdot \left(\operatorname{Matrix.single}\left(j, k, \left(1: \mathbb{C}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.IsCoolingKraus` (`✓ std3`).

*Citation.* Varun Narasimhachar, Gilad Gour (2015). *Low-temperature thermodynamics with quantum coherence*. DOI: [10.1038/ncomms8689](https://doi.org/10.1038/ncomms8689). URL: <https://arxiv.org/abs/1409.7740v3>.

*Commentary.*

In the increasing energy basis, an allowed Kraus operator is diagonal or a complex multiple of the matrix unit with row j and column k, where j < k. The latter sends the kth energy coordinate to the lower jth coordinate. Zero operators are allowed. This expresses the two classes in LTT_arXiv.tex, arXiv:1409.7740v3, lines 693–700.

**Definition 1.2 (Transitions through cooling maps).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.IsCoolingMap}\left(\rho, \sigma\right)\right) \Leftrightarrow \left(\exists \left(n: \mathbb{N}\right), \left(\exists \left(K: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.IsCoolingKraus}\left(K\left(i\right)\right)\right)\right) \land \left(\left(\sum_{i: \operatorname{Fin}\left(n\right)} \left(\operatorname{Matrix.conjTranspose}\left(K\left(i\right)\right) \cdot K\left(i\right)\right) = \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right) \land \left(\operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of}_{kraus}\left(K, K\right)\left(\rho\right) = \sigma\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.IsCoolingMap` (`✓ std3`).

*Citation.* Varun Narasimhachar, Gilad Gour (2015). *Low-temperature thermodynamics with quantum coherence*. DOI: [10.1038/ncomms8689](https://doi.org/10.1038/ncomms8689). URL: <https://arxiv.org/abs/1409.7740v3>.

*Commentary.*

There is a finite Kraus family K, each member of which has one of the two allowed forms, whose adjoint products sum to the identity and whose channel sends ρ to σ. This is the state-transition reading of the cooling-map definition in LTT_arXiv.tex, lines 693–700. The completeness identity makes the Kraus channel trace preserving; its Kraus form makes it completely positive. `D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus` applies the two families by summing K i times ρ times the adjoint of K i. The two family arguments are both K.

**Definition 1.3 (All ground-energy coordinates).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(e: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.groundSet}\left(e\right): \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)\right) = \operatorname{Finset.filter}\left(\lambda \left(a: \operatorname{Fin}\left(m\right)\right) \mapsto \left(\forall \left(b: \operatorname{Fin}\left(m\right)\right), \left(e\left(a\right) \le e\left(b\right)\right)\right), \left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.groundSet` (`✓ std3`).

*Citation.* Varun Narasimhachar, Gilad Gour (2015). *Low-temperature thermodynamics with quantum coherence*. DOI: [10.1038/ncomms8689](https://doi.org/10.1038/ncomms8689). URL: <https://arxiv.org/abs/1409.7740v3>.

*Commentary.*

For the diagonal ancilla Hamiltonian with real energies e, take every coordinate a whose energy is no greater than the energy of any coordinate b. All degeneracies are retained. This describes the ground eigenspace used in LTT_arXiv.tex, lines 137–141. If m is positive this finite set is nonempty; for m = 0 it is empty.

**Definition 1.4 (The normalized ground-space projector).**

$$\forall \left(m: \mathbb{N}\right), \left(\forall \left(e: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.groundState}\left(e\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)\right) = \operatorname{Matrix.diagonal}\left(\lambda \left(a: \operatorname{Fin}\left(m\right)\right) \mapsto \left(\operatorname{ite}\left(a \in \operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.groundSet}\left(e\right), \operatorname{Inv.inv}\left(\left(\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.groundSet}\left(e\right)\right)\right): \mathbb{C}\right)\right), \left(0: \mathbb{C}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.groundState` (`✓ std3`).

*Citation.* Varun Narasimhachar, Gilad Gour (2015). *Low-temperature thermodynamics with quantum coherence*. DOI: [10.1038/ncomms8689](https://doi.org/10.1038/ncomms8689). URL: <https://arxiv.org/abs/1409.7740v3>.

*Commentary.*

The diagonal entry at a ground coordinate is the inverse of the number of ground coordinates, explicitly cast from a natural number to a complex number; every other entry is zero. For positive m this is the normalized projector onto the entire ground eigenspace. It encodes the idealized state in LTT_arXiv.tex, lines 137–141; line 648 fixes the paper's subsequent low-temperature convention. The definition also permits m = 0, when the matrix has no entries.

**Definition 1.5 (Commutation with total energy).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(E: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{R}\right)\right), \left(\forall \left(e: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right), \left(\forall \left(U: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.IsEnergyConserving}\left(E, e, U\right)\right) \Leftrightarrow \left(U \cdot \operatorname{Matrix.diagonal}\left(\lambda \left(x: \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right)\right) \mapsto \left(\operatorname{Complex.ofReal}\left(\left(E\left(\operatorname{Prod.fst}\left(x\right)\right) + e\left(\operatorname{Prod.snd}\left(x\right)\right): \mathbb{R}\right)\right)\right)\right) = \operatorname{Matrix.diagonal}\left(\lambda \left(x: \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right)\right) \mapsto \left(\operatorname{Complex.ofReal}\left(\left(E\left(\operatorname{Prod.fst}\left(x\right)\right) + e\left(\operatorname{Prod.snd}\left(x\right)\right): \mathbb{R}\right)\right)\right)\right) \cdot U\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.IsEnergyConserving` (`✓ std3`).

*Citation.* Varun Narasimhachar, Gilad Gour (2015). *Low-temperature thermodynamics with quantum coherence*. DOI: [10.1038/ncomms8689](https://doi.org/10.1038/ncomms8689). URL: <https://arxiv.org/abs/1409.7740v3>.

*Commentary.*

The total Hamiltonian is diagonal on pairs x, with energy E x.1 + e x.2. Each real sum is included in the complex scalars. Energy conservation means that U commutes with this matrix, as in LTT_arXiv.tex, lines 121–134. The predicate accepts an arbitrary complex matrix; unitarity is required separately in the transition assertion.

**Definition 1.6 (The ground-space thermal output).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(e: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right), \left(\forall \left(U: \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.thermalOutput}\left(e, U, \rho\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(U \cdot \operatorname{Matrix.kronecker}\left(\rho, \operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.groundState}\left(e\right)\right) \cdot \operatorname{Matrix.conjTranspose}\left(U\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.thermalOutput` (`✓ std3`).

*Citation.* Varun Narasimhachar, Gilad Gour (2015). *Low-temperature thermodynamics with quantum coherence*. DOI: [10.1038/ncomms8689](https://doi.org/10.1038/ncomms8689). URL: <https://arxiv.org/abs/1409.7740v3>.

*Commentary.*

Tensor ρ with the ancilla's normalized ground-space projector, conjugate by U, and trace out the ancilla. This combines LTT_arXiv.tex, lines 126–128 and 137–141, with the idealized ground-space convention of line 648. `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight` retains the system coordinate and sums the diagonal ancilla coordinates. The definition itself imposes neither unitarity nor energy conservation.

**Definition 1.7 (The state-transition direction of Conjecture 1).**

$$\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(E: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{StrictMono}\left(E\right)\right) \Rightarrow \left(\left(\forall \left(i: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(k: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(l: \operatorname{Fin}\left(d\right)\right), \left(\left(i < j\right) \Rightarrow \left(\left(k < l\right) \Rightarrow \left(\left(E\left(j\right) - E\left(i\right) = E\left(l\right) - E\left(k\right)\right) \Rightarrow \left(\left(i = k\right) \land \left(j = l\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\sigma\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.IsCoolingMap}\left(\rho, \sigma\right)\right) \Rightarrow \left(\exists \left(m: \mathbb{N}\right), \left(\exists \left(e: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right), \left(\exists \left(U: \operatorname{Matrix.unitaryGroup}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right), \left(\left(\left(0: \mathbb{N}\right) < m\right) \land \left(\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.IsEnergyConserving}\left(E, e, \left(\operatorname{Subtype.val}\left(U\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right)\right)\right) \land \left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.thermalOutput}\left(e, \left(\operatorname{Subtype.val}\left(U\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right), \rho\right) = \sigma\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Varun Narasimhachar, Gilad Gour (2015). *Low-temperature thermodynamics with quantum coherence*. DOI: [10.1038/ncomms8689](https://doi.org/10.1038/ncomms8689). URL: <https://arxiv.org/abs/1409.7740v3>.

*Commentary.*

Conjecture 1 states: "Cooling maps are equivalent to low-temperature thermal operations, with regard to the feasibility of state transitions." LTT_arXiv.tex, lines 924–927, explicitly distinguishes this assertion from equality of the two sets of channels. The formula expresses its cooling-to-thermal direction for every finite system with strictly increasing energies and distinct positive gaps, the assumptions in lines 109–111. Both input and output satisfy `D5/S3/Quantum/Information/SLDSpectralEnergy.IsDensity`, meaning positive semidefiniteness and trace one. The ancilla has positive finite dimension, arbitrary real diagonal energies and its full normalized ground-space state. The unitary is explicitly coerced to a matrix in both occurrences. A change of ancilla energy basis can be absorbed into the unitary. The assertion uses the exact idealized state; it makes no assertion about positive-temperature or approximate transitions.

**Theorem 1.8 (A four-level counterexample).**

$$\neg \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(E: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{StrictMono}\left(E\right)\right) \Rightarrow \left(\left(\forall \left(i: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(k: \operatorname{Fin}\left(d\right)\right), \left(\forall \left(l: \operatorname{Fin}\left(d\right)\right), \left(\left(i < j\right) \Rightarrow \left(\left(k < l\right) \Rightarrow \left(\left(E\left(j\right) - E\left(i\right) = E\left(l\right) - E\left(k\right)\right) \Rightarrow \left(\left(i = k\right) \land \left(j = l\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(\sigma: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\sigma\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.IsCoolingMap}\left(\rho, \sigma\right)\right) \Rightarrow \left(\exists \left(m: \mathbb{N}\right), \left(\exists \left(e: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\mathbb{R}\right)\right), \left(\exists \left(U: \operatorname{Matrix.unitaryGroup}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right), \left(\left(\left(0: \mathbb{N}\right) < m\right) \land \left(\left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.IsEnergyConserving}\left(E, e, \left(\operatorname{Subtype.val}\left(U\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right)\right)\right) \land \left(\operatorname{D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation.thermalOutput}\left(e, \left(\operatorname{Subtype.val}\left(U\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(m\right)\right), \mathbb{C}\right)\right), \rho\right) = \sigma\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/narasimhachar-gour-2015-cooling-map-thermal-operation-refutation` (refuted) by `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"narasimhachar-gour-2015-cooling-map-thermal-operation-refutation","declaration_gid":"D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Varun Narasimhachar, Gilad Gour (2015). *Low-temperature thermodynamics with quantum coherence*. DOI: [10.1038/ncomms8689](https://doi.org/10.1038/ncomms8689). URL: <https://arxiv.org/abs/1409.7740v3>.

*Commentary.*

Take d = 4 and E = (0, 1, 3, 7), with coordinates numbered 0 through 3. The six positive gaps are 1, 2, 3, 4, 6 and 7, all distinct. Let V have rows (1, 0), (0, 1), (3/5, 4/5) and (3/5, 4i/5), where i is the imaginary unit. Put σ = VV†/4 and let K 0 and K 1 be the diagonal matrices formed from the two columns of V. Every row of V has squared norm one, so (K 0)†K 0 + (K 1)†K 1 = I and every diagonal entry of σ is 1/4.

Use the matrix `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.Pm` as ρ: every entry is 1/4. It is vv† for v = (1/2, 1/2, 1/2, 1/2), hence positive semidefinite with trace one. The same properties hold for σ, since VV† is positive semidefinite and σ has four diagonal entries 1/4. The two diagonal Kraus operators send ρ to σ by direct multiplication, proving that the transition is a cooling transition.

For any positive finite ancilla dimension m and energy function e, let G be the set of its minimum-energy coordinates and g its cardinality. A finite minimum exists, so g > 0. If U commutes with the total Hamiltonian, its entry U((j,b),(k,a)) vanishes whenever E j + e b differs from E k + e a. For a in G and k < j, minimality of e a and strict increase of E force this inequality of total energies. Thus a ground-space input cannot raise the system energy.

Expanding the partial trace of U(ρ ⊗ groundState e)U† gives its (i,j) entry as 1/(4g) times the sum of U((i,b),(k,a)) conjugate(U((j,b),(l,a))) over b, l, a in G and k. For a diagonal output entry, energy conservation and injectivity of E eliminate the terms with k ≠ l. The real population at j is therefore 1/(4g) times the sum of |U((j,b),(k,a))|² over k, a in G and b.

Define the real matrix T by T(j,k) = ∑ over a in G and b of |U((j,b),(k,a))|². All entries are nonnegative. If the output is σ, its uniform populations give row sums g. Unitarity gives column sums g, while the downward-energy restriction makes T(j,k) zero for k < j. Comparing row 0 with column 0 forces T(0,1), T(0,2) and T(0,3) to vanish. Comparing row 1 with column 1 then forces T(1,2) and T(1,3) to vanish, and the corresponding comparison at 2 forces T(2,3) to vanish. Thus every off-diagonal entry of T is zero.

A zero sum of these nonnegative squared moduli forces every summand to vanish. Hence for a in G, U((j,b),(k,a)) is zero when j ≠ k. When j = k but b is outside G, equality of total energies would imply e b = e a, placing b in G; energy conservation therefore forces these entries to vanish as well. For each k, restrict U to the coordinates (k,a) with a in G and call the resulting square matrix A k. The support just proved reduces U†U = I to (A k)†A k = I on G, so each A k is unitary.

Return to the full output-entry expansion. The same support restrictions leave only system indices k = i and l = j, and ancilla indices in G. The remaining sum is trace((A i)(A j)†), so equality of the output with σ gives trace((A i)(A j)†) = g(VV†)(i,j) for all i and j. Expand the squared Hilbert–Schmidt norms of A 2 − (3/5)A 0 − (4/5)A 1 and A 3 − (3/5)A 0 − (4i/5)A 1. Substitution of these trace identities and the displayed rows of V makes both squared norms zero. Consequently A 2 = (3/5)A 0 + (4/5)A 1 and A 3 = (3/5)A 0 + (4i/5)A 1.

Set X = (A 0)(A 1)†. Expand the unitary identities (A 2)(A 2)† = I and (A 3)(A 3)† = I using those two linear relations and the unitarity of A 0 and A 1. The first gives X + X† = 0; the second gives X − X† = 0. Thus X = 0. But X is a product of unitaries on the nonempty space indexed by G, hence invertible and nonzero, a contradiction.

Finally, applying the asserted transition principle to E, ρ and σ would provide precisely such a positive finite ancilla, energy-conserving unitary and thermal output. The contradiction refutes the stated direction of Conjecture 1. It concerns exact finite ground-space thermal operations and does not assert a result for their approximate or positive-temperature variants.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus`
- Truth anchor: `D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.Pm`
- Truth anchor: `D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight`
- Truth anchor: `D5/S3/Quantum/Information/SLDSpectralEnergy.IsDensity`
- Truth anchor: `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.IsCoolingKraus`
- Truth anchor: `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.IsCoolingMap`
- Truth anchor: `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.IsEnergyConserving`
- Truth anchor: `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.groundSet`
- Truth anchor: `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.groundState`
- Truth anchor: `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.result`
- Truth anchor: `D5/S3/QuantumChannels/CoolingMapThermalOperationRefutation.thermalOutput`
- Dependency: [D5/S3/Quantum/Decoherence/FiniteShiftedRecordChannel](../Quantum/Decoherence/FiniteShiftedRecordChannel.md)
- Dependency: [D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer](../Quantum/Information/NiceErrorBasisNonNormalStabilizer.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Quantum/Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../Quantum/Information/SLDSpectralEnergy.md)
