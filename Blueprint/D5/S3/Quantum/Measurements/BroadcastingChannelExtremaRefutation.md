# Broadcasting channels need have neither extremum

## Abstract

A three-dimensional observable with two outcomes has a nonempty set of broadcasting channels and has neither extremum under nondisturbing precomposition.

**Theorem 1.1 (Density matrices are contractions).**

$$\forall n \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)], \forall T \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(T\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(T\right) = 1) \Rightarrow (\operatorname{Matrix}.\operatorname{PosSemidef}\left(1 - T\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.density_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive semidefinite complex matrix of trace one is bounded above by the identity in the positive semidefinite order.

**Definition 1.2 (Finite Kraus channels).**

$$\forall d \in \mathbb{N},\; \forall iota \in Type,\; [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(iota, iota, \mathbb{C}\right),\; (\operatorname{IsChannel}\left(Phi\right)) \Leftrightarrow (\exists k \in \mathbb{N},\; \exists K \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(iota, \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\sum_{j : \operatorname{Fin}\left(k\right)} ((\operatorname{Matrix}.\operatorname{conjTranspose}\left(K\left(j\right)\right)) \cdot (K\left(j\right))) = 1) \land (\forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; Phi\left(X\right) = \operatorname{MatrixMap}.\operatorname{of}_{kraus}\left(K, K, X\right)))$$

*Formalization.* `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.IsChannel` (`✓ std3`).

*Citation.* A. Mitra (2021). *Layers of classicality in the compatibility of measurements*. DOI: [10.1103/PhysRevA.104.022206](https://doi.org/10.1103/PhysRevA.104.022206). URL: <https://arxiv.org/abs/2101.05752v4>.

*Commentary.*

Section II.B, p. 2: “A CPTP map Θ : S(Hin) → S(Hout) is called a quantum channel, where Hin and Hout are two Hilbert spaces [15].” Finite Kraus form expresses complete positivity and trace preservation. MatrixMap.of_kraus is the frozen operation; its action is the finite sum of K(j) X conjTranspose(K(j)). The output index type iota has anonymous Fintype and DecidableEq instances.

**Definition 1.3 (Broadcasting an observable).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{Broadcasts}\left(A, L\right)) \Leftrightarrow ((\operatorname{IsChannel}\left(L\right)) \land (\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{GHZMeasureBiseparableBound}.\operatorname{IsDensity}\left(rho\right)) \Rightarrow (\forall x \in \operatorname{Fin}\left(m\right),\; (\operatorname{Matrix}.\operatorname{trace}\left((L\left(rho\right)) \cdot (\operatorname{Matrix}.\operatorname{kronecker}\left(A\left(x\right), 1\right))\right) = \operatorname{Matrix}.\operatorname{trace}\left((rho) \cdot (A\left(x\right))\right)) \land (\operatorname{Matrix}.\operatorname{trace}\left((L\left(rho\right)) \cdot (\operatorname{Matrix}.\operatorname{kronecker}\left(1, A\left(x\right)\right))\right) = \operatorname{Matrix}.\operatorname{trace}\left((rho) \cdot (A\left(x\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.Broadcasts` (`✓ std3`).

*Citation.* A. Mitra (2021). *Layers of classicality in the compatibility of measurements*. DOI: [10.1103/PhysRevA.104.022206](https://doi.org/10.1103/PhysRevA.104.022206). URL: <https://arxiv.org/abs/2101.05752v4>.

*Commentary.*

Definition 1, p. 2: “A channel Λ : S(H) → S(H_A ⊗ H_B) with H_A = H_B = H is called a broadcasting channel.” Definition 3, p. 3: “An observable A ∈ O_X^d is broadcast by a broadcasting channel Λ ∈ C_broad^d if for all ρ ∈ S(H), x ∈ X” followed by equation (5), Tr[ρA(x)] = Tr[Λ(ρ)A(x) ⊗ I] = Tr[Λ(ρ)I ⊗ A(x)]. Outcomes are Fin m, and each subsystem is indexed by Fin d. The state predicate is the frozen GHZMeasureBiseparableBound.IsDensity: positive semidefinite with trace one.

**Definition 1.4 (Nondisturbing channels).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall Theta \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{Nondisturbing}\left(A, Theta\right)) \Leftrightarrow ((\operatorname{IsChannel}\left(Theta\right)) \land (\forall rho \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{GHZMeasureBiseparableBound}.\operatorname{IsDensity}\left(rho\right)) \Rightarrow (\forall x \in \operatorname{Fin}\left(m\right),\; \operatorname{Matrix}.\operatorname{trace}\left((Theta\left(rho\right)) \cdot (A\left(x\right))\right) = \operatorname{Matrix}.\operatorname{trace}\left((rho) \cdot (A\left(x\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.Nondisturbing` (`✓ std3`).

*Citation.* A. Mitra (2021). *Layers of classicality in the compatibility of measurements*. DOI: [10.1103/PhysRevA.104.022206](https://doi.org/10.1103/PhysRevA.104.022206). URL: <https://arxiv.org/abs/2101.05752v4>.

*Commentary.*

Definition 8, p. 5: “A channel Θ : S(H) → S(H) is nondisturbing with respect to an observable A if for all ρ ∈ S(H),” followed by equation (22), Tr[ρA(x)] = Tr[Θ(ρ)A(x)] for all x ∈ Ω_A. The displayed formula uses this trace form, equivalent to the dual form in equation (23).

**Definition 1.5 (Nondisturbing precomposition).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall Lprime \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{ConstructedFrom}\left(A, Lprime, L\right)) \Leftrightarrow (\exists Theta \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{Nondisturbing}\left(A, Theta\right)) \land (Lprime = L \circ Theta))$$

*Formalization.* `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.ConstructedFrom` (`✓ std3`).

*Citation.* A. Mitra (2021). *Layers of classicality in the compatibility of measurements*. DOI: [10.1103/PhysRevA.104.022206](https://doi.org/10.1103/PhysRevA.104.022206). URL: <https://arxiv.org/abs/2101.05752v4>.

*Commentary.*

Section III.A, p. 5 uses concatenation with nondisturbing channels. ConstructedFrom A Lprime L states that Lprime = L ∘ Theta for such a channel Theta. Equality is equality on all complex matrices.

**Definition 1.6 (Highest element).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{HasHighest}\left(A\right)) \Leftrightarrow (\exists H \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{Broadcasts}\left(A, H\right)) \land (\forall L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{Broadcasts}\left(A, L\right)) \Rightarrow (\operatorname{ConstructedFrom}\left(A, L, H\right))))$$

*Formalization.* `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.HasHighest` (`✓ std3`).

*Citation.* A. Mitra (2021). *Layers of classicality in the compatibility of measurements*. DOI: [10.1103/PhysRevA.104.022206](https://doi.org/10.1103/PhysRevA.104.022206). URL: <https://arxiv.org/abs/2101.05752v4>.

*Commentary.*

Section III.A, p. 5: “For an observable, in this way, one can get the set of different broadcasting channels that broadcast the observable. It is an open question whether this set has the highest element i.e., a broadcasting channel in this set from which all other broadcasting channels that can broadcast the observable, can be constructed through concatenation with nondisturbing channels. It is also an open question whether this set has the lowest element i.e., a broadcasting channel in this set which can be constructed from all other broadcasting channels that broadcast the observable through concatenation with nondisturbing channels.” HasHighest requires a broadcasting channel H from which every broadcasting channel L is obtained by nondisturbing precomposition.

**Definition 1.7 (Lowest element).**

$$\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{HasLowest}\left(A\right)) \Leftrightarrow (\exists H \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{Broadcasts}\left(A, H\right)) \land (\forall L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{Broadcasts}\left(A, L\right)) \Rightarrow (\operatorname{ConstructedFrom}\left(A, H, L\right))))$$

*Formalization.* `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.HasLowest` (`✓ std3`).

*Citation.* A. Mitra (2021). *Layers of classicality in the compatibility of measurements*. DOI: [10.1103/PhysRevA.104.022206](https://doi.org/10.1103/PhysRevA.104.022206). URL: <https://arxiv.org/abs/2101.05752v4>.

*Commentary.*

Section III.A, p. 5: “For an observable, in this way, one can get the set of different broadcasting channels that broadcast the observable. It is an open question whether this set has the highest element i.e., a broadcasting channel in this set from which all other broadcasting channels that can broadcast the observable, can be constructed through concatenation with nondisturbing channels. It is also an open question whether this set has the lowest element i.e., a broadcasting channel in this set which can be constructed from all other broadcasting channels that broadcast the observable through concatenation with nondisturbing channels.” HasLowest requires a broadcasting channel H obtained from every broadcasting channel L by nondisturbing precomposition.

**Definition 1.8 (The two extremum questions).**

$$(claim) \Leftrightarrow (\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{ConcealmentKernelNecessityRefutation}.\operatorname{IsPOVM}\left(A\right)) \Rightarrow ((\exists L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{Broadcasts}\left(A, L\right)) \Rightarrow ((\operatorname{HasHighest}\left(A\right)) \lor (\operatorname{HasLowest}\left(A\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.claim` (`✓ std3`).

*Citation.* A. Mitra (2021). *Layers of classicality in the compatibility of measurements*. DOI: [10.1103/PhysRevA.104.022206](https://doi.org/10.1103/PhysRevA.104.022206). URL: <https://arxiv.org/abs/2101.05752v4>.

*Commentary.*

Section III.A, p. 5: “For an observable, in this way, one can get the set of different broadcasting channels that broadcast the observable. It is an open question whether this set has the highest element i.e., a broadcasting channel in this set from which all other broadcasting channels that can broadcast the observable, can be constructed through concatenation with nondisturbing channels. It is also an open question whether this set has the lowest element i.e., a broadcasting channel in this set which can be constructed from all other broadcasting channels that broadcast the observable through concatenation with nondisturbing channels.” The universal encoding quantifies over natural dimensions d, outcome counts m, and all observables A. The frozen ConcealmentKernelNecessityRefutation.IsPOVM means that every effect is positive semidefinite and their sum is I. Nonemptiness of the broadcasting set is explicit. The disjunction allows either extremum; its negation exhibits one observable lacking both.

**Theorem 1.9 (Both answers can be negative).**

$$\neg (\forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{ConcealmentKernelNecessityRefutation}.\operatorname{IsPOVM}\left(A\right)) \Rightarrow ((\exists L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{Broadcasts}\left(A, L\right)) \Rightarrow ((\operatorname{HasHighest}\left(A\right)) \lor (\operatorname{HasLowest}\left(A\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/mitra-2021-broadcasting-channel-extrema` (refuted) by `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mitra-2021-broadcasting-channel-extrema","declaration_gid":"D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Mitra (2021). *Layers of classicality in the compatibility of measurements*. DOI: [10.1103/PhysRevA.104.022206](https://doi.org/10.1103/PhysRevA.104.022206). URL: <https://arxiv.org/abs/2101.05752v4>.

*Commentary.*

Take d = 3, m = 2, P = diag(1,1,0), Q = I − P, A(0) = (3/4)P + (1/4)Q, and A(1) = I − A(0). Three broadcasting channels prepare the matrix units at (0,0), (1,1), and (0,1) on the P sector and at (2,2) on the Q sector. Preservation of A(0) and trace forces preservation of P. ConcealmentKernelNecessityRefutation.dual_kraus identifies the dual effect. The balanced state on coordinates zero and two is ActualQubitChordObstruction.signalProbe 1. Together with the other normalized real and imaginary pure states it determines the dual effect on all matrices, so nondisturbing precomposition fixes each of the three channels. Their inequality excludes a lowest element. FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero applied to I − P places the three input states of a highest element in the P sector. They would produce three orthogonal pure outputs. Positivity and the dual Kraus completeness identity bound their total trace by trace(P) = 2, although each output contributes at least one. Thus 3 ≤ 2, a contradiction. Only this three-dimensional, two-outcome instance is asserted; the rank-r family and the qubit and sharp-observable questions remain open here.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.Broadcasts`
- Truth anchor: `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.ConstructedFrom`
- Truth anchor: `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.HasHighest`
- Truth anchor: `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.HasLowest`
- Truth anchor: `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.IsChannel`
- Truth anchor: `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.Nondisturbing`
- Truth anchor: `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.density_le_one`
- Truth anchor: `D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](../Entanglement/GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/ActualQubitChordObstruction](../Information/ActualQubitChordObstruction.md)
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](FiniteMemoryHistoryCapacity.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/PositiveFilterTransposeRefutation](../QuantumChannels/PositiveFilterTransposeRefutation.md)
- Dependency: [D5/S3/Quantum/Recovery/KrausCompletion](../Recovery/KrausCompletion.md)
