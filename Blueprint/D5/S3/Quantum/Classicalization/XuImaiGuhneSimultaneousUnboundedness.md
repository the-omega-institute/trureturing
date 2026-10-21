# Two unbounded entanglement gaps with one qubit

## Abstract

Both classicalization gaps for tripartite negativity are unbounded with a qubit measured party.

**Definition 1.1 (tripartiteNegativity).**

$$\forall (A : Type) , (\forall (B : Type) , (\forall (C : Type) , ([Fintype\left(A\right)] , [DecidableEq\left(A\right)] , [Fintype\left(B\right)] , [DecidableEq\left(B\right)] , [Fintype\left(C\right)] , [DecidableEq\left(C\right)] , \forall (rho : Matrix\left((A \times (B \times C)), (A \times (B \times C)), \mathbb{C}\right)) , (tripartiteNegativity\left(rho\right) = negativity\left(\operatorname{Matrix}.\operatorname{submatrix}\left(rho, (\operatorname{Equiv}.\operatorname{prodAssoc}\left(A, B, C\right)), (\operatorname{Equiv}.\operatorname{prodAssoc}\left(A, B, C\right))\right)\right) + negativity\left(\operatorname{Matrix}.\operatorname{submatrix}\left(rho, (\operatorname{Equiv}.\operatorname{prodComm}\left((B \times C), A\right)), (\operatorname{Equiv}.\operatorname{prodComm}\left((B \times C), A\right))\right)\right) + negativity\left(\operatorname{Matrix}.\operatorname{submatrix}\left(rho, (fun (p : ((A \times C) \times B)) \mapsto (((p).1).1, (p).2, ((p).1).2)), (fun (p : ((A \times C) \times B)) \mapsto (((p).1).1, (p).2, ((p).1).2))\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.tripartiteNegativity` (`✓ std3`).

*Citation.* Zhen-Peng Xu, Satoya Imai, and Otfried Gühne (2023). *Fate of multiparticle entanglement when one particle becomes classical*. DOI: [10.1103/PhysRevA.107.L040401](https://doi.org/10.1103/PhysRevA.107.L040401). URL: <https://arxiv.org/abs/2206.12834v2>.

*Commentary.*

Equation (4), page 3: “N_ABC(ρ_ABC) = N_{AB|C} + N_{BC|A} + N_{AC|B}”, where N_{X|Y} “is the negativity for a bipartition X|Y with eigenvalues λ_i of the partial transposed state ρ^{T_Y} with respect to the subsystem Y”. The three regroupings transpose C, A and B respectively. The bipartite negativity is (traceNorm(partialTranspose ρ) − 1)/2; its sign is the standard positive negativity, as in the source's numerical values.

**Definition 1.2 (branch).**

$$\forall (A : Type) , (\forall (B : Type) , (\forall (C : Type) , ([Fintype\left(C\right)] , \forall (rho : Matrix\left((A \times (B \times C)), (A \times (B \times C)), \mathbb{C}\right)) , (\forall (m : Matrix\left(C, C, \mathbb{C}\right)) , (branch\left(rho, m\right) = (fun (p : (A \times B)) \mapsto fun (q : (A \times B)) \mapsto \sum c : C , \sum z : C , rho\left(((p).1, (p).2, c), ((q).1, (q).2, z)\right) \cdot m\left(z, c\right)))))))$$

*Formalization.* `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.branch` (`✓ std3`).

*Citation.* Zhen-Peng Xu, Satoya Imai, and Otfried Gühne (2023). *Fate of multiparticle entanglement when one particle becomes classical*. DOI: [10.1103/PhysRevA.107.L040401](https://doi.org/10.1103/PhysRevA.107.L040401). URL: <https://arxiv.org/abs/2206.12834v2>.

*Commentary.*

Equation (1), page 2: “p_i = tr(ρ_ABC m_i), σ_i = tr_C(ρ_ABC m_i)/p_i”. The branch is the unnormalized matrix p_i σ_i, so it also covers zero-probability outcomes without division.

**Definition 1.3 (classicalize).**

$$\forall (A : Type) , (\forall (B : Type) , (\forall (C : Type) , (\forall (I : Type) , (\forall (E : Type) , ([Fintype\left(C\right)] , [Fintype\left(I\right)] , \forall (rho : Matrix\left((A \times (B \times C)), (A \times (B \times C)), \mathbb{C}\right)) , (\forall (m : I \to Matrix\left(C, C, \mathbb{C}\right)) , (\forall (tau : I \to Matrix\left(E, E, \mathbb{C}\right)) , (classicalize\left(rho, m, tau\right) = (fun (p : (A \times (B \times E))) \mapsto fun (q : (A \times (B \times E))) \mapsto \sum i : I , branch\left(rho, m\left(i\right)\right)\left(((p).1, ((p).2).1), ((q).1, ((q).2).1)\right) \cdot tau\left(i, ((p).2).2, ((q).2).2\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.classicalize` (`✓ std3`).

*Citation.* Zhen-Peng Xu, Satoya Imai, and Otfried Gühne (2023). *Fate of multiparticle entanglement when one particle becomes classical*. DOI: [10.1103/PhysRevA.107.L040401](https://doi.org/10.1103/PhysRevA.107.L040401). URL: <https://arxiv.org/abs/2206.12834v2>.

*Commentary.*

Equation (1), page 2: “Φ_C(ρ_ABC) = Σ_i p_i σ_i ⊗ τ_i, where p_i = tr(ρ_ABC m_i), σ_i = tr_C(ρ_ABC m_i)/p_i and τ_i is the register state related to the outcome i”. The outcome type is any finite type, and the prepared register has carrier E.

**Definition 1.4 (delta).**

$$\forall (A : Type) , (\forall (B : Type) , (\forall (C : Type) , ([Fintype\left(A\right)] , [DecidableEq\left(A\right)] , [Fintype\left(B\right)] , [DecidableEq\left(B\right)] , [Fintype\left(C\right)] , [DecidableEq\left(C\right)] , \forall (rho : Matrix\left((A \times (B \times C)), (A \times (B \times C)), \mathbb{C}\right)) , (delta\left(rho\right) = sInf\left(\{x : \mathbb{R} \mid \exists (k : \mathbb{N}) , (\exists (e : \mathbb{N}) , (\exists (m : Fin\left(k\right) \to Matrix\left(C, C, \mathbb{C}\right)) , (\exists (tau : Fin\left(k\right) \to Matrix\left(Fin\left(e\right), Fin\left(e\right), \mathbb{C}\right)) , (((\forall (i : Fin\left(k\right)) , ((m\left(i\right)).\operatorname{PosSemidef})) \land (\sum i : Fin\left(k\right) , m\left(i\right) = 1)) \land ((\forall (i : Fin\left(k\right)) , (((tau\left(i\right)).\operatorname{PosSemidef}) \land ((tau\left(i\right)).\operatorname{trace} = 1))) \land (x = tripartiteNegativity\left(rho\right) - tripartiteNegativity\left(classicalize\left(rho, m, tau\right)\right)))))))\}\right)))))$$

*Formalization.* `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.delta` (`✓ std3`).

*Citation.* Zhen-Peng Xu, Satoya Imai, and Otfried Gühne (2023). *Fate of multiparticle entanglement when one particle becomes classical*. DOI: [10.1103/PhysRevA.107.L040401](https://doi.org/10.1103/PhysRevA.107.L040401). URL: <https://arxiv.org/abs/2206.12834v2>.

*Commentary.*

Equation (2), page 2: “Δ_E(ρ_ABC) = min_{Φ_C ∈ N_C} {E[ρ_ABC] − E[Φ_C(ρ_ABC)]}”. Here E is tripartiteNegativity. Effects are positive semidefinite and sum to the identity; each register matrix is positive semidefinite with trace one. The infimum ranges over every finite outcome count and every finite register dimension. For the constructed family the infimum is attained by a two-outcome measurement with two orthogonal qubit states.

**Definition 1.5 (deltaTilde).**

$$\forall (A : Type) , (\forall (B : Type) , ([Fintype\left(A\right)] , [DecidableEq\left(A\right)] , [Fintype\left(B\right)] , [DecidableEq\left(B\right)] , \forall (rho : Matrix\left((A \times (B \times Fin\left(2\right))), (A \times (B \times Fin\left(2\right))), \mathbb{C}\right)) , (deltaTilde\left(rho\right) = tripartiteNegativity\left(rho\right) - tripartiteNegativity\left((fun (p : (A \times (B \times Fin\left(2\right)))) \mapsto fun (q : (A \times (B \times Fin\left(2\right)))) \mapsto branch\left(rho, 1\right)\left(((p).1, ((p).2).1), ((q).1, ((q).2).1)\right) \cdot (if ((((p).2).2 = 0) \land (((q).2).2 = 0)) then 1 else 0))\right))))$$

*Formalization.* `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.deltaTilde` (`✓ std3`).

*Citation.* Zhen-Peng Xu, Satoya Imai, and Otfried Gühne (2023). *Fate of multiparticle entanglement when one particle becomes classical*. DOI: [10.1103/PhysRevA.107.L040401](https://doi.org/10.1103/PhysRevA.107.L040401). URL: <https://arxiv.org/abs/2206.12834v2>.

*Commentary.*

Equation (9), page 3: “Δ̃_E(ρ_ABC) = E[ρ_ABC] − E[ρ_AB ⊗ |0⟩⟨0|], with ρ_AB = tr_C(ρ_ABC)”. The register is Fin 2 and its zero basis vector supplies the rank-one flag.

**Definition 1.6 (claim).**

$$claim = (\forall (M : \mathbb{R}) , (\exists (a : \mathbb{N}) , (\exists (b : \mathbb{N}) , (\exists (rho : Matrix\left((Fin\left(a\right) \times (Fin\left(b\right) \times Fin\left(2\right))), (Fin\left(a\right) \times (Fin\left(b\right) \times Fin\left(2\right))), \mathbb{C}\right)) , ((((rho).\operatorname{PosSemidef}) \land ((rho).\operatorname{trace} = 1)) \land ((M < delta\left(rho\right)) \land (M < deltaTilde\left(rho\right) - delta\left(rho\right))))))))$$

*Formalization.* `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.claim` (`✓ std3`).

*Citation.* Zhen-Peng Xu, Satoya Imai, and Otfried Gühne (2023). *Fate of multiparticle entanglement when one particle becomes classical*. DOI: [10.1103/PhysRevA.107.L040401](https://doi.org/10.1103/PhysRevA.107.L040401). URL: <https://arxiv.org/abs/2206.12834v2>.

*Commentary.*

Section V.B, page 5: “Inspired by those two examples, an interesting question arises whether there exist entanglement measures E and states ρ_ABC such that both Δ_E(ρ_ABC) and Δ̃_E(ρ_ABC) − Δ_E(ρ_ABC) can be arbitrarily large in the sense that they are not limited by the size of C, even if C is only a qubit. We leave this question for further research.” The proposition answers the question with the fixed measure tripartiteNegativity. A and B have arbitrary finite dimensions, C has dimension exactly two, and a single state exceeds the same real threshold in both gaps.

**Theorem 1.7 (Simultaneous unboundedness).**

$$\forall (M : \mathbb{R}) , (\exists (a : \mathbb{N}) , (\exists (b : \mathbb{N}) , (\exists (rho : Matrix\left((Fin\left(a\right) \times (Fin\left(b\right) \times Fin\left(2\right))), (Fin\left(a\right) \times (Fin\left(b\right) \times Fin\left(2\right))), \mathbb{C}\right)) , ((((rho).\operatorname{PosSemidef}) \land ((rho).\operatorname{trace} = 1)) \land ((M < delta\left(rho\right)) \land (M < deltaTilde\left(rho\right) - delta\left(rho\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhen-Peng Xu, Satoya Imai, and Otfried Gühne (2023). *Fate of multiparticle entanglement when one particle becomes classical*. DOI: [10.1103/PhysRevA.107.L040401](https://doi.org/10.1103/PhysRevA.107.L040401). URL: <https://arxiv.org/abs/2206.12834v2>.

*Commentary.*

Tensor a normalized three-qubit W state with a maximally entangled state of local dimension d on A and B. Rank-one refinement of any qubit POVM gives branch partial-transpose norms (4|α|²+|β|²)/3, whose sum is 5/3. The triangle inequality bounds the output entanglement by 5d/3−1, attained with computational-basis measurement and orthogonal flags. The output-register cut has zero negativity. The two gaps equal [2d(√2−1)+√2]/3 and d(3−√5)/3. Both coefficients of d are positive; choosing d sufficiently large proves the displayed proposition.

## References

- Truth anchor: `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.branch`
- Truth anchor: `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.claim`
- Truth anchor: `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.classicalize`
- Truth anchor: `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.delta`
- Truth anchor: `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.deltaTilde`
- Truth anchor: `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.result`
- Truth anchor: `D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.tripartiteNegativity`
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Dynamics/KickedIsingNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation](../Entanglement/EnergyRestrictedUnitaryEncodingRefutation.md)
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](../Entanglement/GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/Quantum/Schatten/TraceNorm](../Schatten/TraceNorm.md)
- Dependency: [D5/S3/QuantumBounds/NegativityReductionInclusionRefutation](../../QuantumBounds/NegativityReductionInclusionRefutation.md)
- Dependency: [D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance](../../QuantumChannels/SchurChannelMixedUnitaryDistance.md)
