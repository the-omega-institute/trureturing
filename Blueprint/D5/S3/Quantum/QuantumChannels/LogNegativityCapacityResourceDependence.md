# Log-negativity capacity depends on the input resource

## Abstract

A two-qutrit CPTP map separates assisted and separable-input log-negativity capacities.

**Definition 1.1 (Free local ancillary systems).**

$$\forall (dA : \mathbb{N}), \forall (dB : \mathbb{N}), \forall (r : \mathbb{N}), \forall (K : \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), (\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), \mathbb{C}\right)), \forall (a : \mathbb{N}), \forall (b : \mathbb{N}), \forall (rho : \operatorname{Matrix}\left(((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(a\right)) \times (\operatorname{Fin}\left(dB\right) \times \operatorname{Fin}\left(b\right))), ((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(a\right)) \times (\operatorname{Fin}\left(dB\right) \times \operatorname{Fin}\left(b\right))), \mathbb{C}\right)), \operatorname{extend}\left(K, rho\right) = \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of}_{kraus}\left(\lambda (k : \operatorname{Fin}\left(r\right)) \mapsto \operatorname{reindex}\left(\operatorname{prodProdProdComm}\left(\operatorname{Fin}\left(dA\right), \operatorname{Fin}\left(dB\right), \operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \operatorname{prodProdProdComm}\left(\operatorname{Fin}\left(dA\right), \operatorname{Fin}\left(dB\right), \operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \operatorname{kronecker}\left(K\left(k\right), (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right)), (\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right)), \mathbb{C}\right))\right)\right), \lambda (k : \operatorname{Fin}\left(r\right)) \mapsto \operatorname{reindex}\left(\operatorname{prodProdProdComm}\left(\operatorname{Fin}\left(dA\right), \operatorname{Fin}\left(dB\right), \operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \operatorname{prodProdProdComm}\left(\operatorname{Fin}\left(dA\right), \operatorname{Fin}\left(dB\right), \operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right)\right), \operatorname{kronecker}\left(K\left(k\right), (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right)), (\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right)), \mathbb{C}\right))\right)\right)\right)\left(rho\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.extend` (`✓ std3`).

*Citation.* Earl T. Campbell (2010). *Optimal entangling capacity of dynamical processes*. DOI: [10.1103/PhysRevA.82.042314](https://doi.org/10.1103/PhysRevA.82.042314). URL: <https://arxiv.org/abs/1007.1445>.

*Commentary.*

Section I, p. 2, verbatim: “Throughout, we assume that local ancilla (typically labelled as Hilbert space Ha′ ⊗ Hb′ ), local unitaries and classical communication are freely available as is appropriate in many communication and distributed computation scenarios.” The finite Kraus action is D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus applied to the two displayed families and rho. It uses identity Kraus factors on the ancillary pair, with Matrix.reindex ordering the cut as AA' versus BB'.

**Definition 1.2 (Separable-input entangling capacity).**

$$\forall (dA : \mathbb{N}), \forall (dB : \mathbb{N}), \forall (r : \mathbb{N}), \forall (K : \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), (\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), \mathbb{C}\right)), \operatorname{capSep}\left(K\right) = \operatorname{iSup}_{a : \mathbb{N}} (\operatorname{iSup}_{b : \mathbb{N}} (\operatorname{iSup}_{rho : \operatorname{Matrix}\left(((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(a\right)) \times (\operatorname{Fin}\left(dB\right) \times \operatorname{Fin}\left(b\right))), ((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(a\right)) \times (\operatorname{Fin}\left(dB\right) \times \operatorname{Fin}\left(b\right))), \mathbb{C}\right)} (\operatorname{iSup}_{((\operatorname{IsDensity}\left(rho\right)) \land (\operatorname{IsSeparable}\left(rho\right)))} ((\operatorname{logb}\left(2, \operatorname{traceNorm}\left(\operatorname{partialTranspose}\left(\operatorname{extend}\left(K, rho\right)\right)\right)\right) : \mathbb{R}) : EReal))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.capSep` (`✓ std3`).

*Citation.* Earl T. Campbell (2010). *Optimal entangling capacity of dynamical processes*. DOI: [10.1103/PhysRevA.82.042314](https://doi.org/10.1103/PhysRevA.82.042314). URL: <https://arxiv.org/abs/1007.1445>.

*Commentary.*

Section I, Eq. (1), p. 2, verbatim: “The maximum achievable entanglement for a dynamical map, Λ, when the initial state is separable, is given by:” The formula is E(Λ) = sup{E(Λ(σ))|σ ∈ S}. Eqs. (4)–(5) and the logarithmic rescaling use Real.logb 2 of the partial-transpose trace norm. The supremum in EReal includes every finite local ancilla dimension. IsDensity is positive semidefinite with trace one, and IsSeparable is a finite convex mixture of products of such matrices.

**Definition 1.3 (Assisted entangling capacity).**

$$\forall (dA : \mathbb{N}), \forall (dB : \mathbb{N}), \forall (r : \mathbb{N}), \forall (K : \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), (\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), \mathbb{C}\right)), \operatorname{capAssisted}\left(K\right) = \operatorname{iSup}_{a : \mathbb{N}} (\operatorname{iSup}_{b : \mathbb{N}} (\operatorname{iSup}_{rho : \operatorname{Matrix}\left(((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(a\right)) \times (\operatorname{Fin}\left(dB\right) \times \operatorname{Fin}\left(b\right))), ((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(a\right)) \times (\operatorname{Fin}\left(dB\right) \times \operatorname{Fin}\left(b\right))), \mathbb{C}\right)} (\operatorname{iSup}_{(\operatorname{IsDensity}\left(rho\right))} ((\operatorname{logb}\left(2, \operatorname{traceNorm}\left(\operatorname{partialTranspose}\left(\operatorname{extend}\left(K, rho\right)\right)\right)\right) - \operatorname{logb}\left(2, \operatorname{traceNorm}\left(\operatorname{partialTranspose}\left(rho\right)\right)\right) : \mathbb{R}) : EReal))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.capAssisted` (`✓ std3`).

*Citation.* Earl T. Campbell (2010). *Optimal entangling capacity of dynamical processes*. DOI: [10.1103/PhysRevA.82.042314](https://doi.org/10.1103/PhysRevA.82.042314). URL: <https://arxiv.org/abs/1007.1445>.

*Commentary.*

Section I, Eq. (2), p. 2, verbatim: “However, when prior entanglement is available, the maximum increase of entanglement is:” The formula is Eᴰ(Λ) = sup{E(Λ(σ)) − E(σ)|σ ∈ D}. Both logarithms have base two. No restriction to positive partial transpose is imposed on these inputs.

**Definition 1.4 (The all-CPTP resource-independence question).**

$$claim \Leftrightarrow \forall (dA : \mathbb{N}), \forall (dB : \mathbb{N}), \forall (r : \mathbb{N}), \forall (K : \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), (\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), \mathbb{C}\right)), (\sum_{k : \operatorname{Fin}\left(r\right)} (\operatorname{conjTranspose}\left(K\left(k\right)\right) \cdot K\left(k\right)) = (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), (\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), \mathbb{C}\right))) \Rightarrow \operatorname{capAssisted}\left(K\right) = \operatorname{capSep}\left(K\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.claim` (`✓ std3`).

*Citation.* Earl T. Campbell (2010). *Optimal entangling capacity of dynamical processes*. DOI: [10.1103/PhysRevA.82.042314](https://doi.org/10.1103/PhysRevA.82.042314). URL: <https://arxiv.org/abs/1007.1445>.

*Commentary.*

Section VII, p. 7, verbatim: “The most obvious open question is whether log-negativity EC is resource independent for all unitaries, or indeed all CPTP maps, or whether this is a singular feature of 2-qubit gates.” The assertion here is its all-CPTP clause. The dimensions dA and dB and the finite Kraus count r range over natural numbers. Completeness of the Kraus family states trace preservation. The two capacities include every finite local ancillary system.

**Theorem 1.5 (Separable states have positive partial transpose).**

$$\forall (A : Type), \forall (B : Type), \forall (finiteA : \operatorname{Fintype}\left(A\right)), \forall (finiteB : \operatorname{Fintype}\left(B\right)), \forall (eqA : \operatorname{DecidableEq}\left(A\right)), \forall (eqB : \operatorname{DecidableEq}\left(B\right)), \forall (sigma : \operatorname{Matrix}\left((A \times B), (A \times B), \mathbb{C}\right)), (\operatorname{IsSeparable}\left(sigma\right)) \Rightarrow \operatorname{PosSemidef}\left(\lambda (i : (A \times B)) \mapsto \lambda (j : (A \times B)) \mapsto sigma\left((\operatorname{fst}\left(i\right), \operatorname{snd}\left(j\right)), (\operatorname{fst}\left(j\right), \operatorname{snd}\left(i\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.separable_ppt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite types A and B, a finite convex mixture of product density matrices remains positive semidefinite after transposing the B indices. The matrix entry at (a,b),(c,d) is sigma((a,d),(c,b)). Positivity follows by applying partial transpose to each product and adding the nonnegative weighted terms.

**Theorem 1.6 (A CPTP separation).**

$$\neg (\forall (dA : \mathbb{N}), \forall (dB : \mathbb{N}), \forall (r : \mathbb{N}), \forall (K : \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), (\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), \mathbb{C}\right)), (\sum_{k : \operatorname{Fin}\left(r\right)} (\operatorname{conjTranspose}\left(K\left(k\right)\right) \cdot K\left(k\right)) = (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), (\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), \mathbb{C}\right))) \Rightarrow \operatorname{capAssisted}\left(K\right) = \operatorname{capSep}\left(K\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.result` (`✓ std3`). ∎

*Resolves.* `Problems/campbell-2010-log-negativity-resource-independence` (refuted) by `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"campbell-2010-log-negativity-resource-independence","declaration_gid":"D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Earl T. Campbell (2010). *Optimal entangling capacity of dynamical processes*. DOI: [10.1103/PhysRevA.82.042314](https://doi.org/10.1103/PhysRevA.82.042314). URL: <https://arxiv.org/abs/1007.1445>.

*Acknowledgement.* Charles H. Bennett, David P. DiVincenzo, Tal Mor, Peter W. Shor, John A. Smolin, Barbara M. Terhal (1999). *Unextendible Product Bases and Bound Entanglement*. DOI: [10.1103/PhysRevLett.82.5385](https://doi.org/10.1103/PhysRevLett.82.5385). URL: <https://arxiv.org/abs/quant-ph/9808030>.

*Commentary.*

The Tiles complementary projector Q is positive under partial transpose. The input Q/4 therefore has zero log-negativity and gives output partial-transpose trace norm two. For a separable input with arbitrary finite local ancillas, the conditional ancillary matrices are positive under partial transpose; a rational product-overlap estimate bounds the output norm by 2 minus 1/6561. The assisted capacity is at least one, whereas the separable-input capacity is at most log base two of 2 minus 1/6561, strictly less than one. This does not decide the question for unitary channels.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.capAssisted`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.capSep`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.extend`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.separable_ppt`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity](../Entanglement/AbsolutePPT/QuadbitMaximumPurity.md)
- Dependency: [D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound](../Entanglement/GHZMeasureBiseparableBound.md)
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](../Information/SeparableStateLocalUnitaryStabilizerObstruction.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence](IptPptSquaredEquivalence.md)
- Dependency: [D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance](../../QuantumChannels/SchurChannelMixedUnitaryDistance.md)
