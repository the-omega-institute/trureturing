# Steering does not force atemporality

## Abstract

A two-qubit state is spatially steerable and temporally compatible.

**Definition 1.1 (The temporal kernel).**

$$\forall R \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; (\operatorname{temporalKernel}\left(R\right) = \operatorname{kronecker}\left(\operatorname{partialTraceRight}\left(R\right), \frac{1}{2} \cdot 1\right) \cdot \operatorname{swap}\left(2\right) + \operatorname{swap}\left(2\right) \cdot \operatorname{kronecker}\left(\operatorname{partialTraceRight}\left(R\right), \frac{1}{2} \cdot 1\right))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.temporalKernel` (`✓ std3`).

*Citation.* Minjeong Song; Varun Narasimhachar; Bartosz Regula; Thomas J. Elliott; Mile Gu (2024). *Causal Classification of Spatiotemporal Quantum Correlations*. DOI: [10.1103/PhysRevLett.133.110202](https://doi.org/10.1103/PhysRevLett.133.110202). URL: <https://arxiv.org/abs/2306.09336v2>.

*Commentary.*

For a joint two-qubit operator R, the first marginal is partialTraceRight(R). The kernel is the anticommutator of its tensor product with I/2 and the swap S. This is the K operator in Equation (3).

**Definition 1.2 (Forward temporal compatibility).**

$$\forall R \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; ((\operatorname{TemporalForward}\left(R\right)) \Leftrightarrow (\exists E \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right),\; (R = \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{referenceAction}\left(E, \operatorname{CStarMatrix.ofMatrix}\left(\operatorname{temporalKernel}\left(R\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.TemporalForward` (`✓ std3`).

*Citation.* Minjeong Song; Varun Narasimhachar; Bartosz Regula; Thomas J. Elliott; Mile Gu (2024). *Causal Classification of Spatiotemporal Quantum Correlations*. DOI: [10.1103/PhysRevLett.133.110202](https://doi.org/10.1103/PhysRevLett.133.110202). URL: <https://arxiv.org/abs/2306.09336v2>.

*Commentary.*

TemporalForward(R) means that a completely positive trace-preserving quantum channel from the first qubit to the second sends the temporal kernel of R to R. The definition is the channel form of Equation (3).

**Definition 1.3 (Reverse temporal compatibility).**

$$\forall R \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; ((\operatorname{TemporalReverse}\left(R\right)) \Leftrightarrow (\operatorname{TemporalForward}\left(\operatorname{submatrix}\left(R, \operatorname{Prod.swap}, \operatorname{Prod.swap}\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.TemporalReverse` (`✓ std3`).

*Citation.* Minjeong Song; Varun Narasimhachar; Bartosz Regula; Thomas J. Elliott; Mile Gu (2024). *Causal Classification of Spatiotemporal Quantum Correlations*. DOI: [10.1103/PhysRevLett.133.110202](https://doi.org/10.1103/PhysRevLett.133.110202). URL: <https://arxiv.org/abs/2306.09336v2>.

*Commentary.*

TemporalReverse(R) applies the forward definition after swapping the two tensor factors. It is the reverse temporal direction described in the source.

**Definition 1.4 (Atemporality).**

$$\forall R \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; ((\operatorname{Atemporal}\left(R\right)) \Leftrightarrow ((\neg \operatorname{TemporalForward}\left(R\right)) \land (\neg \operatorname{TemporalReverse}\left(R\right))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.Atemporal` (`✓ std3`).

*Citation.* Minjeong Song; Varun Narasimhachar; Bartosz Regula; Thomas J. Elliott; Mile Gu (2024). *Causal Classification of Spatiotemporal Quantum Correlations*. DOI: [10.1103/PhysRevLett.133.110202](https://doi.org/10.1103/PhysRevLett.133.110202). URL: <https://arxiv.org/abs/2306.09336v2>.

*Commentary.*

Atemporal(R) holds exactly when neither temporal direction admits a quantum channel. Thus both forward and reverse temporal compatibility fail.

**Definition 1.5 (Binary projective measurement families).**

$$\forall n \in \mathbb{N},\; (\forall P \in (\operatorname{Fin}\left(n\right) \to (Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))),\; ((\operatorname{BinaryProjective}\left(P\right)) \Leftrightarrow ((\forall x \in \operatorname{Fin}\left(n\right),\; (\forall b \in Bool,\; (\operatorname{IsStarProjection}\left(P\left(x\right)\left(b\right)\right)))) \land (\forall x \in \operatorname{Fin}\left(n\right),\; (P\left(x\right)\left(false\right) + P\left(x\right)\left(true\right) = 1)))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.BinaryProjective` (`✓ std3`).

*Citation.* Minjeong Song; Varun Narasimhachar; Bartosz Regula; Thomas J. Elliott; Mile Gu (2024). *Causal Classification of Spatiotemporal Quantum Correlations*. DOI: [10.1103/PhysRevLett.133.110202](https://doi.org/10.1103/PhysRevLett.133.110202). URL: <https://arxiv.org/abs/2306.09336v2>.

*Commentary.*

BinaryProjective(P) requires every outcome operator to be a star projection and requires the two outcomes at each setting to sum to the identity.

**Definition 1.6 (The conditional-state assemblage).**

$$\forall n \in \mathbb{N},\; (\forall R \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; (\forall P \in (\operatorname{Fin}\left(n\right) \to (Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))),\; (\operatorname{assemblage}\left(R, P\right) = \lambda (x: \operatorname{Fin}\left(n\right)) \mapsto (\lambda (b: Bool) \mapsto (\operatorname{partialTraceRight}\left(\operatorname{kronecker}\left(1, P\left(x\right)\left(b\right)\right) \cdot R\right))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.assemblage` (`✓ std3`).

*Citation.* Minjeong Song; Varun Narasimhachar; Bartosz Regula; Thomas J. Elliott; Mile Gu (2024). *Causal Classification of Spatiotemporal Quantum Correlations*. DOI: [10.1103/PhysRevLett.133.110202](https://doi.org/10.1103/PhysRevLett.133.110202). URL: <https://arxiv.org/abs/2306.09336v2>.

*Commentary.*

The assemblage of R for a measurement family P is the unnormalized state on the first qubit obtained by multiplying R by the second-qubit outcome operator and tracing out the second factor.

**Definition 1.7 (Local-hidden-state models).**

$$\forall n \in \mathbb{N},\; (\forall sigma \in (\operatorname{Fin}\left(n\right) \to (Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))),\; ((\operatorname{HasLHS}\left(sigma\right)) \Leftrightarrow (\exists H \in ((\operatorname{Fin}\left(n\right) \to Bool) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)),\; ((\forall lam \in (\operatorname{Fin}\left(n\right) \to Bool),\; (\operatorname{PosSemidef}\left(H\left(lam\right)\right))) \land (\forall x \in \operatorname{Fin}\left(n\right),\; (\forall b \in Bool,\; (\sum_{(lam: (\operatorname{Fin}\left(n\right) \to Bool))} (\operatorname{ite}\left(lam\left(x\right) = b, H\left(lam\right), 0\right)) = sigma\left(x\right)\left(b\right))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.HasLHS` (`✓ std3`).

*Citation.* Minjeong Song; Varun Narasimhachar; Bartosz Regula; Thomas J. Elliott; Mile Gu (2024). *Causal Classification of Spatiotemporal Quantum Correlations*. DOI: [10.1103/PhysRevLett.133.110202](https://doi.org/10.1103/PhysRevLett.133.110202). URL: <https://arxiv.org/abs/2306.09336v2>.

*Commentary.*

HasLHS(σ) means that σ is generated by positive hidden states indexed by all deterministic Boolean response functions. Summing the hidden state for responses selecting an outcome recovers σ at every setting and outcome.

**Definition 1.8 (Steering from the second qubit).**

$$\forall R \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; ((\operatorname{SteerableBA}\left(R\right)) \Leftrightarrow (\exists n \in \mathbb{N},\; (\exists P \in (\operatorname{Fin}\left(n\right) \to (Bool \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right))),\; ((\operatorname{BinaryProjective}\left(P\right)) \land (\neg \operatorname{HasLHS}\left(\operatorname{assemblage}\left(R, P\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.SteerableBA` (`✓ std3`).

*Citation.* Minjeong Song; Varun Narasimhachar; Bartosz Regula; Thomas J. Elliott; Mile Gu (2024). *Causal Classification of Spatiotemporal Quantum Correlations*. DOI: [10.1103/PhysRevLett.133.110202](https://doi.org/10.1103/PhysRevLett.133.110202). URL: <https://arxiv.org/abs/2306.09336v2>.

*Commentary.*

SteerableBA(R) means that some finite binary projective measurement family on the second qubit produces an assemblage with no local-hidden-state model.

**Definition 1.9 (Steering from the first qubit).**

$$\forall R \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; ((\operatorname{SteerableAB}\left(R\right)) \Leftrightarrow (\operatorname{SteerableBA}\left(\operatorname{submatrix}\left(R, \operatorname{Prod.swap}, \operatorname{Prod.swap}\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.SteerableAB` (`✓ std3`).

*Citation.* Minjeong Song; Varun Narasimhachar; Bartosz Regula; Thomas J. Elliott; Mile Gu (2024). *Causal Classification of Spatiotemporal Quantum Correlations*. DOI: [10.1103/PhysRevLett.133.110202](https://doi.org/10.1103/PhysRevLett.133.110202). URL: <https://arxiv.org/abs/2306.09336v2>.

*Commentary.*

SteerableAB(R) is the corresponding steering condition after interchanging the two qubits.

**Definition 1.10 (The steering implication).**

$$(claim) \Leftrightarrow (\forall R \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; ((\operatorname{IsDensity}\left(R\right)) \Rightarrow (((\operatorname{SteerableBA}\left(R\right)) \lor (\operatorname{SteerableAB}\left(R\right))) \Rightarrow (\operatorname{Atemporal}\left(R\right)))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.claim` (`✓ std3`).

*Citation.* Minjeong Song; Varun Narasimhachar; Bartosz Regula; Thomas J. Elliott; Mile Gu (2024). *Causal Classification of Spatiotemporal Quantum Correlations*. DOI: [10.1103/PhysRevLett.133.110202](https://doi.org/10.1103/PhysRevLett.133.110202). URL: <https://arxiv.org/abs/2306.09336v2>.

*Commentary.*

The claim says that every density operator which is steerable in either direction is atemporal. This is the implication posed in the discussion of Song et al. Here IsDensity is the two-qubit density predicate: positive semidefiniteness and trace one. Steering is tested by finite binary projective measurement families.

$$
\forall R \in \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{C}\right),\; ((\operatorname{IsDensity}\left(R\right)) \Leftrightarrow ((\operatorname{PosSemidef}\left(R\right)) \land (\operatorname{trace}\left(R\right) = 1)))
$$

**Theorem 1.11 (A steerable state with a temporal channel).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/song-et-al-2024-steering-temporal-compatibility-refutation` (refuted) by `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"song-et-al-2024-steering-temporal-compatibility-refutation","declaration_gid":"D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Minjeong Song; Varun Narasimhachar; Bartosz Regula; Thomas J. Elliott; Mile Gu (2024). *Causal Classification of Spatiotemporal Quantum Correlations*. DOI: [10.1103/PhysRevLett.133.110202](https://doi.org/10.1103/PhysRevLett.133.110202). URL: <https://arxiv.org/abs/2306.09336v2>.

*Commentary.*

Take R to be the two-qubit matrix with diagonal blocks [[5391,0],[0,3609]], [[401,0],[0,599]] and off-diagonal blocks [[0,1782],[1188,0]], [[0,1188],[1782,0]], all divided by 10000. Its first marginal is diag(9/10,1/10). A positive decomposition is R = (99/100)((3/50) vv* + (1/25) ww*) + (1/100)(diag(9/10,1/10) tensor I/2), where v = (3,0,0,1) and w = (0,3,1,0) in the ordered basis 00,01,10,11. Every summand is positive semidefinite, and the first marginal has trace one, so R is a density matrix.

Let E be the Pauli channel with weights (4183,3787,223,1807)/10000 on I,X,Y,Z: E(M) = (4183 M + 3787 XMX + 223 YMY + 1807 ZMZ)/10000. The weights are positive and sum to one. Its Kraus operators are the corresponding Pauli matrices multiplied by the square roots of these weights, and R = (id tensor E)K for the temporal kernel K of R.

Bob measures X and Z, with projectors (I + X)/2, (I - X)/2 and (I + Z)/2, (I - Z)/2; false labels the plus outcome. For the X setting, Alice's unnormalized conditional states are [[9/20,297/2000],[297/2000,1/20]] and [[9/20,-297/2000],[-297/2000,1/20]]. For the Z setting they are diag(5391/10000,401/10000) and diag(3609/10000,599/10000).

Use C = diag(1/9,1), U = [[20/909,33/101],[33/101,-20/101]], and V = [[-20/909,33/101],[33/101,20/101]]. Write D_X and D_Z for the false-outcome conditional state minus the true-outcome conditional state at each setting, and set Q = Re tr(U(D_X + D_Z) + V(D_X - D_Z)). The four matrices C + U, C - U, C + V and C - V are rank-one positive semidefinite matrices. For every local-hidden-state model with sigma(X,false) + sigma(X,true) = rho_A = diag(9/10,1/10), each deterministic response contributes either twice U, minus twice U, twice V or minus twice V. Positivity therefore bounds its score by twice its C-weighted hidden-state trace. Summing gives Q <= 2 Re tr(C rho_A) = 2/5.

For the displayed assemblage the quantum score is Q = 10197/25250, which is strictly larger than 2/5. Hence R is steerable in the second-to-first direction. The Pauli channel supplies forward temporal compatibility, so R is not atemporal. This answers the steering clause of the source's question; the Bell-nonlocality clause is not addressed.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.Atemporal`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.BinaryProjective`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.HasLHS`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.SteerableAB`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.SteerableBA`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.TemporalForward`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.TemporalReverse`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.assemblage`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.temporalKernel`
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation](../Entanglement/StructuredNegativityCoincidenceRefutation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
